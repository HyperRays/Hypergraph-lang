#!/usr/bin/env python3
"""Build the pinned Lean import closure and emit Dune's native link inputs."""

import os
from pathlib import Path
import shutil
import subprocess
import sys


def write_sexp(path, items):
    # Dune quoted strings, not shell arguments. subprocess always receives lists.
    def quote(text):
        return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'

    contents = "(" + " ".join(quote(item) for item in items) + ")\n"
    path.write_text(contents)


def main():
    root = Path(os.environ["DUNE_SOURCEROOT"])
    lean_dir = root / "lean"
    dependency = root.parent / "ACUIhE"
    if not (dependency / "lakefile.toml").is_file():
        raise RuntimeError(f"expected the ACUIhE checkout at {dependency}")
    toolchain = (lean_dir / "lean-toolchain").read_text().strip()
    if (dependency / "lean-toolchain").read_text().strip() != toolchain:
        raise RuntimeError("Lean toolchains differ; align lean/lean-toolchain with ACUIhE first")

    subprocess.run(["lake", "--no-cache", "build", "acuihe_native", "acuihe_shared"],
                   cwd=lean_dir, check=True)
    prefix = Path(subprocess.check_output(
        ["lean", "--print-prefix"], cwd=lean_dir, text=True).strip())
    native = lean_dir / ".lake" / "build" / "lib" / "libacuihe_native.a"
    shutil.copyfile(native, "libacuihe_native.a")
    shutil.copyfile(native.with_name("dllacuihe_native.so"), "dllacuihe_native.so")
    write_sexp(Path("lean_c_flags.sexp"), ["-I" + str(prefix / "include"), "-pthread"])
    runtime = str(prefix / "lib" / "lean")
    write_sexp(Path("lean_link_flags.sexp"), [
        "-L" + runtime, "-lLake_shared", "-lleanshared", "-Wl,-rpath," + runtime, "-lpthread",
    ])


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Lean native build: {error}", file=sys.stderr)
        sys.exit(1)
