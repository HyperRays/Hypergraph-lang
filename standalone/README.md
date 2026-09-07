# Standalone HypergraphML binary prototype

This directory is an isolated packaging pipeline. It reads the existing
`ACUIHE/lean` and `hypergraph-ml` projects but does not modify their build
definitions or generated artifacts.

The output is one native executable containing:

- the OCaml parser, lexer, checker, and evaluator;
- the HypergraphML Lean bridge;
- the exact Lean import closure of the optimized batched ACUIhE solver;
- statically linked Lean and Homebrew support archives where available.

Unlike the development build, the executable does not link the aggregate
`libmathlib_Mathlib.dylib`, the ACUIHE dylib, or the HypergraphML dylib.

## Build

The initial prototype targets macOS and expects the same tools as the main
project, plus Homebrew static archives for `gmp`, `libuv`, and `openssl@3`.

```sh
cd standalone
./build.sh
```

The result is written to `dist/hypergraph`. The script runs
`hypergraph-ml/examples/basic.hg` as a smoke test before succeeding. It also
rejects the artifact if it retains a non-system dynamic-library dependency and
writes size, checksum, toolchain, object-count, and dependency information to
`dist/build-manifest.txt`.

## Pipeline

1. `lean/RuntimeLinkProbe.lean` imports the real bridge and is built as a
   temporary Lean executable.
2. Lake's generated response file provides the exact transitive set of native
   module objects for that import closure.
3. Those objects are archived without the probe's generated `main` function.
4. The OCaml sources are copied into the ignored `_stage` directory and built
   with a standalone Dune configuration.
5. Dune force-loads the Lean module archive and statically links the Lean core
   and native support archives into the OCaml executable.

The staging copy is intentional: it keeps this packaging experiment separate
from the existing development Dune and Lake configurations.

## Current baseline

On macOS arm64 with Lean 4.33.1, the initial result is approximately 115 MB and
contains 1,045 Lean module objects. Its only dynamic dependencies are macOS
system libraries (`libc++` and `libSystem`); it does not require an installed
Lean toolchain or any workspace dylibs at runtime.

This is a packaging baseline rather than the final size target. The remaining
weight is the current Lean import closure, particularly mathlib and Lean
compiler support reached through it. The generated `runtime/objects.rsp` in
the ignored staging directory makes that closure explicit for the next round
of module splitting and import reduction.
