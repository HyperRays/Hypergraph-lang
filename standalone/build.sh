#!/bin/sh
set -eu

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
workspace_dir=$(CDPATH= cd -- "$project_dir/.." && pwd)
source_dir="$workspace_dir/hypergraph-ml"
probe_dir="$project_dir/lean"
stage_dir="$project_dir/_stage"
dist_dir="$project_dir/dist"

case "$stage_dir" in
  "$project_dir"/_stage) ;;
  *) echo "refusing to clean unexpected stage path: $stage_dir" >&2; exit 1 ;;
esac

case "$(uname -s)" in
  Darwin) ;;
  *) echo "the initial standalone prototype currently supports macOS only" >&2; exit 1 ;;
esac

command -v lean >/dev/null
command -v lake >/dev/null
command -v dune >/dev/null
command -v brew >/dev/null

lean_prefix=$(lean --print-prefix)
lean_ar="$lean_prefix/bin/llvm-ar"
if [ ! -x "$lean_ar" ]; then
  lean_ar=$(command -v llvm-ar)
fi

gmp_prefix=$(brew --prefix gmp)
libuv_prefix=$(brew --prefix libuv)
openssl_prefix=$(brew --prefix openssl@3)
gmp_archive="$gmp_prefix/lib/libgmp.a"
libuv_archive="$libuv_prefix/lib/libuv.a"
ssl_archive="$openssl_prefix/lib/libssl.a"
crypto_archive="$openssl_prefix/lib/libcrypto.a"

for archive in "$gmp_archive" "$libuv_archive" "$ssl_archive" "$crypto_archive"; do
  if [ ! -f "$archive" ]; then
    echo "missing static dependency: $archive" >&2
    exit 1
  fi
done

echo "[1/5] Building the exact Lean import closure"
(cd "$probe_dir" && lake build runtime-link-probe)

probe_rsp="$probe_dir/.lake/build/bin/runtime-link-probe.rsp"
if [ ! -f "$probe_rsp" ]; then
  echo "Lake did not produce the expected response file: $probe_rsp" >&2
  exit 1
fi

rm -rf "$stage_dir"
mkdir -p "$stage_dir/runtime" "$stage_dir/lib" "$stage_dir/bin"

objects_rsp="$stage_dir/runtime/objects.rsp"
awk '
  /\.c\.o(\.export)?"$/ && $0 !~ /RuntimeLinkProbe\.c\.o/ { print }
' "$probe_rsp" > "$objects_rsp"

object_count=$(wc -l < "$objects_rsp" | tr -d ' ')
if [ "$object_count" -eq 0 ]; then
  echo "no Lean native objects were discovered in $probe_rsp" >&2
  exit 1
fi

runtime_archive="$stage_dir/runtime/libhypergraph_lean_runtime.a"
echo "[2/5] Archiving $object_count Lean runtime objects"
"$lean_ar" rcs "$runtime_archive" @"$objects_rsp"

echo "[3/5] Staging the OCaml frontend"
cp "$source_dir"/lib/*.ml "$stage_dir/lib/"
cp "$source_dir"/lib/*.mli "$stage_dir/lib/"
cp "$source_dir"/lib/*.mll "$stage_dir/lib/"
cp "$source_dir"/lib/*.mly "$stage_dir/lib/"
cp "$source_dir/lib/lean_stubs.c" "$stage_dir/lib/"
cp "$source_dir/bin/hypergraph_cli.ml" "$stage_dir/bin/"
cp "$project_dir/templates/dune-project" "$stage_dir/dune-project"
cp "$project_dir/templates/lib.dune" "$stage_dir/lib/dune"
cp "$project_dir/templates/bin.dune" "$stage_dir/bin/dune"

echo "[4/5] Linking one native OCaml/Lean executable"
LEAN_PREFIX="$lean_prefix" \
LEAN_RUNTIME_ARCHIVE="$runtime_archive" \
GMP_STATIC_ARCHIVE="$gmp_archive" \
LIBUV_STATIC_ARCHIVE="$libuv_archive" \
SSL_STATIC_ARCHIVE="$ssl_archive" \
CRYPTO_STATIC_ARCHIVE="$crypto_archive" \
  dune build --root "$stage_dir" --profile release bin/hypergraph_cli.exe

mkdir -p "$dist_dir"
if [ -f "$dist_dir/hypergraph" ]; then
  chmod u+w "$dist_dir/hypergraph"
fi
cp "$stage_dir/_build/default/bin/hypergraph_cli.exe" \
  "$dist_dir/hypergraph"
chmod 755 "$dist_dir/hypergraph"

echo "[5/5] Verifying the packaged executable"
"$dist_dir/hypergraph" "$source_dir/examples/basic.hg" >/dev/null

non_system_dependencies=$(otool -L "$dist_dir/hypergraph" | awk '
  NR > 1 && $1 !~ /^\/usr\/lib\// && $1 !~ /^\/System\/Library\// {
    print $1
  }
')
if [ -n "$non_system_dependencies" ]; then
  echo "standalone verification found non-system dynamic dependencies:" >&2
  echo "$non_system_dependencies" >&2
  exit 1
fi

manifest="$dist_dir/build-manifest.txt"
{
  echo "artifact=hypergraph"
  echo "bytes=$(stat -f %z "$dist_dir/hypergraph")"
  echo "sha256=$(shasum -a 256 "$dist_dir/hypergraph" | awk '{print $1}')"
  echo "lean_objects=$object_count"
  echo "lean=$(lean --version | head -n 1)"
  echo "ocaml=$(ocamlopt -version)"
  echo "dune=$(dune --version)"
  echo "dynamic_dependencies:"
  otool -L "$dist_dir/hypergraph" | tail -n +2
} > "$manifest"

echo
ls -lh "$dist_dir/hypergraph"
echo "Lean objects linked: $object_count"
echo "Output: $dist_dir/hypergraph"
echo "Manifest: $manifest"
