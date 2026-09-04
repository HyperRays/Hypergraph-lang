#!/bin/sh
set -eu

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
lean_prefix=$(lean --print-prefix)

cd "$project_dir/../ACUIHE/lean"
lake build ACUIHE:shared

cd "$project_dir/lean"
lake build HypergraphML:shared

cd "$project_dir"
LEAN_PREFIX="$lean_prefix" \
HYPERGRAPHML_LEAN_LIB="$project_dir/lean/.lake/build/lib" \
ACUIHE_LEAN_LIB="$project_dir/../ACUIHE/lean/.lake/build/lib" \
LEAN_PACKAGES_LIB="$project_dir/../ACUIHE/lean/.lake/packages" \
dune build "$@"
