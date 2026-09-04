#!/bin/sh
set -eu

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)

"$project_dir/tools/build.sh" bin/hypergraph_cli.exe
exec "$project_dir/_build/default/bin/hypergraph_cli.exe" "$@"
