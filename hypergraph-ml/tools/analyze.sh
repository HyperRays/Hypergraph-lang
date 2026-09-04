#!/bin/sh
set -eu

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)

"$project_dir/tools/build.sh" extensions/analysis/hypergraph_analysis_cli.exe
exec "$project_dir/_build/default/extensions/analysis/hypergraph_analysis_cli.exe" "$@"
