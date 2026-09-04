#!/bin/sh
# Both browser builds against the native binary, on the golden corpus.
#
#   sh hypergraph-ml/test/web.sh
#
# A browser build is a different compiler backend over the same source, so it
# can diverge in the places backends differ: integer width, float formatting,
# string handling. Comparing every output on every golden program is what says
# it does not.
#
# Needs node. The wasm build resolves its .wasm beside the loader, so the
# artifacts must stay where dune put them.

set -eu
cd "$(dirname "$0")/../.."

ML=hypergraph-ml/_build/default/bin/main.exe
JS=hypergraph-ml/_build/default/web/main.bc.js
WASM=hypergraph-ml/_build/default/web/main.bc.wasm.js

[ -x "$ML" ] || { echo "build first: (cd hypergraph-ml && dune build)" >&2; exit 2; }
for b in "$JS" "$WASM"; do
  [ -f "$b" ] || {
    echo "build the web targets first:" >&2
    echo "  (cd hypergraph-ml && dune build --profile release web/main.bc.js web/main.bc.wasm.js)" >&2
    exit 2
  }
done
command -v node >/dev/null || { echo "no node on PATH" >&2; exit 2; }

fail=0
for build in "$JS" "$WASM"; do
  name=$(basename "$build")
  same=0
  for f in hypergraph-ml/test/golden/*.hg hypergraph-ml/test/corpus/*.hg; do
    [ -e "$f" ] || continue
    for mode in report incidence facts; do
      case $mode in
        report)    native=$("$ML" "$f" 2>&1 || true) ;;
        incidence) native=$("$ML" "$f" --incidence 2>&1 || true) ;;
        facts)     native=$("$ML" "$f" --facts-schema --facts 2>&1 || true) ;;
      esac
      # The web entry names its input 'input.hg', having no file to name.
      native=$(printf '%s' "$native" | sed "s|$f|input.hg|g")
      web=$(node hypergraph-ml/web/render.mjs "$build" "$f" "$mode" 2>&1 || true)
      if [ "$native" != "$web" ]; then
        echo "web: FAILED — $name $mode $f" >&2
        printf '%s\n' "$web" | diff - /dev/stdin <<EOF | head -8 >&2 || true
$native
EOF
        fail=$((fail + 1))
      fi
    done
    same=$((same + 1))
  done
  echo "  $name: $same programs"
done

[ "$fail" -eq 0 ] && echo "web: OK"
exit "$fail"
