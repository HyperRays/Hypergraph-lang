#!/bin/sh
# Golden regression: every program under test/golden/ and test/corpus/, put
# through each output the implementation has, compared with what is recorded.
#
#   sh hypergraph-ml/test/golden.sh            check
#   sh hypergraph-ml/test/golden.sh --accept   record the current output
#
# These replace the differential suites. While a Rust and Haskell
# implementation was here, every stage was compared against it directly, which
# is the strongest oracle available for a rewrite and the reason the port can
# be trusted. With that gone the question changes from "does it agree with the
# other one" to "did it change", and a golden answers that.
#
# The corpus itself was drawn from the generators under test/, with programs
# kept only where the two implementations already agreed, so what is recorded
# here was verified rather than merely observed. test/corpus/ additionally
# holds the hand-written cases from porting the parser.
#
# --accept after a deliberate change, and READ THE DIFF: a golden suite is
# only worth as much as the attention paid when it moves.

set -eu
cd "$(dirname "$0")/../.."

ML=hypergraph-ml/_build/default/bin/main.exe
[ -x "$ML" ] || { echo "build first: (cd hypergraph-ml && dune build)" >&2; exit 2; }

accept=no
[ "${1:-}" = "--accept" ] && accept=yes

# Every output the implementation offers, so a change anywhere shows up.
render() {
  f=$1
  echo "== report"
  "$ML" "$f" --plain 2>&1 || true
  echo "== incidence"
  "$ML" "$f" --incidence 2>&1 || true
  echo "== facts"
  "$ML" "$f" --facts-schema --facts 2>&1 || true
}

# The repo's own programs at the top level, whose report is pinned separately
# by corpus_typecheck.expected.txt. That file predates the port and is the one
# expectation here written by neither implementation nor generator.
if [ "$accept" = no ]; then
  got=$(mktemp)
  "$ML" corpus_typecheck.hg --plain > "$got" 2>&1 || true
  if ! diff -q corpus_typecheck.expected.txt "$got" >/dev/null; then
    echo "golden: FAILED — corpus_typecheck.expected.txt" >&2
    diff corpus_typecheck.expected.txt "$got" | head -12 >&2
    rm -f "$got"
    exit 1
  fi
  rm -f "$got"
fi

pass=0; fail=0; wrote=0
for f in hypergraph-ml/test/golden/*.hg hypergraph-ml/test/corpus/*.hg; do
  [ -e "$f" ] || continue
  expected="${f%.hg}.expected"
  actual=$(render "$f" | sed "s|$f|FILE|g")
  if [ "$accept" = yes ]; then
    printf '%s\n' "$actual" > "$expected"
    wrote=$((wrote + 1))
  elif [ ! -f "$expected" ]; then
    echo "golden: FAILED — $expected missing; run with --accept" >&2
    fail=$((fail + 1))
  elif [ "$actual" = "$(cat "$expected")" ]; then
    pass=$((pass + 1))
  else
    echo "golden: FAILED — $f" >&2
    printf '%s\n' "$actual" | diff "$expected" - | head -12 >&2
    fail=$((fail + 1))
  fi
done

if [ "$accept" = yes ]; then
  echo "golden: recorded $wrote"
  exit 0
fi
[ "$fail" -eq 0 ] && echo "golden: OK ($pass programs)"
exit "$fail"
