#!/bin/sh
# The single-statement entry point, which the Rust side exposes as parse_line
# and the pest grammar as 'line = SOI ~ expr ~ EOI'.
#
#   sh hypergraph-ml/test/line.sh
#
# What separates it from parsing a file is that a SECOND statement is refused.
# A statement may still span lines wherever the grammar allows a newline, so a
# struct body and a multi-line set both go through.

set -eu
cd "$(dirname "$0")/../.."
ML=hypergraph-ml/_build/default/bin/main.exe
[ -x "$ML" ] || { echo "build first: (cd hypergraph-ml && dune build)" >&2; exit 2; }

fail=0
ok()  { if $ML --line "$1" >/dev/null 2>&1; then :; else echo "FAIL accepted?  $1" >&2; fail=1; fi; }
no()  { if $ML --line "$1" >/dev/null 2>&1; then echo "FAIL refused?   $1" >&2; fail=1; fi; }

# One statement of each kind.
ok 'let x = 5'
ok 'let x: mut Set<Int> = {}'
ok 'g &= {1} -> {2}'
ok 'struct P { a: Int }'
ok 'type M = Decimal'

# Newlines are fine where the grammar puts them, even here.
ok 'struct P {
  a: Int
  , b: String
}'
ok 'let g = {1,
  2}'

# A second statement is the thing this entry point exists to refuse.
no 'let x = 5
let y = 6'
no 'let x = 5 let y = 6'

# And it still applies every other rule.
no ''
no 'let x ='
no 'let m = a & b ^ c'
no 'let bad = (3) / x'
no 'let g = {1
  & 2}'

# The REPL continues a statement while a bracket is open, and answers in order.
out=$(printf 'let x = 5\nstruct P {\n  a: Int\n}\nlet m = a & b ^ c\n' | $ML --repl)
echo "$out" | grep -q '^> ok$'          || { echo "FAIL repl: no ok" >&2; fail=1; }
echo "$out" | grep -q '| | ok'          || { echo "FAIL repl: no continuation" >&2; fail=1; }
echo "$out" | grep -q 'error 1:15'      || { echo "FAIL repl: no error" >&2; fail=1; }

[ "$fail" -eq 0 ] && echo "line: OK"
exit "$fail"
