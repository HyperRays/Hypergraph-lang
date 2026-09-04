#!/bin/sh
set -eu

cli=$1
example=$2

if ! command -v souffle >/dev/null 2>&1; then
  echo "souffle: skipped (not installed)"
  exit 0
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
mkdir "$work/out"

$cli --facts-schema --facts "$example" > "$work/query.dl"
printf '%s\n' \
  '.decl known(name: symbol)' \
  'known(Name) :- Person(X, Name).' \
  '.output known' >> "$work/query.dl"

souffle -w -D "$work/out" "$work/query.dl" >/dev/null 2>&1
grep -Fx 'Alice' "$work/out/known.csv" >/dev/null
grep -Fx 'Bob' "$work/out/known.csv" >/dev/null
