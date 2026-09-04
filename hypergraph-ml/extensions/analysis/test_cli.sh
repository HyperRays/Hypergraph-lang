#!/bin/sh
set -eu

cli=$1
example=$2

json=$($cli --incidence-json "$example")
case $json in
  '[{"graph":"network"'*'"entries":[[0,-1],[1,1]]}'*']') ;;
  *)
    echo "incidence JSON output was not the expected sparse matrix" >&2
    exit 1
    ;;
esac

stdin_text=$(printf '%s\n' 'let edge = {1} -> {2}' 'let graph = {edge}' | $cli --incidence -)
case $stdin_text in
  'graph graph: 2 vertices x 1 columns'*'  1'*'-1'*'  2'*'+1'*) ;;
  *)
    echo "incidence stdin output was not the expected text matrix" >&2
    exit 1
    ;;
esac

if $cli --incidence --incidence-json "$example" >/dev/null 2>&1; then
  echo "conflicting incidence modes were accepted" >&2
  exit 1
fi

if printf '%s\n' 'let bad = missing' | $cli --incidence - >/dev/null 2>&1; then
  echo "invalid input returned success" >&2
  exit 1
fi
