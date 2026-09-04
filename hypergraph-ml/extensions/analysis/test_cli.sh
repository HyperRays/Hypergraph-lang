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

schema=$($cli --facts-schema "$example")
case $schema in
  *'.decl graph(g: id)'*'.decl Person(x: id, name: symbol)'*) ;;
  *)
    echo "facts schema output is incomplete" >&2
    exit 1
    ;;
esac

facts=$($cli --facts --tag sample "$example")
case $facts in
  *'Person('*'graph("sample:network").'*'tail('*'head('*) ;;
  *)
    echo "tagged facts output is incomplete" >&2
    exit 1
    ;;
esac

if $cli --incidence --facts "$example" >/dev/null 2>&1; then
  echo "incidence and facts modes were accepted together" >&2
  exit 1
fi
