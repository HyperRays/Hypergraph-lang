Parse a file:

  $ ../bin/hypergraph_cli.exe ../examples/basic.hg
  Parsed 10 statement(s).

Dump the AST from stdin:

  $ echo 'let x = 1' | ../bin/hypergraph_cli.exe --ast -
  (program (let "x" immutable (none) (int 1)))

Report syntax errors with positions and a nonzero exit code:

  $ echo 'let x = ]' | ../bin/hypergraph_cli.exe
  <stdin>:1:9-10: syntax error: unexpected ']'
  [1]

Report lexical errors:

  $ echo 'let x = @' | ../bin/hypergraph_cli.exe
  <stdin>:1:9-10: lexical error: unexpected character '@'
  [1]

Reject extra filenames:

  $ ../bin/hypergraph_cli.exe first.hg second.hg 2>/dev/null
  [2]

Report I/O errors:

  $ ../bin/hypergraph_cli.exe missing.hg
  I/O error: missing.hg: No such file or directory
  [2]
