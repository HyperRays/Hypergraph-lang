# Hypergraph language front end and native solver

An OCaml lexer and Menhir parser for
[Hypergraph-lang.md](Hypergraph-lang.md). Parsing produces an AST with source
locations. It does not infer types, choose conversions, or evaluate expressions.

[Hypergraph.Solver](ffi/acuihe.mli) exposes the sibling **ACUIhE Lean solver**
through an in-process C FFI. It supports algebraic equality, inclusion,
unifiability, and ground substitutions. Parsed programs are not yet connected
to these solver APIs.
See [the native API guide](ffi/README.md) for usage and ownership details.

## Build and run

Requires OCaml 4.13 or newer, Dune 3.0 or newer, Menhir, Python 3, a C toolchain,
and Lean/Lake **4.33.1** through elan. Keep the `ACUIhE` checkout beside this
directory, with its dependencies available. Both Lean projects pin the same
toolchain. The generated parser uses Menhir's default code backend and does not
require `menhirLib` at runtime.

```sh
opam install dune menhir
dune build
dune runtest
dune exec bin/hypergraph_cli.exe -- examples/basic.hg
dune exec bin/hypergraph_cli.exe -- --ast examples/basic.hg
echo 'let e = {1} -["payload"]-> {2.0}' | dune exec bin/hypergraph_cli.exe -- --ast -
```

`dune build` invokes Lake to build the native solver and generates compiler and
linker flags from the pinned Lean installation. Native executables link the
solver archive and dynamically link Lean's runtime libraries. Keep that Lean
installation available when running them. No solver subprocess or text
serialization is used at runtime.

With no filename, the CLI reads stdin. `--ast` prints an AST S-expression dump.
Without `--ast`, the CLI reports the number of parsed statements. Exit codes are
0 for success, 1 for lexical or syntax errors, and 2 for command-line or I/O
errors.

```text
<stdin>:1:9-10: syntax error: unexpected ']'
```

## Implementation

| File | Role |
| --- | --- |
| [lib/lexer.mll](lib/lexer.mll) | ocamllex tokens, comments, string escapes, lexical errors |
| [lib/parser.mly](lib/parser.mly) | Menhir grammar and AST construction |
| [lib/ast.ml](lib/ast.ml) | Types, expressions, declarations, and updates |
| [lib/location.ml](lib/location.ml) | Source spans and located values |
| [lib/parse.mli](lib/parse.mli) | Parsing API with structured diagnostics |
| [lean/HypergraphFFI.lean](lean/HypergraphFFI.lean) | Versioned exports specializing the verified Lean solver |
| [ffi/acuihe.mli](ffi/acuihe.mli) | OCaml native solver API, re-exported as `Hypergraph.Solver` |
| [ffi/acuihe_stubs.c](ffi/acuihe_stubs.c) | Runtime initialization, ownership, and structural data transfer |
| [lib/pp.ml](lib/pp.ml) | AST inspection printer |
| [bin/hypergraph_cli.ml](bin/hypergraph_cli.ml) | File/stdin CLI |
| [test/test_parser.ml](test/test_parser.ml) | AST, failure, location, and specification tests |

The grammar is built with `--strict --explain`: grammar conflicts fail the
build. See the [Menhir manual](https://gallium.inria.fr/~fpottier/menhir/manual.html)
for the generator's flags and APIs.

Use the library from another Dune stanza with `(libraries hypergraph)`:

```ocaml
match Hypergraph.Parse.string ~filename:"example.hg" "let s = {1, 2}" with
| Ok program -> Format.printf "%a@." Hypergraph.Pp.program program
| Error diagnostic ->
    Format.eprintf "%a@." Hypergraph.Diagnostic.pp diagnostic
```

`Parse.file` closes its input even on failure; I/O errors raise `Sys_error`.
`Parse.channel` leaves the caller's channel open. `Parse.program`,
`Parse.expression`, and `Parse.type_expression` accept a `Lexing.lexbuf` and
consume the entire input. Locations have one-based lines and byte columns,
zero-based byte offsets, and an exclusive end position.

## Supported syntax and initial choices

The parser covers structs, enums, aliases, generic and sum types, inferred and
annotated `let` bindings, `: mut` annotations, constructors, qualified enum
variants, sets, lists, all six edge forms, and `|`, `&`, `-`, `|=`, `&=`, `-=`.

The specification leaves some lexical and grammatical details open. This
implementation makes the following choices, without changing the specification:

- Identifiers follow `[A-Za-z_][A-Za-z0-9_]*`. Only `struct`, `enum`, `alias`,
  `let`, and `mut` are reserved. Built-in types remain ordinary type names.
- Newlines are whitespace. Statements can optionally end with one semicolon.
  Comma-separated items can have one trailing comma. Generic parameter and
  argument lists must be nonempty; other lists and declaration bodies may be
  empty. Enum variants may have zero or more positional payload arguments.
- `//` line comments and nested `/* ... */` block comments are supported.
  LF, CRLF, and CR line endings are recognized.
- Integers are digit sequences, and decimals have digits on both sides of a
  decimal point. Both may have a leading minus. Their exact spelling is stored
  as a string; no machine integer/float conversion or normalization takes place.
  Exponents, numeric separators, and leading plus signs are not supported.
- Double-quoted strings accept literal UTF-8 bytes and the escapes `\"`, `\\`,
  `\/`, `\n`, `\r`, `\t`, `\b`, and `\f`. Raw control characters, raw newlines,
  and other escapes (including `\u`) are rejected.
- `&` binds more tightly than `|` and `-`. `|` and `-` have equal precedence.
  These operations associate to the left. Edge arrows bind least tightly and
  cannot be chained without parentheses. Thus `a | b -> c - d` means
  `(a | b) -> (c - d)`. Parentheses also group type sums.
- `->`, `<-`, `<->`, `-[`, and `<-[` are indivisible tokens. Whitespace may
  surround them and appear inside payload brackets, but not inside the tokens.
  Closing `]` is a separate token, so `a -[ [1, 2] ] -> b` works. `a - [1]`
  parses as difference with a list operand; `a -[1]` starts an incomplete edge.

```hg
let forward = a -> b
let backward = b <- a
let undirected = a <-> b
let forward_payload = a -["p"]-> b
let backward_payload = b <-["p"]- a
let undirected_payload = a <-["p"]-> b
```

An `Edge` AST node preserves written `left` and `right` endpoints and its
`Forward`, `Backward`, or `Undirected` direction. The AST's optional payload
records whether a payload was written.

`!` is represented as the type name `Bottom`. Bare `Some(value)` and `None`
parse as an ordinary constructor and name, respectively. The parser does not
resolve their Option meaning or expand `Graph` and user aliases.

`dune runtest` parses every `hg` code block directly from the specification,
including examples marked semantically rejected, and checks AST structure,
precedence, diagnostics, channel refills, and CLI behavior. Mathematical
`typesystem` blocks are not source-language input.

The same command runs the native FFI suite in native and bytecode modes,
including returned substitutions, graph layers, GC compaction, and system
threads. On OCaml 5 it also tests sharing handles between domains.
