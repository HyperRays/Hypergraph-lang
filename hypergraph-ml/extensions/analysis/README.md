# Optional graph analysis

This directory is an optional, one-way extension of the core `Hypergraph`
library. It provides incidence matrices and Soufflé query-data export. Core
modules and the normal document runner never depend on it.

Run an incidence view from the project directory:

```sh
./tools/analyze.sh --incidence extensions/analysis/example.hg
./tools/analyze.sh --incidence-json extensions/analysis/example.hg
```

Use `-` instead of a filename to read the document from standard input.

## Query data

The extension exports a Soufflé schema and ground facts; it does not execute
queries itself. Either output can be requested separately, or both can be
combined into a complete input document:

```sh
./tools/analyze.sh --facts-schema extensions/analysis/example.hg
./tools/analyze.sh --facts extensions/analysis/example.hg
./tools/analyze.sh --facts-schema --facts extensions/analysis/example.hg
./tools/analyze.sh --facts --tag first extensions/analysis/example.hg
```

Struct declarations become relations named after the struct. Enum variants
become `Enum__Variant` relations. Integers are emitted as exact decimal
symbols and decimals as exact numerator/denominator symbols, so exporting
facts cannot narrow the language's arbitrary-precision values.

For example, append this query to the combined schema and facts for
`example.hg`:

```prolog
.decl known(name: symbol)
known(Name) :- Person(X, Name).
.output known
```

Running that document with Soufflé returns `Alice` and `Bob`. Soufflé is only
needed to run queries; it is not a build or runtime dependency of the
extension.

## OCaml API

The wrapped library exposes `Hypergraph_analysis.Incidence` for structured,
text, and JSON matrices, and `Hypergraph_analysis.Facts` for schema and fact
generation. Both consume the checked/evaluated result returned by
`Hypergraph.Program.run`.

The extension can be removed without changing the parser, type checker,
evaluator, solver, or core runner: delete this directory, `tools/analyze.sh`,
and the optional-analysis link in the main README.
