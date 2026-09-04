# Optional graph analysis

This directory is an optional, one-way extension of the core `Hypergraph`
library. It provides incidence matrices and, in the next layer, query-data
export. Core modules and the normal document runner never depend on it.

Run an incidence view from the project directory:

```sh
./tools/analyze.sh --incidence extensions/analysis/example.hg
./tools/analyze.sh --incidence-json extensions/analysis/example.hg
```

Use `-` instead of a filename to read the document from standard input.

The extension can be removed without changing the parser, type checker,
evaluator, solver, or core runner: delete this directory, `tools/analyze.sh`,
and the optional-analysis link in the main README.
