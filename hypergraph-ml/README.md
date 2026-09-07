# Hypergraph ML

`hypergraph-ml` is the OCaml library implementation of the language specified
in [`Hypergraph-lang.md`](Hypergraph-lang.md).
That document supersedes the former OCaml language and is the source of truth
for syntax and semantics.

The implementation is deliberately staged:

1. `Driver.parse` produces a located `Ast.program` with exact `Z.t` integers
   and `Q.t` decimals.
2. `Check.check` translates source types to the proved ACUIhE representation,
   solves all connected program constraints with shared assignments, and
   records grounded `UndirectedEdge` coercions.
3. `Value.run` evaluates a checked program. Coercing an `UndirectedEdge` is
   irreversible and emits its two directed orientations.
4. `Program.run` is the convenience entry point that performs all three
   stages.

`Solver` is the lower-level typed OCaml API for the verified Lean solver. It
offers ACUIhE terms, equality/subsumption constraints, exact `Sat`/`Unsat`
results, assignment rechecking, raw replacement rules, and
`of_subsumption`. The latter is decoded by Lean using
`BlockReplacement.ofSubsumption` itself.

## Type representation

- Scalars are primitive ACUIhE constants.
- `Set<T>` is `C_Set + S_element(T)`, so it distributes over sums.
- `List<T>` is `C_List + S_list_element(T)`. Lists distribute over sums while
  preserving runtime order and duplicate values.
- Every struct and enum is `E(C_Name + Σ S_member(member_type))`.
- `Option<T>`, `Edge<T,H,P>`, and `UndirectedEdge<T,H,P>` are predeclared named
  declarations. Edge sides are `Set<T>`/`Set<H>` and payload is `Option<P>`.
- `Graph<T,H,P>` is the transparent alias
  `Set<Edge<T,H,P> + UndirectedEdge<T,H,P>>`.
- Set union is the type join, intersection is the narrow meet, and difference
  retains the left type.
- Nested graph equality uses `Opaque<Hide,Marker>`; copying preserves the
  marker while a new graph value receives a new marker.

## Build and test

The build supports macOS and Linux. It needs OCaml/Dune with `menhir`,
`yojson`, `zarith`, `ppx_deriving`, and a working `elan`/`lake` installation.
The Lean toolchain is pinned by `lean/lean-toolchain`.

```sh
cd hypergraph-ml
./tools/build.sh @all
./tools/build.sh @runtest
```

The helper builds the ACUIhE and HypergraphML Lean shared libraries first,
then supplies their native include/library paths to Dune. The FFI bridge is
serialized for thread safety. Solver calls are synchronous, exact, unbounded,
and never return an `Unknown` result.

## Run a document

The runner builds any missing Lean and OCaml artifacts, checks the complete
document, evaluates it, and prints the final value of each binding in source
order:

```sh
cd hypergraph-ml
./tools/run.sh examples/basic.hg
```

Expected output:

```text
alice = Person("Alice")
bob = Person("Bob")
knows = {Person("Alice")} -> {Person("Bob")}
```

Use `-` to read a document from standard input:

```sh
./tools/run.sh - < examples/basic.hg
```

Parse, type, and evaluation errors are printed with the file, line, and
column, and return a non-zero exit status.

## Optional graph analysis

Incidence matrices and query-data export live in a removable extension rather
than the core library. See
[`extensions/analysis/README.md`](extensions/analysis/README.md) for its
standalone command and API.
