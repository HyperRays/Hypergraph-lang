# Native Lean solver API

The OCaml library `acuihe` calls the compiled ACUIhE solver through C functions.
The `hypergraph` library re-exports the API as `Hypergraph.Solver`. Calls pass
native objects, integers, and arrays directly within the process.

```ocaml
open Hypergraph.Solver

let int_type = Term.constant 0
let unknown = Term.variable 0

let inferred =
  match solve [| Term.free unknown, Term.free int_type |] with
  | None -> failwith "inconsistent type constraints"
  | Some substitution -> Solution.get substitution 0

let () =
  assert (Graph.equal inferred (Graph.normalize int_type))
```

Use `(libraries hypergraph)` in a consuming Dune stanza, or `(libraries acuihe)`
and `open Acuihe` when the parser is unnecessary. The complete signatures are
in [acuihe.mli](acuihe.mli).

## Operations and data

- `Term.zero`, `constant`, `variable`, `add`, `hom`, and `free` construct terms.
  `free` is the algebra's `E` operator. Integer IDs identify symbols, not numeric
  values: constant 0 is distinct from `Term.zero` and from variable 0.
  Callers intern their names into separate constant, variable, and homomorphism
  namespaces. The full nonnegative OCaml `int` range is supported.
- `Term.equal` and `Term.below` decide algebraic equality and additive inclusion.
  These preserve ACUI, named homomorphism distribution, `E(0) = 0`, and E
  injectivity; E is not made distributive.
- `solve` consumes an OCaml array of equation pairs and returns `None` or an
  opaque substitution. `is_unifiable` skips witness reconstruction. Mixed
  equations and inequalities use `solve_constraints` or
  `constraints_satisfiable`; `Below(a,b)` becomes `a + b = b`.
- `Solution.get` queries a variable as a ground canonical graph. Variables not
  present in the input map to zero. The solver supplies one satisfying ground
  substitution, without a minimality or most-generality guarantee.
- `Graph.normalize`, `equal`, and `below` operate on canonical graphs.
  `Graph.layer` returns an OCaml array of `{ word; atom }` records. Words are
  arrays of homomorphism IDs, outermost first. Atoms are `Constant id`,
  `Variable id`, or `Free child`. Ground solutions have no variable atoms.
  The layer is unordered and duplicate-free; an empty layer denotes zero.
  `Graph.to_term` reconstructs an equivalent raw term through this public view.

## Runtime ownership

Terms, graphs, and substitutions are OCaml custom blocks owning reference-counted
Lean objects. The C layer retains inputs before calling consuming Lean exports
and releases handles through OCaml finalizers. Native holders live on the C heap
so OCaml compaction cannot move them during an unlocked call. The handles root
both arguments and results across exceptions at OCaml runtime-lock transitions.

Lean runtime and module initialization occur once. Foreign threads get Lean
thread-local initialization and teardown. Objects retained by OCaml are marked
for Lean's atomic reference counting, allowing handles to be shared between
OCaml threads and domains. Solver, normalization, comparison, and layer calls
release the OCaml runtime lock. Constructors perform short calls with the lock
held. Finalizers can safely release handles on a different domain.

Use the provided equality functions. Polymorphic comparison and `Marshal` are
not supported for handles. Layer arrays belong to OCaml and may be modified
without changing the Lean graph. Native memory reclamation follows OCaml GC;
large workloads can call `Gc.full_major ()` to promptly collect unused handles.

The bridge does not impose solver fuel limits or provide cancellation of a
running native call. The host can run other OCaml threads while Lean searches.

## Lean API and proof boundary

[HypergraphFFI.lean](../lean/HypergraphFFI.lean) is a small adapter importing the
unchanged sibling solver. Its exports are versioned `acuihe_v1_*` C symbols.
[acuihe_native.h](acuihe_native.h) declares their ABI. Initializing the bridge
checks the exported ABI version before constructing handles.

Terms, graphs, and substitutions remain opaque to C. Equation inputs use Lean
`Array (Term × Term)` objects. The layer export uses the standard erased
`Finset`/`List`, pair, sum, particle, and natural-number representations. The C
adapter copies these into OCaml arrays and variants; it does not inspect a raw
canonical-graph presentation. This structural ABI is tied to the pinned Lean
version and must be checked when upgrading it.

The exported solver wraps `ACUIhE.Solver.solve` directly. The adapter includes
`solve_sound`, `solve_none_iff`, and `isUnifiable_iff` theorems. Its C ownership
and OCaml conversion code are covered by execution tests, outside Lean's proof
boundary.

Reference conventions: [Lean's FFI](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/)
and [OCaml's C interface](https://ocaml.org/manual/5.4/intfc.html).

## Build and verification

Run from the project root:

```sh
dune build
dune runtest
```

The build rule invokes [build_lean.py](../tools/build_lean.py). Lake computes the
API module's transitive native import closure and packages it as a static archive
for native executables and a shared object for OCaml's bytecode loader. The
toolchain's Lean runtime libraries are shared dependencies. Dune receives the
headers and runtime paths from the pinned toolchain, without hardcoded paths to
an individual machine. Lake also checks the sibling project for changed inputs
on each Dune invocation.

The adapter's `lake-manifest.json` pins build dependencies; it is ordinary Lake
metadata. The runtime FFI has no serialization protocol.

The bridge targets POSIX platforms and has been tested here on macOS ARM64 with
OCaml 5.4.1, Lean 4.33.1, and Dune 3.19.1. Native and bytecode tests cover solver
answers, inequalities, maximum symbol IDs, nested graph reconstruction, small
OCaml heaps, repeated GC/compaction, system threads, and OCaml 5 domains.

For a bytecode executable launched directly instead of via `dune exec`, point
`CAML_LD_LIBRARY_PATH` at the built FFI directory:

```sh
CAML_LD_LIBRARY_PATH=_build/default/ffi _build/default/test/test_ffi.bc
```
