# Verified FILO algorithm for ACUIh unification

The algorithmic pipeline from the [FILO paper](https://arxiv.org/html/2502.14130v1)
is implemented with Lean proofs against the project's existing ACUIh ground
substitution matrices. This is the Lean solver core, not the Java GUI or OWL
file parser. It does not solve the full ACUIhE algebra.

## Public interface

Import `ACUIhE.FILO` (also imported by `ACUIhE`). Labels need only
`DecidableEq`; their types need not be finite.

```lean
FILO.solve (p : FILO.Problem Const Var Hom) :
  Option (ACUIh.Linear.GroundMatrix Const Var Hom)

FILO.solve_sound p : FILO.solve p = some m → p.IsSolution m
FILO.solve_none_iff p : FILO.solve p = none ↔ ¬ p.Unifiable
FILO.solve_complete p : p.Unifiable → ∃ m, FILO.solve p = some m

FILO.isUnifiable p : Bool
FILO.isUnifiable_iff p : FILO.isUnifiable p = true ↔ p.Unifiable
```

The Boolean entry point skips reconstruction. A computable
`Decidable p.Unifiable` instance uses that entry point.
`FILO.fromEquations` adapts the central equation objects to two inequalities.

## Implemented stages and proofs

| Stage | Implementation | Principal guarantees |
| --- | --- | --- |
| Flattening I, constant projection, flattening II (§§4.2–4.4) | `Preprocessing/`, `Preprocessing.lean` | `Preprocessing.unifiable_iff`; actual solutions transfer back through `Preprocessing.column_sound`. |
| TOP/CONSTANT/NOTHING (§4.5) | `Choices/Basic.lean` | Disjoint classification; actual supported assignments satisfy the consistency checks. |
| Necessary status clauses | `Choices/Constraints.lean` | `clauses_sound`: every solution satisfies the parent/child and word-provider clauses. Literal-only contradictions are rejected before variable setup. |
| Compact names | `Choices/Indexing.lean` | Map structured names to integer indices once; `encode_decode`, `run_sound`, and `run_complete` transfer the same search back to the original classifications. |
| Indexed propagation | `Choices/Propagation.lean` | Occurrence lists are built once. Forward/backward sweeps immediately use earlier removals; `close_preserves` and `close_fixed` prove preservation and a genuine fixed point. |
| Partial-choice search | `Choices/Search.lean` | Propagate after each decision; branch only on ambiguous domains. `searchDomains_sound` and `searchDomains_complete`; strict domain-cardinality termination. |
| Implicit solver rules 1–8 (§4.6) | `Goal/Implicit.lean` | Critical checks 5/7/8 precede simplification. `fails_impossible`, `simplify_correct`, `reduce_some_correct`, and `reduce_complete`. |
| No-unsolved-constraints case: rule 9 (§4.6) | `Goal/Starts.lean` | Direct reconstruction from starts and increasing subsumptions; `Starts.solve_sound`. No shortcut search runs on this path. |
| Starts and reduced, choice-specific goals | `Goal/Prepared.lean` | Initial membership, TOP removal, and constant components; `compatible_local` transfers residual shortcut satisfaction to the original generic clauses. |
| Stored resolvers and reconstruction (§4.7) | `Shortcuts/Table.lean` | Acyclic backward references; memoized oldest-to-newest reconstruction; `materialize_correct`, `trace_correct`. |
| Good-variable shortcut generation (§4.7) | `Shortcuts/Generation.lean` | Subsets are generated from good active atoms; `fresh_sound`, `fresh_complete`, `stalled_ready`. |
| Shortcut loop (§4.7) | `Shortcuts/Engine.lean` | Stops when the initial shortcut resolves or no new shortcut appears; `search_sound`, `search_complete`. |
| Composition and output (§4.8) | `GenericSolver.lean`, `Solver.lean` | Both reconstruction paths and all constant columns compose into the public soundness and completeness theorems; `solve_eq_uncached` proves exact result preservation by column caching. |

The public solver uses this entire pipeline. The old complete-choice traversal
and its separate static-domain implementation were removed. Status propagation
is a pruning stage, not a substitute for the implicit and shortcut word solvers.
The superseded direct generic-goal
solver was removed from `Shortcuts/Search.lean`; that file now imports the
choice-specific engine. The subset enumerator was retained separately in
`Shortcuts/Enumeration.lean`. There is no fallback to the old direct solver.

## Termination and execution

Domain propagation strictly deletes entries until it reaches its actual fixed
point. Each partial-choice branch also strictly deletes an entry; there is no
fallback to complete-assignment enumeration. Shortcut search strictly reduces the finite unexplored shortcut universe
on every recursive call. These are termination proofs for the executable
recursive functions, not assumptions or user-supplied fuel bounds.

Each shortcut stores its chosen resolver edges to an older table. Reconstruction
folds that table once and reuses already reconstructed entries; it does not
rerun saturation or search for the same resolver again. The rule-9 path instead
uses structural component depth to propagate start particles to parents.

The public matrix-producing solver traverses a duplicate-free, syntax-derived
list of input constants. `solveColumns` solves each visited constant once,
stops immediately on failure, and stores successful columns in a finite table.
Returned matrix rows read that table; they do not rerun column search.
`Problem.mem_constantList` and `Problem.constantList_nodup` establish exact
coverage without duplicates. `solveColumns_lookup` recovers the exact original
column result, and `solve_eq_uncached` proves equality with the former wrapper,
including every coordinate of a successful matrix. The uncached expression is
only a theorem specification, not an executable fallback. Missing required
columns cannot produce a successful result; zero remains the value for
constants absent from the input. No stronger assumptions on label types are
introduced. The Boolean entry point still skips reconstruction.

`solveFlatColumn` accepts the already flattened input. The ordinary matrix
wrapper shares this input across columns. The support-restricted wrapper also
flattens each support term once: `Coordinates.prepare_at_eq` proves exact
equality with independently flattening each column's specification, and
`Coordinates.solve_eq` proves equality of the resulting matrices.

Search returns a plain-data reconstruction plan. Plans, shortcut entries, and
returned matrices have no correctness-proof fields. Predicates such as
`Prepared.Valid`, `Table.Certified`, and `Plan.Correct` are proof invariants:
the actual computations are proved to establish them. They are not assumptions
supplied to the public solver and are not runtime output-validation checks.

## Semantic details

The existing additive inequality orientation is preserved: the left word set
is included in the right word set, opposite to the paper's subsumption notation.
Both increasing and decreasing directions of every defined component link are
proved, along with exact constant components and the finite role alphabet.
The final theorems concern the original `Problem.IsSolution` / `Problem.Unifiable`,
not a new definition in terms of successful search.

Choice classification distinguishes empty languages (TOP), languages containing
the empty word (CONSTANT), and nonempty languages without it (NOTHING).
Completeness extracts this exact classification from an arbitrary genuine
solution. For soundness, minimal reconstruction may leave an unneeded
NOTHING variable empty: the proof therefore does **not** assume that the output
realizes every guessed status exactly. It proves directly that the constructed
substitution satisfies the original equations/inequalities. The pointwise
choice facts used by implicit simplification are explicitly established along
the reconstruction proof, rather than postulated.

Only the initial shortcut may contain the current constant or a constant
component. Relative reconstruction appends edge labels on the right, which
implements the paper's prefixing operation without reversing homomorphism order.

## Verification boundary

`Coordinates.lean` provides sound and complete solving with a shared finite
coordinate alphabet and a list of `(term, allowed coordinates)` restrictions.
Every forbidden coordinate is zero; coordinates outside the shared alphabet
are unrestricted. This avoids expanding one term/coordinate pair per
prohibition. `WordRules.compile_exact` proves this encoding is precisely the
shared E conditions. FILO preprocessing, search, reconstruction, and caching
are reused; no word-length bound is introduced.

Domains use finite sets of integer-indexed names, and fixed-point sweeps
still visit all occurrence entries. Packed array/bitset domains, a
change-driven scheduling queue, and reuse between distinct E-search states
are further optimizations, not features of this implementation.

`lake build` checks the executable code and the complete proof chain.
There are no `sorry`/`admit`, custom axioms, assumed solver stages, unsafe
proof shortcuts, runtime substitution validation, or test files.
The proofs use Lean/mathlib's standard foundational axioms.

The scope is deciding ground unifiability and returning one ground unifier.
No claim is made about most-general unifiers, enumeration of all unifiers,
OWL/GUI compatibility, or measured performance relative to the Java application.
