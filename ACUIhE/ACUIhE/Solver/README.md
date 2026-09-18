# Full ACUIhE unification

Import `ACUIhE.Solver`. Inputs are lists of the central `Equation` objects;
`fromInequalities` uses the central conversion of `A ≤₊ B` into `A + B = B`.
Constants, variables, and homomorphism labels require only decidable equality.

```lean
Solver.solve (p : Solver.Problem Const Var Hom) :
  Option (Var → Graph Const Empty Hom)

Solver.solve_sound p : Solver.solve p = some σ → p.IsSolution σ
Solver.solve_none_iff p : Solver.solve p = none ↔ ¬ p.Unifiable
Solver.solve_complete p : p.Unifiable → ∃ σ, Solver.solve p = some σ

Solver.isUnifiable p : Bool
Solver.isUnifiable_iff p : Solver.isUnifiable p = true ↔ p.Unifiable
```

`Problem.Unifiable` means existence of an ordinary term substitution making
each original equation equal in every ACUIhE algebra. It is not defined by
successful search. `Problem.unifiable_iff_graph` proves equivalence with a
ground canonical-graph solution by grounding any residual variables to zero.
`solve_complete_of_unifier` accepts nonground substitutions over any target
variable type. The result is one unifier, not an enumeration of all unifiers.

## Shared fragment implementation

The mixed solver does not contain its own E-matching rules or recursive search.

- `ACUIESolver/Matching/Rules.lean` defines complete and pending E conditions,
  positive-name groups, their semantics, and preservation of pending conditions.
- `FiniteRules.lean` interprets them as finite-set constraints, solved by the
  original ACUIESolver Horn procedure.
- `WordRules.lean` interprets the same conditions as word-valued layer
  constraints, solved by FILO. Both translations are proved exact.
- `GroupSearch.lean` supplies the single pruned, ordered-group traversal.
- `Iteration.lean` supplies the cached reconstruction traversal and its
  finite-dependency stabilization theorem. ACUIESolver's cached output is
  still proved syntactically equal to its original semantic reconstruction.

FILO's `Coordinates.lean` extends its existing column procedure with prescribed
coordinate support. A single finite alphabet is shared by all support
restrictions, and each restricted term is stored and flattened once. Within
each partial layer system, each required column is solved once and cached. A
coordinate restriction forbids every word at a prohibited E name, but leaves
all words available at permitted names and original constants. In particular,
an E child can contain `h(a)`; its allowed coordinate does not impose `h(a) ≤₊ a`.

Partial states distinguish pending positive edges from edges committed to zero.
All original layer equations and shared variables remain coupled throughout
search. No proof assumes that distinct positive groups reconstruct to distinct
values, or that positive groups must reconstruct to nonzero values.

## Proof organization

- `Problem.lean`: ordinary substitution, full-theory unification, and the
  equivalence with graph solutions.
- `Normalization.lean`: normalize both sides by the full graph normal form;
  cancel exposed E edges using `Cancellation.lean`, then remove canonical
  identities and duplicate equation pairs. Preservation is
  proved for every interpretation and every individual ordinary substitution,
  including nonground substitutions, and for the inequality input interface.
- `Prepared.lean`: a list of ACUIh equations coupled by equations
  `root = E(child)`.
- `Preparation.lean`: exact separation of normalized layers at E boundaries;
  each distinct canonical E child is named once, using a disjoint
  auxiliary-variable type. Equal graphs share a name even if their raw
  presentations have different orders.
- `Search.lean`: supplies these layers to the shared E conditions and traversal.
- `Interpretation.lean`: evaluates word-valued rows in a full algebra.
- `Reconstruction.lean`: the shared iteration constructs a solution of every
  prepared equation and E edge.
- `Projection.lean`: any genuine graph solution supplies a successful symbolic
  matching. Graph-child height gives a strict dependency order. This projection
  is used only in the completeness proof, not to discard parts of runtime input.
- `Decision.lean`: composes both directions into the public results above.

Before layer preparation, `Decomposition.lean` first exposes constructor
shapes hidden by additive units or repeated terms, with a proof of preservation
in every interpretation. It separates equations only when
outer constants and homomorphism prefixes are provably disjoint. It cancels
matching homomorphism prefixes in the canonical free algebra; this does not
assert that homomorphisms are injective in every model. `Elimination.lean`
substitutes explicitly determined variables through the entire problem and
retains a reconstruction map. Self-referential bindings are left for the full
solver. A contradictory closed equation is rejected by canonical equality.
The transformation is proved equivalent to the original `Problem.Unifiable`.

`ForcedMatching.lean` also derives child equalities from finite sums of E
terms. It requires a provably nonzero child with exactly one compatible
partner, reusing the existing constant-word compatibility and positivity
tests through the graph projection. Association, zeros, and repeated raw
partners are handled without assuming a bijection: several children may
match one partner. The original equation is retained, and ambiguous or
possibly vanishing children remain for the full solver. `Decomposition.run_correct`
proves equality of the solution sets for every canonical graph assignment;
the public ordinary-unification theorems continue to use the original theory.
Elimination keeps undetermined variables pending and searches them again after
each binding. Each recursive call erases the selected variable from the finite
input list; `Elimination.select_progress` proves the strict decrease. Thus a
newly exposed binding is used without introducing an iteration cutoff.

`Forced.lean` proves required positive E support and strict dependencies
between E roots. `Compatibility.lean` checks necessary constant-provider
conditions, allowing variables to supply arbitrary words beneath their
prefixes. These facts prune the same ordered-group traversal. Every genuine
completion survives the checks. Dependency and incompatibility lists are
shared across that traversal. `FILO/Deferred.lean` retains the existing FILO
plans at intermediate states; its `defer_eq` theorem proves exact matrix
equality when reconstruction is requested. The Boolean API never forces it.

The executable solver has no correctness-proof inputs, search-depth bounds,
candidate-substitution validation, or fallback procedure. Termination and the
finite reconstruction bound are proved. `isUnifiable` skips graph and column
reconstruction; it still decides the required FILO columns during E search.

Preprocessing retains input-derived finite enumerations for FILO's term
interface. Their graphs are proved equal to `Graph.normalize`; enumerations
themselves need not have identical order. All deduplication uses canonical
graph identity, with no ordering requirement on labels. Consequently `E(0)`
introduces no auxiliary variable, and homomorphism distribution, zero removal,
and idempotence happen before E search. Duplicate equation pairs are compared
in their given orientation. Exposed `E(A) = E(B)`, `E(A) = 0`, and `0 = E(B)`
are recursively reduced to their child equations. Cancellation is proved in
every full algebra; it does not assume E is monotone. This normalization pass does not cancel
homomorphism prefixes; the separate decomposition pass above proves that
operation at the free-algebra unification boundary. No search-optimal equation
ordering is claimed.

The shared FILO search now propagates necessary word-provider and parent/child
clauses after partial choices. It rejects literal-only contradictions before
building domains and occurrence lists. The complete implicit and shortcut
word solvers are unchanged; there is no second fragment solver or fallback.

Build with `lake build`. Rebuild the benchmark executable with
`lake build acuihe_bench`. The
[indexed-propagation comparison](../../Benchmarks/results/INDEXED_COMPARISON.md)
and [coupled-system comparison](../../Benchmarks/results/INDEXED_COUPLED.md)
measure earlier implementations. The
[canonical-preprocessing comparison](../../Benchmarks/results/CANONICALIZATION_COMPARISON.md)
measures the preceding implementation on retained inputs with the same deadlines as
the previous solver. The
[earlier shared-rule results](../../Benchmarks/results/SHARED_RULES_REPORT.md)
remain available unchanged. These synthetic measurements do not
establish asymptotic complexity or performance on arbitrary workloads.

After these changes, `lake build` succeeds. An explicit `#print axioms` audit
of `solve_sound`, `solve_complete_of_unifier`, `solve_none_iff`, and the new
preservation/search lemmas reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` (or subsets). There are no new assumed
stages or proof holes. Packed array domains, change-driven scheduling, and
incremental reuse across distinct E-search states remain future work.

Run `lake build acuihe_optimization_tests` and
`.lake/build/bin/acuihe_optimization_tests` for decision/witness regressions.
The executable checks returned witnesses against the original equations; its
module also audits the public correctness theorems with `#print axioms`.
