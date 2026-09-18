# ACUIESolver: verified ordered E-matching

`solve` decides finite ACUIE unification problems and constructs one unifier
when one exists. It preserves ACUI addition, injective `E`, and `E(0) = 0`.
No distributivity of E, nonzero-constructor assumption, syntactic occurs
check, or restriction on the original substitution is imposed.

## Public interface

Import `ACUIhE.ACUIESolver` (also imported by `ACUIhE`).

`Problem Const Var` is a list of central `ACUIE.Equation Const Var` objects.
`fromInequalities` represents `A ≤₊ B` by `A + B = B`. Only decidable
equality on constants and variables is required; their types need not be finite.

`solve p` returns either:

- `Result.unifier σ`, with an ordinary substitution solving the original problem;
- `Result.unsatisfiable`, exactly when no unifier exists.

The independent semantic definition is unchanged:

```lean
p.IsUnifier σ := ∀ q ∈ p,
  (q.left.substitute σ).Equal (q.right.substitute σ)

p.Unifiable := ∃ σ, p.IsUnifier σ
```

`isUnifiable` and `Problem.decidableUnifiable` use the new algorithm.
The solver decides existence and returns one witness; it does not enumerate a
complete set of most-general unifiers.

## Algorithm

The public solver runs this algorithm directly on the original input, without
first expanding the symbolic `preview` branches. Write `n` for the number of
input subterm occurrences and `m` for the number of E occurrences.

1. Collect the input subterm occurrences and choose which E occurrences have
   positive names. All other E occurrences are committed to zero. Non-E
   occurrences never branch.
2. Partition the remaining positive occurrences into ordered groups, choosing
   the highest remaining group first. The group's rank is computed as the
   number of remaining occurrences. Thus the ordered groups determine their
   labels uniquely; unused numeric label slots are not searched. Subsets are
   chosen depth first without materializing a powerset.
3. Propagate flat constraints immediately after the zero choice and after
   each group choice. Finished groups impose their complete constraints.
   Undecided positive edges keep necessary constraints: their row contains
   their own name, contains only remaining names, and their child excludes
   their own name. Their stored zero labels are **placeholders, not zero
   decisions**. A contradiction prunes every completion of the partial state.
4. Unknown rows describe input subterms; lookup unions the rows of equal raw
   subterms, so repeated variables
   are shared across every depth. Constants and E classes have fixed rows,
   sums are row unions, and all original equations are included. Equal positive
   names impose child-row equality; children use strictly lower-ranked names.
   Compile every atom coordinate into Horn implications on *absent*
   memberships. Starting from no absences, derive consequences to a fixed
   point, stopping as soon as a propagation step adds nothing. A derived
   contradiction rejects the partial state; otherwise the complement
   is the greatest satisfying membership assignment. No row subsets are
   enumerated. At a completed matching, reuse these rows directly.
5. Reconstruct a substitution using arrays of cached named terms. Dependencies
   refer to earlier rounds, and shared named terms are reused. Return the first
   successful branch, or unsatisfiable after all ordered matchings fail.

The branch checks are syntactic Horn constraints, not validation of candidate
term substitutions. Plain table data is produced by the layer solver; no
caller-supplied proof or semantic oracle is part of execution.

## Proof chain

### Layer compilation and propagation

`Layers.Horn.saturate` recurses only when another absent-membership bit is
derived. `saturate_eq_closure` proves exact equality with the original
fixed-round closure, and `solve_eq_fixedRounds` proves the solver result is
unchanged. `solve_sound`, `solve_complete`, and `solve_least` prove exact
decision and least-model synthesis for arbitrary finite Horn systems.

`Layers.compile_exact` proves equivalence between the compiled Horn system
and the original flat inclusions. `Layers.solve_sound` and
`Layers.solve_complete` therefore establish the layer solver's soundness and completeness.

`Matching.constraints_exact` connects a matching branch's flat constraints to
the semantic reconstruction interface: a valid ranked table with the specified
E-name classes.

### Partial pruning and symmetry removal

`Matching.Completion` explicitly separates undecided positive edges from
assigned zero edges. `partialConstraints_necessary` proves every full
completion satisfies the partial constraints. Consequently, `prune_sound`
proves a rejected partial state has **no** full solution extending it.
`partialConstraints_empty` identifies a finished partial system with the
original exact matching compiler.

`constraints_canonicalize` proves that replacing numeric labels by canonical
group ranks leaves the constraint list itself unchanged. `next_group` proves
that every canonical completion supplies an available next group at exactly
the computed rank. `GroupSearch.run_ne_none` combines this with safe pruning.

`GroupState.assign` preserves the rank-counting invariant. `GroupPath.canonical`
and `findTable_canonical` prove completed paths have canonical ranks, without
a runtime canonicality filter. `orderedPartition_path_unique` proves that
the same ordered partition has one positive support, group path, and numeric
encoding. `GroupSearch.run_leaf_path` connects these structural paths to execution;
`findTable_unique_path` gives the corresponding unique-path result for a
returned matching. `chooseSubset_none_iff` proves the streaming subset
chooser exhaustive, and `subset_choice_unique` proves uniqueness of each
include/exclude decomposition.

### Completeness from arbitrary unifiers

Start with any unifier, of any depth, including nonground unifiers. Project
its canonical graph layers onto the input constants and nonzero input E
occurrences. Projection preserves union.

`Matching.Order` identifies equal E children and orders distinct ones by
height, breaking height ties by first occurrence. Zero receives label zero.
Compressed labels are bounded by the number of nonzero input occurrences,
hence by `m`; strict graph-child dependencies receive strictly increasing
labels outwards.

`Matching.projected_valid` and `projected_exactNames` prove that the projected
rows solve that branch. Canonicalization preserves those constraints exactly.
`initial_completion`, `next_group`, and `GroupSearch.run_ne_none` then prove that
the pruned group search cannot report failure when an original unifier exists.
No assumed small-model or depth bound is used.

### Reconstruction and public correctness

The retained `Finite.Table.eval_reconstruct` theorem interprets every input
subterm correctly in **every ACUIE algebra**. Names may decode to zero or
coincide: distinct labels are not disequality assertions.

`Matching.atomCache_eq` proves the cached reconstruction syntactically equal
to the semantic reconstruction at every round and index. Thus
`Matching.reconstruct_sound` applies without any post-hoc substitution check.

The public guarantees are unchanged:

- `solve_unifier_sound`
- `solve_complete`
- `solve_unifiable_iff`
- `solve_unsatisfiable_iff`
- `isUnifiable_eq_true` and `isUnifiable_eq_false`

All recursive definitions terminate. There is no fuel parameter, cutoff,
custom axiom, unfinished proof, or exhaustive-row fallback.

## Search size and representation

The search now ranges over zero choices and ordered partitions of the other
E occurrences, not all `(m+1)^m` numeric label assignments. It prunes partial
matchings, and non-E positions do not branch. Each partial system has
polynomially many flat constraints and `n*n` membership bits. Strict Horn
expansions add bits, and propagation stops at its first fixed point.

This remains a combinatorial search; these refinements are not a polynomial
time claim. Propagation is currently recomputed for each partial state rather
than reusing a parent's Horn model. The proofs establish exactness, safe
pruning, unique ordered-group encodings, and termination, not a wall-clock
speedup for every input.

The cached reconstruction uses array-backed vectors. Its exact equivalence
is proved; the project does not claim a formal machine-cost theorem or
runtime pointer-sharing theorem. Printing or fully expanding an ordinary
term can still cost its expanded output size.

## Organization and compatibility

- `Layers/Horn.lean`: finite propagation, stabilization, soundness, completeness.
- `Layers/Flat.lean`: set expressions, exact compilation, complete layer solving.
- `Matching/Rules.lean`: shared complete and pending E conditions and their semantics.
- `Matching/FiniteRules.lean`: exact finite-set interpretation of the shared rules.
- `Matching/WordRules.lean`: exact word-valued interpretation, using FILO's coordinate solver.
- `Matching/Constraints.lean`: supplies ACUIE layers to the shared rules and proves exactness.
- `Matching/Order.lean`: ordered finite labels extracted from arbitrary values.
- `Matching/Completeness.lean`: canonical-graph projection supplies a branch.
- `Matching/Canonical.lean`: canonical ranks and exact constraint preservation.
- `Matching/Partial.lean`: partial constraints and no-completion pruning proof.
- `Matching/Groups.lean`: descending groups and the rank-counting invariant.
- `Matching/GroupPaths.lean`: canonicality and uniqueness of group paths.
- `Matching/SubsetChoice.lean`: streaming, exhaustive subset choices.
- `Matching/GroupSearch.lean`: terminating partial-state search and completeness.
- `Matching/FirstSome.lean`: compatibility helper for existing residual lists.
- `Matching/Iteration.lean`: shared cached iteration and strict-dependency stabilization.
- `Matching/Reconstruction.lean`: cached reconstruction and exact equivalence.
- `Matching/Search.lean`: complete matching solver.
- `Solver.lean`: public result, unchanged semantic guarantees and decision instance.
- `Finite/`: retained finite representation and semantic proof infrastructure.
  `Finite/Search.lean` now only forwards legacy names to the new solver.

The old `Finite/Assignments.lean` row-mask enumeration and numeric-label
enumeration have been removed.
`preview`, `step`, `prototype`, and symbolic `search` remain available as
separate incremental APIs. They are not a preprocessing stage or fallback
of the public complete solver.

No example tests stand in for these universal theorems.
