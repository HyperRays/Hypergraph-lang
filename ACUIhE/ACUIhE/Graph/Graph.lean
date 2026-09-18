import ACUIhE.Graph.Fold
import ACUIhE.Graph.PresentationNormalization

/-!
# Canonical graphs for the full ACUIhE algebra

`ACUIhE.Graph` is the canonical representation, not an indexed storage DAG.
Each graph has a finite-set layer of word-labelled particles and nonzero
canonical E children. Equality ignores presentation ordering and duplicates
recursively, without retaining node IDs or a particular sharing layout.

This entry point imports:

* `Structure`: finite presentations, structural equality, the graph type,
  local-layer types, the ACUIh normal-form embedding, and the full algebra instance;
* `Semantics`: presentation reification and interpretation in arbitrary models;
* `Normalization`: normalization, certified reification, soundness,
  completeness, and canonicality;
* `Decision`: executable graph equality and full-theory derivability;
* `Layers`: the finite-set layer interface;
* `Fold`: structural folds and induction over canonical E children, retaining
  original summand identities independently of computed results;
* `PresentationNormalization`: executable, input-derived enumerations whose
  graphs are proved equal to the existing canonical normalization.

Use `Graph.normalize` on full terms. The theorems
`Graph.normalize_eq_iff_derives`, `Graph.normalize_reify`,
`Graph.reify_normalize`, and `Graph.isCanonical` establish uniqueness and
both reification round trips.
`Graph.canonicalize` is now a graph-to-graph fixed-point operation:
every graph is already canonical.
-/
