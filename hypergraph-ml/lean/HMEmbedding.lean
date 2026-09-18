import HMEmbedding.Examples

/-!
Verified embedding of the pure rank-1 Damas–Milner typing system into ACUIhE.

From Hypergraph-ml/lean: `lake build HMEmbedding`

The encoding uses the existing O_i for arrows and products. Bound variables
are scoped by finite sets; the six HM rules are defined once, with independent
source and target type operations. Target equality and substitution are the
existing ACUIhE operations, with no additional algebraic axioms.

Main results:
* encode_equal_iff: preservation and reflection of type equality.
* encode_subst / encode_fv: substitution and free-variable preservation.
* full_hm_embedding: preservation and reflection of ALL typing derivations,
  including GEN, INST, ABS, COMB, TAUT, LET and arbitrary environments.
* instance_iff / principal_iff: instances and principal-scheme status correspond.
* solver_iff: the existing unrestricted solver decides translated HM equations.
  A well-founded retraction of arbitrary solutions proves the reverse direction.

This is a formal embedding, not a new AST-to-constraint inference implementation.
It does not compute principal schemes or claim that every ACUIhE type is an HM
type. It uses the pure HM core, with base constants and products; polymorphic
recursion, higher-rank polymorphism, subtyping, and mutation are outside that core.
The reference core admits recursion via a polymorphic fix constant in the context.

Reference: Damas–Milner, Principal type-schemes for functional programs, §§2–5:
https://steshaw.org/hm/milner-damas.pdf
-/

#print axioms HMEmbedding.encode_equal_iff
#print axioms HMEmbedding.encode_subst
#print axioms HMEmbedding.encode_fv
#print axioms HMEmbedding.full_hm_embedding
#print axioms HMEmbedding.instance_iff
#print axioms HMEmbedding.principal_iff
#print axioms HMEmbedding.unifiable_iff
#print axioms HMEmbedding.solver_iff
#print axioms HMEmbedding.Examples.mixed_id_typed
#print axioms HMEmbedding.Examples.higher_order_id
#print axioms HMEmbedding.Examples.id_alpha_renaming
#print axioms HMEmbedding.Examples.capture_rejected
#print axioms HMEmbedding.Examples.occurs_rejected
