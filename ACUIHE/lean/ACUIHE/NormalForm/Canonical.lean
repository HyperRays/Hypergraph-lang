import ACUIHE.Solver.Correctness

namespace ACUIHE.Solver

universe u v w

/-- Canonicalize an abstract normal form by reifying and normalizing it. -/
def canonicalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : NormalForm Const Var Hom :=
  normalize (reify normalForm)

/-- A normal form is canonical when canonicalizing it makes no change. -/
def IsCanonical
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Prop :=
  canonicalize normalForm = normalForm

/-- Normal forms produced by `normalize` are fixed points of canonicalization. -/
@[simp]
theorem canonicalize_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) :
    canonicalize (normalize term) = normalize term := by
  unfold canonicalize
  exact (normalize_eq_of_derives (derives_reify_normalize term)).symm

/-- Canonicalization is idempotent. -/
@[simp]
theorem canonicalize_idempotent
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    canonicalize (canonicalize normalForm) = canonicalize normalForm := by
  exact canonicalize_normalize (reify normalForm)

/--
Two normal forms canonicalize to the same form exactly when their
reifications are semantically equivalent.
-/
theorem canonicalize_eq_iff_semanticallyEquivalent
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    canonicalize left = canonicalize right ↔
      SemanticallyEquivalent (reify left) (reify right) := by
  unfold canonicalize
  exact derives_iff_normalize_eq.symm.trans soundness_and_completeness

/-- Semantically equivalent canonical forms are equal. -/
theorem canonical_unique
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (leftCanonical : IsCanonical left)
    (rightCanonical : IsCanonical right)
    (equivalent : SemanticallyEquivalent (reify left) (reify right)) :
    left = right := by
  rw [← leftCanonical, ← rightCanonical]
  exact
    (canonicalize_eq_iff_semanticallyEquivalent left right).mpr equivalent

end ACUIHE.Solver
