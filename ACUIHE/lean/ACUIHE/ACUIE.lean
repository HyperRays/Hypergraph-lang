import ACUIHE.NormalForm.Core

/-! Qualification of terms and normal forms as the homomorphism-free ACUIE fragment. -/

namespace ACUIHE

universe u v w

namespace Term

/-- A term belongs to the ACUIE fragment when it contains no homomorphic operator. -/
def IsACUIE {Const : Type u} {Var : Type v} {Hom : Type w} :
    Term Const Var Hom → Prop
  | .zero => True
  | .const _ => True
  | .var _ => True
  | .add left right => IsACUIE left ∧ IsACUIE right
  | .hom _ _ => False
  | .free body => IsACUIE body

end Term

namespace Solver

/--
An executable check that a normal form belongs to the ACUIE fragment.

Every homomorphism path must be empty, including paths inside nested `E`
bodies. Constants, variables, and recursively checked `E` summands are accepted.
This checks the normalized representation: a homomorphism applied to zero
normalizes to the empty form and is therefore accepted.
-/
def isACUIE
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Bool :=
  normalForm.fold true (fun left right => left && right)
    (fun path _ => path.isEmpty)
    (fun path _ => path.isEmpty)
    (fun path body => path.isEmpty && body)

@[simp]
theorem isACUIE_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    isACUIE (∅ : NormalForm Const Var Hom) = true := by
  simp [isACUIE]

@[simp]
theorem isACUIE_constantForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    isACUIE (constantForm (Var := Var) (Hom := Hom) name) = true := by
  simp [isACUIE, constantForm]

@[simp]
theorem isACUIE_variableForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    isACUIE (variableForm (Const := Const) (Hom := Hom) name) = true := by
  simp [isACUIE, variableForm]

@[simp]
theorem isACUIE_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    isACUIE (left ∪ right) = (isACUIE left && isACUIE right) := by
  unfold isACUIE
  apply NormalForm.fold_union
  exact Bool.and_true

@[simp]
theorem isACUIE_wrapE
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (body : NormalForm Const Var Hom) :
    isACUIE (wrapE body) = isACUIE body := by
  by_cases bodyEmpty : body = ∅
  · simp [bodyEmpty]
  · rw [wrapE_of_ne_empty bodyEmpty]
    simp [isACUIE]

/-- Normalizing a homomorphism-free term produces an ACUIE normal form. -/
theorem isACUIE_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) (acuie : term.IsACUIE) :
    isACUIE (normalize term) = true := by
  induction term with
  | zero => exact isACUIE_empty
  | const name => exact isACUIE_constantForm name
  | var name => exact isACUIE_variableForm name
  | add left right leftHypothesis rightHypothesis =>
      rw [normalize_add, isACUIE_union,
        leftHypothesis acuie.1, rightHypothesis acuie.2]
      rfl
  | hom name body inductionHypothesis =>
      exact False.elim acuie
  | free body inductionHypothesis =>
      rw [normalize_free, isACUIE_wrapE, inductionHypothesis acuie]

end Solver

end ACUIHE
