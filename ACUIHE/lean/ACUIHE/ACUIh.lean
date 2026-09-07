import ACUIHE.ACUIh.Canonical
import ACUIHE.NormalForm.Core

/-! Qualification of terms and normal forms as the E-free ACUIh fragment. -/

namespace ACUIHE

universe u v w

namespace Term

/-- A term belongs to the ACUIh fragment when it contains no `E` operator. -/
def IsACUIh {Const : Type u} {Var : Type v} {Hom : Type w} :
    Term Const Var Hom → Prop
  | .zero => True
  | .const _ => True
  | .var _ => True
  | .add left right => IsACUIh left ∧ IsACUIh right
  | .hom _ body => IsACUIh body
  | .free _ => False

end Term

namespace Solver

/--
An executable check that a normal form belongs to the ACUIh fragment.

Constants, variables, and homomorphism paths are accepted. Encountering any
encoded `E` summand makes the result false.
-/
def isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Bool :=
  normalForm.fold true (fun left right => left && right)
    (fun _ _ => true)
    (fun _ _ => true)
    (fun _ _ => false)

@[simp]
theorem isACUIh_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    isACUIh (∅ : NormalForm Const Var Hom) = true := by
  simp [isACUIh]

@[simp]
theorem isACUIh_constantForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    isACUIh (constantForm (Var := Var) (Hom := Hom) name) = true := by
  simp [isACUIh, constantForm]

@[simp]
theorem isACUIh_variableForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    isACUIh (variableForm (Const := Const) (Hom := Hom) name) = true := by
  simp [isACUIh, variableForm]

@[simp]
theorem isACUIh_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    isACUIh (left ∪ right) = (isACUIh left && isACUIh right) := by
  unfold isACUIh
  apply NormalForm.fold_union
  intro value
  exact Bool.and_true value

@[simp]
theorem isACUIh_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) :
    isACUIh (prefixHom name normalForm) = isACUIh normalForm := by
  unfold isACUIh
  simpa only [id_eq] using
    (NormalForm.fold_prefixHom
      (zero := true)
      (combine := fun left right => left && right)
      (zeroRight := Bool.and_true)
      (onConstant := fun _ _ => true)
      (onVariable := fun _ _ => true)
      (onEOperator := fun _ _ => false)
      name id
      (mapZero := rfl)
      (mapCombine := by intro left right; rfl)
      (mapConstant := by intro path constantName; rfl)
      (mapVariable := by intro path variableName; rfl)
      (mapEOperator := by intro path body; rfl)
      normalForm)

/-- Normalizing an E-free term produces an ACUIh normal form. -/
theorem isACUIh_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) (acuih : term.IsACUIh) :
    isACUIh (normalize term) = true := by
  induction term with
  | zero => exact isACUIh_empty
  | const name => exact isACUIh_constantForm name
  | var name => exact isACUIh_variableForm name
  | add left right leftHypothesis rightHypothesis =>
      rw [normalize_add, isACUIh_union,
        leftHypothesis acuih.1, rightHypothesis acuih.2]
      rfl
  | hom name body inductionHypothesis =>
      rw [normalize_hom, isACUIh_prefixHom,
        inductionHypothesis acuih]
  | free body inductionHypothesis =>
      exact False.elim acuih

end Solver

end ACUIHE
