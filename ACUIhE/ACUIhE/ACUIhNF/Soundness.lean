import ACUIhE.ACUIhNF.Definition
import ACUIhE.ACUIhNF.Theory

/-!
# Interpretation of normal forms

Finite-set union is interpreted using the ACUI operation of the target
algebra. Normalization preserves evaluation in every ACUIh algebra.
-/

namespace ACUIhE.ACUIh

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable {α : Type x} [ACUIh Hom α]

namespace NF

local instance : Std.Commutative (fun a b : α => a + b) :=
  ⟨ACUIh.add_comm (Hom := Hom)⟩

local instance : Std.Associative (fun a b : α => a + b) :=
  ⟨ACUIh.add_assoc (Hom := Hom)⟩

local instance : Std.IdempotentOp (fun a b : α => a + b) :=
  ⟨ACUIh.add_idem (Hom := Hom)⟩

/-- Interpret every summand and join the results in an arbitrary ACUIh algebra. -/
def eval (interpretConst : Const → α) (interpretVar : Var → α)
    (normal : NF Const Var Hom) : α :=
  normal.fold (· + ·) 0 (fun summand => summand.reify.eval interpretConst interpretVar)

@[simp] theorem eval_empty (interpretConst : Const → α) (interpretVar : Var → α) :
    eval interpretConst interpretVar (∅ : NF Const Var Hom) = 0 := rfl

@[simp] theorem eval_singleton (interpretConst : Const → α) (interpretVar : Var → α)
    (summand : Summand Const Var Hom) :
    eval interpretConst interpretVar {summand} =
      summand.reify.eval interpretConst interpretVar :=
  ACUIh.add_zero _

/-- Interpretation respects the homomorphism action on normal forms. -/
@[simp] theorem eval_prepend (interpretConst : Const → α) (interpretVar : Var → α)
    (name : Hom) (normal : NF Const Var Hom) :
    eval interpretConst interpretVar (prepend name normal) =
      H name (eval interpretConst interpretVar normal) := by
  unfold eval prepend
  rw [Finset.fold_map]
  change normal.fold (fun a b : α => a + b) (0 : α)
      (fun summand => H name (summand.reify.eval interpretConst interpretVar)) = _
  simpa only [H, ACUIh.hom_zero] using
    (Finset.fold_hom (m := H name) (s := normal) (b := (0 : α))
      (f := fun summand => summand.reify.eval interpretConst interpretVar)
      (ACUIh.hom_add name))

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Idempotency permits this equation even when the summand is already present. -/
@[simp] theorem eval_insert (interpretConst : Const → α) (interpretVar : Var → α)
    (summand : Summand Const Var Hom) (normal : NF Const Var Hom) :
    eval interpretConst interpretVar (insert summand normal) =
      summand.reify.eval interpretConst interpretVar + eval interpretConst interpretVar normal :=
  Finset.fold_insert_idem

/-- Interpretation respects union, including overlapping sets of summands. -/
@[simp] theorem eval_union (interpretConst : Const → α) (interpretVar : Var → α)
    (left right : NF Const Var Hom) :
    eval interpretConst interpretVar (left ∪ right) =
      eval interpretConst interpretVar left + eval interpretConst interpretVar right := by
  induction left using Finset.induction_on with
  | empty =>
      rw [Finset.empty_union, eval_empty]
      exact ((ACUIh.add_comm _ _).trans (ACUIh.add_zero _)).symm
  | insert summand left _ ih =>
      rw [Finset.insert_union, eval_insert, eval_insert, ih]
      exact (ACUIh.add_assoc _ _ _).symm

end NF

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Normalization preserves the value of a term in every ACUIh algebra. -/
@[simp] theorem Term.eval_normalize (interpretConst : Const → α) (interpretVar : Var → α)
    (term : Term Const Var Hom) :
    NF.eval interpretConst interpretVar term.normalize = term.eval interpretConst interpretVar := by
  induction term with
  | zero => rfl
  | const => exact ACUIh.add_zero _
  | var => exact ACUIh.add_zero _
  | add _ _ ih₁ ih₂ =>
      simpa only [Term.normalize, Term.eval, NF.eval_union] using
        congrArg₂ (fun a b : α => a + b) ih₁ ih₂
  | hom name _ ih =>
      simpa only [Term.normalize, Term.eval, NF.eval_prepend] using congrArg (H name) ih

/-- Equal normal forms have equal values under every interpretation. -/
theorem NF.eval_eq_of_normalize_eq (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (equality : left.normalize = right.normalize) :
    left.eval interpretConst interpretVar = right.eval interpretConst interpretVar := by
  rw [← Term.eval_normalize interpretConst interpretVar left,
    ← Term.eval_normalize interpretConst interpretVar right, equality]

/-- Equal normal forms imply derivability using only the fragment's equations. -/
theorem NF.soundness {left right : Term Const Var Hom}
    (equality : left.normalize = right.normalize) : Derives left right := by
  apply completeness
  intro α _ interpretConst interpretVar
  exact NF.eval_eq_of_normalize_eq interpretConst interpretVar equality

end ACUIhE.ACUIh
