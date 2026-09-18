import ACUIhE.Equation.Definition

namespace ACUIhE

universe u v w x

/--
Formal derivations from the ACUIhE equations and injectivity rule.

The congruence constructors express that equals may be replaced by equals
under each operation in the signature. Since the axiom constructors range
over arbitrary terms, they also include every substitution instance of an
ACUIhE equation. The `free_inj` constructor expresses cancellation for the
injective otherwise-free operator.
-/
inductive Derives {Const : Type u} {Var : Type v} {Hom : Type w} :
    Term Const Var Hom → Term Const Var Hom → Prop where
  | refl (term : Term Const Var Hom) : Derives term term
  | symm {left right : Term Const Var Hom} :
      Derives left right → Derives right left
  | trans {left middle right : Term Const Var Hom} :
      Derives left middle → Derives middle right → Derives left right
  | add_congr {left₁ left₂ right₁ right₂ : Term Const Var Hom} :
      Derives left₁ right₁ → Derives left₂ right₂ →
        Derives (.add left₁ left₂) (.add right₁ right₂)
  | hom_congr (name : Hom) {left right : Term Const Var Hom} :
      Derives left right → Derives (.hom name left) (.hom name right)
  | free_congr {left right : Term Const Var Hom} :
      Derives left right → Derives (.free left) (.free right)
  | free_inj {left right : Term Const Var Hom} :
      Derives (.free left) (.free right) → Derives left right
  | add_assoc (a b c : Term Const Var Hom) :
      Derives (.add (.add a b) c) (.add a (.add b c))
  | add_comm (a b : Term Const Var Hom) :
      Derives (.add a b) (.add b a)
  | add_zero (a : Term Const Var Hom) :
      Derives (.add a .zero) a
  | add_idem (a : Term Const Var Hom) :
      Derives (.add a a) a
  | hom_add (name : Hom) (a b : Term Const Var Hom) :
      Derives (.hom name (.add a b))
        (.add (.hom name a) (.hom name b))
  | hom_zero (name : Hom) :
      Derives (.hom name (.zero : Term Const Var Hom)) .zero
  | free_zero :
      Derives (.free (.zero : Term Const Var Hom)) .zero

/--
(Soundness)
Every equation derivable from the ACUIhE axioms is valid in every ACUIhE
algebra, for every interpretation of constants and variables.
-/
theorem Derives.sound {Const : Type u} {Var : Type v} {Hom : Type w}
    {α : Type x} [ACUIhE Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (derivation : Derives left right) :
    left.eval interpretConst interpretVar =
      right.eval interpretConst interpretVar := by
  induction derivation with
  | refl => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ leftHypothesis rightHypothesis =>
      exact leftHypothesis.trans rightHypothesis
  | add_congr _ _ leftHypothesis rightHypothesis =>
      simp only [Term.eval]
      rw [leftHypothesis, rightHypothesis]
  | hom_congr name _ inductionHypothesis =>
      exact congrArg (H name) inductionHypothesis
  | free_congr _ inductionHypothesis =>
      exact congrArg E inductionHypothesis
  | free_inj _ inductionHypothesis =>
      exact E_injective inductionHypothesis
  | add_assoc => exact ACUIhE.add_assoc _ _ _
  | add_comm => exact ACUIhE.add_comm _ _
  | add_zero => exact ACUIhE.add_zero _
  | add_idem => exact ACUIhE.add_idem _
  | hom_add => exact ACUIhE.hom_add _ _ _
  | hom_zero => exact ACUIhE.hom_zero _
  | free_zero => exact ACUIhE.free_zero

/-- Every derivable equation is semantically valid. -/
theorem Derives.semanticallyEquivalent {Const : Type u} {Var : Type v}
    {Hom : Type w} {left right : Term Const Var Hom}
    (derivation : Derives left right) :
    SemanticallyEquivalent left right := by
  intro α _ interpretConst interpretVar
  exact derivation.sound interpretConst interpretVar

end ACUIhE
