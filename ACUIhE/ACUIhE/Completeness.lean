import ACUIhE.Soundness

namespace ACUIhE

universe u v w

/-- Derivability is an equivalence relation on raw terms. -/
def derivationSetoid (Const : Type u) (Var : Type v) (Hom : Type w) :
    Setoid (Term Const Var Hom) where
  r := Derives
  iseqv := ⟨Derives.refl, Derives.symm, Derives.trans⟩

/--
The canonical term model: raw terms modulo equations derivable from the
ACUIhE axioms.
-/
def TermModel (Const : Type u) (Var : Type v) (Hom : Type w) :=
  Quotient (derivationSetoid Const Var Hom)

namespace TermModel

/-- Embed a raw term into its derivability equivalence class. -/
def ofTerm {Const : Type u} {Var : Type v} {Hom : Type w}
    (term : Term Const Var Hom) : TermModel Const Var Hom :=
  Quotient.mk (derivationSetoid Const Var Hom) term

instance {Const : Type u} {Var : Type v} {Hom : Type w} :
    Zero (TermModel Const Var Hom) where
  zero := ofTerm .zero

instance {Const : Type u} {Var : Type v} {Hom : Type w} :
    Add (TermModel Const Var Hom) where
  add := Quotient.lift₂
    (fun left right => ofTerm (.add left right))
    (by
      intro left₁ left₂ right₁ right₂ leftEquality rightEquality
      exact Quotient.sound
        (Derives.add_congr leftEquality rightEquality))

/-- The homomorphic operator induced on the quotient term model. -/
def hom {Const : Type u} {Var : Type v} {Hom : Type w} (name : Hom) :
    TermModel Const Var Hom → TermModel Const Var Hom :=
  Quotient.lift
    (fun term => ofTerm (.hom name term))
    (by
      intro left right equality
      exact Quotient.sound (Derives.hom_congr name equality))

/-- The free operator induced on the quotient term model. -/
def free {Const : Type u} {Var : Type v} {Hom : Type w} :
    TermModel Const Var Hom → TermModel Const Var Hom :=
  Quotient.lift
    (fun term => ofTerm (.free term))
    (by
      intro left right equality
      exact Quotient.sound (Derives.free_congr equality))

/-- The quotient by derivability is itself an ACUIhE algebra. -/
instance {Const : Type u} {Var : Type v} {Hom : Type w} :
    ACUIhE Hom (TermModel Const Var Hom) where
  hom := hom
  free := free
  add_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c
    exact Quotient.sound (Derives.add_assoc a b c)
  add_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    exact Quotient.sound (Derives.add_comm a b)
  add_zero := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    exact Quotient.sound (Derives.add_zero a)
  add_idem := by
    intro a
    refine Quotient.inductionOn a ?_
    intro a
    exact Quotient.sound (Derives.add_idem a)
  hom_add := by
    intro name a b
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    exact Quotient.sound (Derives.hom_add name a b)
  hom_zero := fun name => Quotient.sound (Derives.hom_zero name)
  free_zero := Quotient.sound Derives.free_zero
  free_injective := by
    intro left right
    refine Quotient.inductionOn₂ left right ?_
    intro left right equality
    exact Quotient.sound
      (Derives.free_inj (Quotient.exact equality))

/--
Evaluating a term in the canonical term model returns its own derivability
equivalence class.
-/
theorem eval_eq_ofTerm {Const : Type u} {Var : Type v} {Hom : Type w}
    (term : Term Const Var Hom) :
    term.eval
        (fun name => ofTerm (.const name))
        (fun name => ofTerm (.var name)) =
      ofTerm term := by
  induction term with
  | zero => rfl
  | const => rfl
  | var => rfl
  | add left right leftHypothesis rightHypothesis =>
      simp only [Term.eval]
      rw [leftHypothesis, rightHypothesis]
      rfl
  | hom name body inductionHypothesis =>
      simp only [Term.eval]
      rw [inductionHypothesis]
      rfl
  | free body inductionHypothesis =>
      simp only [Term.eval]
      rw [inductionHypothesis]
      rfl

end TermModel

/-- Every semantically valid ACUIhE equation is derivable. -/
theorem completeness {Const : Type u} {Var : Type v} {Hom : Type w}
    {left right : Term Const Var Hom}
    (validity : SemanticallyEquivalent left right) :
    Derives left right := by
  have equalityInTermModel := validity
    (α := TermModel Const Var Hom)
    (fun name => TermModel.ofTerm (.const name))
    (fun name => TermModel.ofTerm (.var name))
  rw [TermModel.eval_eq_ofTerm, TermModel.eval_eq_ofTerm] at equalityInTermModel
  exact Quotient.exact equalityInTermModel

/-- Syntactic derivability and semantic validity coincide. -/
theorem soundness_and_completeness {Const : Type u} {Var : Type v}
    {Hom : Type w} {left right : Term Const Var Hom} :
    Derives left right ↔ SemanticallyEquivalent left right :=
  ⟨Derives.semanticallyEquivalent, completeness⟩

end ACUIhE
