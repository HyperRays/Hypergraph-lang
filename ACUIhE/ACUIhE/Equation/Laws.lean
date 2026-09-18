import ACUIhE.Equation.Definition
import ACUIhE.Completeness
import ACUIhE.ACUIhNF.Completeness
import ACUIhE.Graph.Normalization
import ACUIhE.Transfer.Core
import Mathlib.Order.Defs.PartialOrder

/-!
# Relation laws and connections with the derivation systems

Equality and additive-order laws are proved once in `Transfer.Core`. The
three `Term.normalFormModel` adapters transfer them through faithful graph
or finite-set interpretations. The public fragment theorems are specializations.
-/

namespace ACUIhE
universe u v w x

namespace Below

variable {α : Type u} [Add α]

@[simp] theorem iff_add_eq (a b : α) : a ≤₊ b ↔ a + b = b := Iff.rfl

/-- ACUI addition induces an order, independently of the other operators. -/
@[instance_reducible] def partialOrder
    (assoc : ∀ a b c : α, (a + b) + c = a + (b + c))
    (comm : ∀ a b : α, a + b = b + a)
    (idem : ∀ a : α, a + a = a) : PartialOrder α where
  le := Below
  le_refl := idem
  le_trans := by
    intro a b c ab bc
    change a + b = b at ab
    change b + c = c at bc
    change a + c = c
    calc
      a + c = a + (b + c) := congrArg (a + ·) bc.symm
      _ = (a + b) + c := (assoc a b c).symm
      _ = b + c := congrArg (· + c) ab
      _ = c := bc
  le_antisymm := by
    intro a b ab ba
    exact (show b + a = a from ba).symm.trans ((comm b a).trans ab)

end Below

end ACUIhE

namespace ACUIhE

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

section Algebra

variable {Hom : Type w} {α : Type x} [ACUIhE Hom α]

/-- The additive order of any ACUIhE algebra; install locally when needed. -/
@[instance_reducible] def additivePartialOrder : PartialOrder α :=
  Below.partialOrder ACUIhE.add_assoc ACUIhE.add_comm ACUIhE.add_idem

theorem zero_below (a : α) : (0 : α) ≤₊ a :=
  (ACUIhE.add_comm 0 a).trans (ACUIhE.add_zero a)

/-- Named homomorphisms preserve the additive order. No such law is assumed for `E`. -/
theorem hom_below (name : Hom) {a b : α} (h : a ≤₊ b) : H name a ≤₊ H name b :=
  (ACUIhE.hom_add name a b).symm.trans (congrArg (H name) h)

end Algebra

namespace Term

theorem below_iff_semanticallyEquivalent (left right : Term Const Var Hom) :
    left.Below right ↔ SemanticallyEquivalent (.add left right) right := Iff.rfl

theorem below_iff_derives (left right : Term Const Var Hom) :
    left.Below right ↔ Derives (.add left right) right :=
  (below_iff_semanticallyEquivalent left right).trans soundness_and_completeness.symm

/-- A valid term inequality holds in algebras of any carrier universe. -/
theorem Below.sound {α : Type x} [ACUIhE Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (h : left.Below right) :
    left.eval interpretConst interpretVar ≤₊ right.eval interpretConst interpretVar :=
  ((below_iff_derives left right).mp h).sound interpretConst interpretVar

/-- The faithful additive interpretation used to transfer the shared relation laws. -/
def normalFormModel :
    Transfer.AdditiveModel (Term Const Var Hom) (Graph Const Var Hom) Term.Equal Term.add :=
  {
    normalize := Graph.normalize
    equal_iff := fun a b => (Graph.normalize_eq_iff_semanticallyEquivalent a b).symm
    join := (· + ·)
    map_add := fun _ _ => rfl
    join_assoc := ACUIhE.add_assoc (Hom := Hom)
    join_comm := ACUIhE.add_comm (Hom := Hom)
    join_idem := ACUIhE.add_idem (Hom := Hom) }

theorem Equal.refl (a : Term Const Var Hom) : a.Equal a :=
  normalFormModel.toEqualityModel.refl a

theorem Equal.symm {a b : Term Const Var Hom} (h : a.Equal b) : b.Equal a :=
  normalFormModel.toEqualityModel.symm h

theorem Equal.trans {a b c : Term Const Var Hom} (ab : a.Equal b) (bc : b.Equal c) :
    a.Equal c :=
  normalFormModel.toEqualityModel.trans ab bc

theorem Equal.add_congr {a b c d : Term Const Var Hom} (ab : a.Equal b) (cd : c.Equal d) :
    (Term.add a c).Equal (.add b d) :=
  normalFormModel.add_congr ab cd

theorem Equal.hom_congr (name : Hom) {a b : Term Const Var Hom} (h : a.Equal b) :
    (Term.hom name a).Equal (.hom name b) :=
  normalFormModel.toEqualityModel.unary_congr (.hom name) (Graph.hom name) (fun _ => rfl) h

theorem Equal.free_congr {a b : Term Const Var Hom} (h : a.Equal b) :
    (Term.free a).Equal (.free b) :=
  normalFormModel.toEqualityModel.unary_congr .free Graph.free (fun _ => rfl) h

theorem Equal.free_inj {a b : Term Const Var Hom} (h : (Term.free a).Equal (.free b)) :
    a.Equal b :=
  normalFormModel.toEqualityModel.unary_inj .free Graph.free (fun _ => rfl)
    Graph.free_injective h

theorem Below.refl (a : Term Const Var Hom) : a.Below a :=
  normalFormModel.below_refl a

theorem Below.trans {a b c : Term Const Var Hom} (ab : a.Below b) (bc : b.Below c) :
    a.Below c :=
  normalFormModel.below_trans ab bc

/-- Antisymmetry gives algebraic equality, not equality of raw syntax. -/
theorem Below.antisymm {a b : Term Const Var Hom} (ab : a.Below b) (ba : b.Below a) :
    a.Equal b :=
  normalFormModel.below_antisymm ab ba

theorem Equal.below {a b : Term Const Var Hom} (h : a.Equal b) : a.Below b :=
  normalFormModel.equal_below h

theorem equal_iff_below_below (a b : Term Const Var Hom) :
    a.Equal b ↔ a.Below b ∧ b.Below a :=
  normalFormModel.equal_iff_below_below a b

theorem equal_iff_derives (a b : Term Const Var Hom) : a.Equal b ↔ Derives a b :=
  soundness_and_completeness.symm

/-- Universal validity extends to models in any carrier universe. -/
theorem Equal.sound {α : Type x} [ACUIhE Hom α]
    (ic : Const → α) (iv : Var → α) {a b : Term Const Var Hom} (h : a.Equal b) :
    a.eval ic iv = b.eval ic iv :=
  (completeness h).sound ic iv

end Term

@[simp] theorem Equation.valid_swap (equation : Equation Const Var Hom) :
    equation.swap.Valid ↔ equation.Valid :=
  Generic.Equation.valid_swap Term.Equal.symm equation

end ACUIhE

namespace ACUIhE.ACUIh

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

section Algebra

variable {α : Type x} [ACUIh Hom α]

/-- The additive order of any ACUIh algebra, without an `E` operator. -/
@[instance_reducible] def additivePartialOrder : PartialOrder α :=
  _root_.ACUIhE.Below.partialOrder ACUIh.add_assoc ACUIh.add_comm ACUIh.add_idem

theorem zero_below (a : α) : (0 : α) ≤₊ a :=
  (ACUIh.add_comm 0 a).trans (ACUIh.add_zero a)

theorem hom_below (name : Hom) {a b : α} (h : a ≤₊ b) : H name a ≤₊ H name b :=
  (ACUIh.hom_add name a b).symm.trans (congrArg (H name) h)

end Algebra

namespace Term

theorem below_iff_semanticallyEquivalent (left right : Term Const Var Hom) :
    left.Below right ↔ SemanticallyEquivalent (.add left right) right := Iff.rfl

theorem below_iff_derives (left right : Term Const Var Hom) :
    left.Below right ↔ Derives (.add left right) right :=
  (below_iff_semanticallyEquivalent left right).trans soundness_and_completeness.symm

theorem Below.sound {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (h : left.Below right) :
    left.eval interpretConst interpretVar ≤₊ right.eval interpretConst interpretVar :=
  ((below_iff_derives left right).mp h).sound interpretConst interpretVar

end Term

namespace Term

/-- The proof-only ACUIh adapter chooses label equality internally so that the
public relation laws do not acquire `DecidableEq` assumptions. Executable
normalization still uses the caller-supplied decidable label equalities. -/
noncomputable def normalFormModel :
    Transfer.AdditiveModel (Term Const Var Hom) (NF Const Var Hom) Term.Equal Term.add := by
  classical
  exact {
    normalize := Term.normalize
    equal_iff := fun _ _ => NF.normalize_eq_iff_semanticallyEquivalent.symm
    join := (· ∪ ·)
    map_add := fun _ _ => rfl
    join_assoc := Finset.union_assoc
    join_comm := Finset.union_comm
    join_idem := Finset.union_self }

theorem Equal.refl (a : Term Const Var Hom) : a.Equal a :=
  normalFormModel.toEqualityModel.refl a

theorem Equal.symm {a b : Term Const Var Hom} (h : a.Equal b) : b.Equal a :=
  normalFormModel.toEqualityModel.symm h

theorem Equal.trans {a b c : Term Const Var Hom} (ab : a.Equal b) (bc : b.Equal c) :
    a.Equal c :=
  normalFormModel.toEqualityModel.trans ab bc

theorem Equal.add_congr {a b c d : Term Const Var Hom} (ab : a.Equal b) (cd : c.Equal d) :
    (Term.add a c).Equal (.add b d) :=
  normalFormModel.add_congr ab cd

theorem Equal.hom_congr (name : Hom) {a b : Term Const Var Hom} (h : a.Equal b) :
    (Term.hom name a).Equal (.hom name b) :=
  normalFormModel.toEqualityModel.unary_congr (.hom name) (NF.prepend name) (fun _ => rfl) h

theorem Below.refl (a : Term Const Var Hom) : a.Below a :=
  normalFormModel.below_refl a

theorem Below.trans {a b c : Term Const Var Hom} (ab : a.Below b) (bc : b.Below c) :
    a.Below c :=
  normalFormModel.below_trans ab bc

/-- Antisymmetry gives algebraic equality, not equality of raw syntax. -/
theorem Below.antisymm {a b : Term Const Var Hom} (ab : a.Below b) (ba : b.Below a) :
    a.Equal b :=
  normalFormModel.below_antisymm ab ba

theorem Equal.below {a b : Term Const Var Hom} (h : a.Equal b) : a.Below b :=
  normalFormModel.equal_below h

theorem equal_iff_below_below (a b : Term Const Var Hom) :
    a.Equal b ↔ a.Below b ∧ b.Below a :=
  normalFormModel.equal_iff_below_below a b

theorem equal_iff_derives (a b : Term Const Var Hom) : a.Equal b ↔ Derives a b :=
  soundness_and_completeness.symm

/-- Universal validity extends to models in any carrier universe. -/
theorem Equal.sound {α : Type x} [ACUIh Hom α]
    (ic : Const → α) (iv : Var → α) {a b : Term Const Var Hom} (h : a.Equal b) :
    a.eval ic iv = b.eval ic iv :=
  (completeness h).sound ic iv

end Term

@[simp] theorem Equation.valid_swap (equation : Equation Const Var Hom) :
    equation.swap.Valid ↔ equation.Valid :=
  Generic.Equation.valid_swap Term.Equal.symm equation

end ACUIhE.ACUIh

namespace ACUIhE.ACUIE

universe u v w x

variable {Const : Type u} {Var : Type v}

/-- With no homomorphism names, the full signature is precisely ACUIE.
The proof uses only local model structures: no arbitrary homomorphisms are
chosen and no algebra-conversion API is introduced. -/
theorem semanticallyEquivalent_iff_toACUIhE (left right : Term Const Var) :
    SemanticallyEquivalent left right ↔
      _root_.ACUIhE.SemanticallyEquivalent (left.toACUIhE (Hom := Empty)) right.toACUIhE := by
  constructor
  · intro h α fullModel ic iv
    let _ : ACUIE α := {
      add := (· + ·)
      zero := 0
      free := fullModel.free
      add_assoc := fullModel.add_assoc
      add_comm := fullModel.add_comm
      add_zero := fullModel.add_zero
      add_idem := fullModel.add_idem
      free_zero := fullModel.free_zero
      free_injective := fullModel.free_injective }
    have eval_eq (term : Term Const Var) :
        (term.toACUIhE (Hom := Empty)).eval ic iv = term.eval ic iv := by
      induction term with
      | zero | const | var => rfl
      | add a b ih₁ ih₂ =>
          simp only [Term.toACUIhE, Term.eval, _root_.ACUIhE.Term.eval, ih₁, ih₂]
      | free body ih => exact congrArg E ih
    rw [eval_eq, eval_eq]
    exact h ic iv
  · intro h α fragmentModel ic iv
    let _ : _root_.ACUIhE.ACUIhE Empty α := {
      add := (· + ·)
      zero := 0
      hom := fun name => nomatch name
      free := fragmentModel.free
      add_assoc := fragmentModel.add_assoc
      add_comm := fragmentModel.add_comm
      add_zero := fragmentModel.add_zero
      add_idem := fragmentModel.add_idem
      hom_add := by intro name; cases name
      hom_zero := by intro name; cases name
      free_zero := fragmentModel.free_zero
      free_injective := fragmentModel.free_injective }
    have eval_eq (term : Term Const Var) :
        (term.toACUIhE (Hom := Empty)).eval ic iv = term.eval ic iv := by
      induction term with
      | zero | const | var => rfl
      | add a b ih₁ ih₂ =>
          simp only [Term.toACUIhE, Term.eval, _root_.ACUIhE.Term.eval, ih₁, ih₂]
      | free body ih => exact congrArg E ih
    exact (eval_eq left).symm.trans ((h ic iv).trans (eval_eq right))

section Algebra

variable {α : Type x} [ACUIE α]

/-- The additive order of any ACUIE algebra, without homomorphisms. -/
@[instance_reducible] def additivePartialOrder : PartialOrder α :=
  _root_.ACUIhE.Below.partialOrder ACUIE.add_assoc ACUIE.add_comm ACUIE.add_idem

theorem zero_below (a : α) : (0 : α) ≤₊ a :=
  (ACUIE.add_comm 0 a).trans (ACUIE.add_zero a)

end Algebra

namespace Term

theorem below_iff_eval_add_eq (left right : Term Const Var) :
    left.Below right ↔
      ∀ {α : Type (max u v)} [ACUIE α]
        (interpretConst : Const → α) (interpretVar : Var → α),
        (Term.add left right).eval interpretConst interpretVar =
          right.eval interpretConst interpretVar := Iff.rfl

theorem below_iff_semanticallyEquivalent (left right : Term Const Var) :
    left.Below right ↔ SemanticallyEquivalent (.add left right) right := Iff.rfl

end Term

namespace Term

/-- The faithful additive interpretation used to transfer the shared relation laws. -/
def normalFormModel :
    Transfer.AdditiveModel (Term Const Var) (Graph Const Var Empty) Term.Equal Term.add :=
  {
    normalize := fun t => Graph.normalize t.toACUIhE
    equal_iff := fun a b => (semanticallyEquivalent_iff_toACUIhE a b).trans
      (Graph.normalize_eq_iff_semanticallyEquivalent _ _).symm
    join := (· + ·)
    map_add := fun _ _ => rfl
    join_assoc := _root_.ACUIhE.ACUIhE.add_assoc (Hom := Empty)
    join_comm := _root_.ACUIhE.ACUIhE.add_comm (Hom := Empty)
    join_idem := _root_.ACUIhE.ACUIhE.add_idem (Hom := Empty) }

theorem Equal.refl (a : Term Const Var) : a.Equal a :=
  normalFormModel.toEqualityModel.refl a

theorem Equal.symm {a b : Term Const Var} (h : a.Equal b) : b.Equal a :=
  normalFormModel.toEqualityModel.symm h

theorem Equal.trans {a b c : Term Const Var} (ab : a.Equal b) (bc : b.Equal c) :
    a.Equal c :=
  normalFormModel.toEqualityModel.trans ab bc

theorem Equal.add_congr {a b c d : Term Const Var} (ab : a.Equal b) (cd : c.Equal d) :
    (Term.add a c).Equal (.add b d) :=
  normalFormModel.add_congr ab cd

theorem Equal.free_congr {a b : Term Const Var} (h : a.Equal b) :
    (Term.free a).Equal (.free b) :=
  normalFormModel.toEqualityModel.unary_congr .free Graph.free (fun _ => rfl) h

theorem Equal.free_inj {a b : Term Const Var} (h : (Term.free a).Equal (.free b)) :
    a.Equal b :=
  normalFormModel.toEqualityModel.unary_inj .free Graph.free (fun _ => rfl)
    Graph.free_injective h

theorem Below.refl (a : Term Const Var) : a.Below a :=
  normalFormModel.below_refl a

theorem Below.trans {a b c : Term Const Var} (ab : a.Below b) (bc : b.Below c) :
    a.Below c :=
  normalFormModel.below_trans ab bc

/-- Antisymmetry gives algebraic equality, not equality of raw syntax. -/
theorem Below.antisymm {a b : Term Const Var} (ab : a.Below b) (ba : b.Below a) :
    a.Equal b :=
  normalFormModel.below_antisymm ab ba

theorem Equal.below {a b : Term Const Var} (h : a.Equal b) : a.Below b :=
  normalFormModel.equal_below h

theorem equal_iff_below_below (a b : Term Const Var) :
    a.Equal b ↔ a.Below b ∧ b.Below a :=
  normalFormModel.equal_iff_below_below a b

end Term

@[simp] theorem Equation.valid_swap (equation : Equation Const Var) :
    equation.swap.Valid ↔ equation.Valid :=
  Generic.Equation.valid_swap Term.Equal.symm equation

end ACUIhE.ACUIE
