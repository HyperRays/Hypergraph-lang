import ACUIhE.FILO.Shortcuts.Support

/-! # FILO's three choices (§4.5)

`classify` is a disjoint classification: NOTHING means nonempty without the
empty word. Completeness uses this exact classification. The implicit
solver's soundness proof uses the pointwise facts proved in `Goal.Implicit`.
Minimal reconstruction can leave an unneeded NOTHING variable empty; we do
not claim that the returned substitution realizes every guess exactly.
-/

namespace ACUIhE.FILO.Choices

open Components ACUIh.Linear

universe v w

inductive Status where
  | top | constant | nothing
  deriving DecidableEq, Repr

abbrev Choice (Var : Type v) (Hom : Type w) := Variable Var Hom → Status

def statuses : List Status := [.top, .constant, .nothing]

@[simp] theorem mem_statuses (k : Status) : k ∈ statuses := by cases k <;> simp [statuses]

variable {Var : Type v} {Hom : Type w} [DecidableEq Hom]

def classify (p : WordPolynomial Hom) : Status :=
  if p.words = ∅ then .top else if [] ∈ p.words then .constant else .nothing

@[simp] theorem classify_top (p : WordPolynomial Hom) : classify p = .top ↔ p.words = ∅ := by
  by_cases hz : p.words = ∅ <;> by_cases hc : [] ∈ p.words <;> simp [classify, hz, hc]

@[simp] theorem classify_constant (p : WordPolynomial Hom) :
    classify p = .constant ↔ [] ∈ p.words := by
  by_cases hz : p.words = ∅ <;> by_cases hc : [] ∈ p.words <;> simp_all [classify]

@[simp] theorem classify_nothing (p : WordPolynomial Hom) :
    classify p = .nothing ↔ p.words ≠ ∅ ∧ [] ∉ p.words := by
  by_cases hz : p.words = ∅ <;> by_cases hc : [] ∈ p.words <;> simp_all [classify]

def ofAssignment (iv : Column Var Hom) : Choice Var Hom := fun x => classify (interpret iv x)

def atomStatus (choice : Choice Var Hom) : Atom Var Hom → Status
  | .const _ => .constant
  | .var x => choice x

variable [DecidableEq Var]

def Classifies (s : System Var Hom) (choice : Choice Var Hom) (iv : Column Var Hom) : Prop :=
  ∀ x ∈ s.names, choice x = classify (interpret iv x)

theorem ofAssignment_classifies (s : System Var Hom) (iv : Column Var Hom) :
    Classifies s (ofAssignment iv) iv := fun _ _ => rfl

/-- The paper's parent/child consistency checks, including the fixed domain
of constant components. Roles outside the input alphabet cannot be active. -/
def ConsistentAt (s : System Var Hom) (choice : Choice Var Hom) : Variable Var Hom → Prop
  | .base _ => True
  | .role r p =>
      (choice p = .top → choice (.role r p) = .top) ∧
      (r ∉ s.roles → choice (.role r p) = .top) ∧
      (match p with | .constant _ => choice (.role r p) = .top | _ => True)
  | .constant p =>
      choice (.constant p) ≠ .nothing ∧
      (choice (.constant p) = .constant ↔ choice p = .constant)

instance (s : System Var Hom) (choice : Choice Var Hom) (x : Variable Var Hom) :
    Decidable (ConsistentAt s choice x) := by
  cases x with
  | base _ => unfold ConsistentAt; infer_instance
  | constant _ => unfold ConsistentAt; infer_instance
  | role r p => cases p <;> unfold ConsistentAt <;> infer_instance

def Consistent (s : System Var Hom) (choice : Choice Var Hom) : Prop :=
  ∀ x ∈ s.names, ConsistentAt s choice x

instance (s : System Var Hom) (choice : Choice Var Hom) : Decidable (Consistent s choice) :=
  inferInstanceAs (Decidable (∀ x ∈ s.names, ConsistentAt s choice x))

theorem consistent_congr (s : System Var Hom) (a b : Choice Var Hom)
    (same : ∀ x ∈ s.names, a x = b x) (hb : Consistent s b) : Consistent s a := by
  intro x hx
  cases x with
  | base v => trivial
  | role r p =>
    simpa only [ConsistentAt, same (.role r p) hx, same p (s.parent_role hx)] using hb _ hx
  | constant p =>
    simpa only [ConsistentAt, same (.constant p) hx, same p (s.parent_constant hx)] using hb _ hx

theorem ofAssignment_consistent (s : System Var Hom) (iv : Column Var Hom)
    (supported : ∀ v, Language.Supported s.roles.toFinset (iv v)) :
    Consistent s (ofAssignment iv) := by
  intro x hx
  cases x with
  | base v => trivial
  | role r p =>
    constructor
    · intro hp
      have hp := (classify_top _).mp hp
      apply (classify_top _).mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro word hw
      have hm := (Language.mem_derivative r (interpret iv p) word).mp hw
      rw [hp] at hm
      exact Finset.notMem_empty _ hm
    · constructor
      · intro absent
        apply (classify_top _).mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro word hw
        exact absent (List.mem_toFinset.mp (interpret_supported _ iv supported p _
          ((Language.mem_derivative r _ word).mp hw) r (by simp)))
      · cases p with
        | base v | role t p => trivial
        | constant p =>
          apply (classify_top _).mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro word hw
          have hm := (Language.mem_derivative r _ word).mp hw
          have impossible := (Language.mem_constantPart _ _).mp hm |>.1
          cases impossible
  | constant p =>
    constructor
    · intro hn
      obtain ⟨nonempty, noConstant⟩ := (classify_nothing _).mp hn
      apply nonempty
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro word hw
      obtain ⟨rfl, _⟩ := (Language.mem_constantPart _ _).mp hw
      exact noConstant hw
    · change classify (Language.constantPart (interpret iv p)) = .constant ↔
        classify (interpret iv p) = .constant
      simp

end ACUIhE.FILO.Choices
