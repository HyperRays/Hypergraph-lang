import ACUIhE.ACUIESolver.Elimination
import Mathlib.Data.Finset.Card

/-! # Finite variable support and the elimination termination measure -/

namespace ACUIhE.ACUIE.Term

universe u v w

variable {Const : Type u} {Var : Type v} {Target : Type w} [DecidableEq Var]

def vars : Term Const Var → Finset Var
  | .zero | .const _ => ∅
  | .var v => {v}
  | .add a b => a.vars ∪ b.vars
  | .free a => a.vars

theorem mem_vars (t : Term Const Var) (v : Var) : v ∈ t.vars ↔ t.occurs v = true := by
  induction t <;> simp_all [vars, occurs]

theorem not_mem_vars (t : Term Const Var) (v : Var) : v ∉ t.vars ↔ t.occurs v = false := by
  simp only [mem_vars, Bool.not_eq_true]

theorem vars_substitute_subset [DecidableEq Target]
    (σ : Substitution Const Var Target) (t : Term Const Var) (allowed : Finset Target)
    (h : ∀ v ∈ t.vars, (σ v).vars ⊆ allowed) :
    (t.substitute σ).vars ⊆ allowed := by
  induction t with
  | zero | const => exact Finset.empty_subset _
  | var v => exact h v (Finset.mem_singleton_self v)
  | free a ih => exact ih h
  | add a b ha hb =>
    exact Finset.union_subset
      (ha (fun v hv => h v (Finset.mem_union_left _ hv)))
      (hb (fun v hv => h v (Finset.mem_union_right _ hv)))

end ACUIhE.ACUIE.Term

namespace ACUIhE.ACUIESolver

universe u v w

variable {Const : Type u} {Var : Type v} {Target : Type w} [DecidableEq Var]

def Problem.vars : Problem Const Var → Finset Var
  | [] => ∅
  | q :: rest => q.left.vars ∪ q.right.vars ∪ Problem.vars rest

@[simp] theorem Problem.vars_append (p q : Problem Const Var) :
    Problem.vars (p ++ q) = p.vars ∪ q.vars := by
  induction p with
  | nil => simp [vars]
  | cons a p ih => simp only [vars, List.cons_append, ih, Finset.union_assoc]

theorem Problem.vars_substitute_subset [DecidableEq Target]
    (σ : ACUIE.Substitution Const Var Target) (p : Problem Const Var) (allowed : Finset Target)
    (h : ∀ v ∈ p.vars, (σ v).vars ⊆ allowed) :
    (p.substitute σ).vars ⊆ allowed := by
  induction p with
  | nil => exact Finset.empty_subset _
  | cons q p ih =>
    apply Finset.union_subset
    · apply Finset.union_subset
      · exact q.left.vars_substitute_subset σ allowed
          (fun v hv => h v (Finset.mem_union_left _ (Finset.mem_union_left _ hv)))
      · exact q.right.vars_substitute_subset σ allowed
          (fun v hv => h v (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
    · exact ih (fun v hv => h v (Finset.mem_union_right _ hv))

theorem Binding.candidate_vars (q : ACUIE.Equation Const Var) {x : Var}
    {t : ACUIE.Term Const Var} (h : candidate q = some (x, t)) :
    q.left.vars ∪ q.right.vars = {x} ∪ t.vars := by
  obtain ⟨left, right⟩ := q
  cases left <;> cases right <;> simp only [candidate] at h
  all_goals try contradiction
  all_goals split at h
  all_goals try contradiction
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  all_goals simp [ACUIE.Term.vars, Finset.union_comm]

theorem Binding.find_vars (p : Problem Const Var) {b : Binding Const Var}
    (h : find p = some b) :
    p.vars = {b.name} ∪ b.value.vars ∪ b.remaining.vars := by
  induction p generalizing b with
  | nil => cases h
  | cons q rest ih =>
    cases hc : candidate q with
    | some pair =>
      obtain ⟨x, t⟩ := pair
      have eq := Option.some.inj (by simpa [find, hc] using h)
      subst b
      exact congrArg (· ∪ Problem.vars rest) (candidate_vars q hc)
    | none =>
      cases ht : find rest with
      | none => simp [find, hc, ht] at h
      | some child =>
        have eq := Option.some.inj (by simpa [find, hc, ht] using h)
        subst b
        simp only [Problem.vars, ih ht]
        ext v
        simp only [Finset.mem_union]
        tauto

/-- A selected binding really removes a variable, rather than spending fuel. -/
theorem Binding.elimination_decreases (p : Problem Const Var) {b : Binding Const Var}
    (h : find p = some b) :
    (b.remaining.substitute (ACUIE.Substitution.single b.name b.value)).vars.card <
      p.vars.card := by
  have parts := find_vars p h
  have absent := (find_correct (Target := Var) p h).1
  have subset : (b.remaining.substitute (ACUIE.Substitution.single b.name b.value)).vars ⊆
      p.vars.erase b.name := by
    apply Problem.vars_substitute_subset
    intro v hv
    by_cases eq : v = b.name
    · subst v
      simp only [ACUIE.Substitution.single, ↓reduceIte]
      intro w hw
      apply Finset.mem_erase.mpr
      constructor
      · intro same
        subst w
        exact ((ACUIE.Term.not_mem_vars _ _).mpr absent) hw
      · rw [parts]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hw)
    · simp only [ACUIE.Substitution.single, eq, ↓reduceIte, ACUIE.Term.vars,
        Finset.singleton_subset_iff, Finset.mem_erase]
      refine ⟨eq, ?_⟩
      rw [parts]
      exact Finset.mem_union_right _ hv
  exact lt_of_le_of_lt (Finset.card_le_card subset) (Finset.card_erase_lt_of_mem (by simp [parts]))

theorem reduceZero_vars (t : ACUIE.Term Const Var) : (reduceZero t).vars ⊆ t.vars := by
  induction t with
  | zero | const | var => simp [reduceZero, Problem.vars, ACUIE.Term.vars]
  | add a b ha hb =>
    simpa only [reduceZero, Problem.vars_append, ACUIE.Term.vars] using Finset.union_subset_union ha hb
  | free a ha => exact ha

variable [DecidableEq Const]

theorem reduceEquation_vars (a b : ACUIE.Term Const Var) :
    (reduceEquation a b).vars ⊆ a.vars ∪ b.vars := by
  fun_induction reduceEquation a b
  · assumption
  · simpa only [ACUIE.Term.vars, Finset.empty_union] using reduceZero_vars _
  · simpa only [ACUIE.Term.vars, Finset.union_empty] using reduceZero_vars _
  · exact Finset.empty_subset _
  · simp [Problem.vars]

theorem reduce_vars (p : Problem Const Var) : (reduce p).vars ⊆ p.vars := by
  induction p with
  | nil => exact Finset.empty_subset _
  | cons q p ih =>
    change Problem.vars (reduceEquation q.left q.right ++ reduce p) ⊆ _
    rw [Problem.vars_append]
    exact Finset.union_subset_union (reduceEquation_vars _ _) ih

end ACUIhE.ACUIESolver
