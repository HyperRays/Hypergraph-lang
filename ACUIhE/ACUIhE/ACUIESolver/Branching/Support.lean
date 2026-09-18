import ACUIhE.ACUIESolver.Branching.Compile
import ACUIhE.ACUIESolver.Support

/-! # Branching introduces no new variables -/

namespace ACUIhE.ACUIESolver

universe u v
variable {Const : Type u} {Var : Type v} [DecidableEq Var]

def Plan.vars : Plan Const Var → Finset Var
  | .accept | .reject => ∅
  | .equation q => q.left.vars ∪ q.right.vars
  | .both a b | .either a b => a.vars ∪ b.vars

theorem Plan.branch_vars {plan : Plan Const Var} {p : Problem Const Var}
    (h : p ∈ plan.branches) : p.vars ⊆ plan.vars := by
  induction plan generalizing p with
  | accept =>
    have eq : p = [] := by simpa [branches] using h
    subst p
    exact Finset.empty_subset _
  | reject => simp [branches] at h
  | equation q =>
    have eq : p = [q] := by simpa [branches] using h
    subst p
    simp [Problem.vars, vars]
  | both a b ha hb =>
    obtain ⟨pa, hpa, hp⟩ := List.mem_flatMap.mp h
    obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hp
    rw [Problem.vars_append]
    exact Finset.union_subset_union (ha hpa) (hb hpb)
  | either a b ha hb =>
    rcases List.mem_append.mp h with h | h
    · exact (ha h).trans (Finset.subset_union_left)
    · exact (hb h).trans (Finset.subset_union_right)

namespace Branching

theorem vanish_vars (t : ACUIE.Term Const Var) : (vanish t).vars ⊆ t.vars := by
  induction t with
  | zero | const | var => simp [vanish, Plan.vars, ACUIE.Term.vars]
  | add a b ha hb => exact Finset.union_subset_union ha hb
  | free a ha => exact ha

variable [DecidableEq Const]

theorem locateConstant_vars (c : Const) (t : ACUIE.Term Const Var) :
    (locateConstant c t).vars ⊆ t.vars := by
  induction t with
  | zero | free => exact Finset.empty_subset _
  | const d => by_cases h : c = d <;> simp [locateConstant, h, Plan.vars]
  | var v => simp [locateConstant, Plan.vars, ACUIE.Term.vars]
  | add a b ha hb => exact Finset.union_subset_union ha hb

private theorem union_bounds {a b left right : Finset Var}
    (ha : a ⊆ left ∪ right) (hb : b ⊆ right ∪ left) : a ∪ b ⊆ left ∪ right :=
  Finset.union_subset ha (by simpa only [Finset.union_comm] using hb)

mutual
  theorem compare_vars (a b : ACUIE.Term Const Var) :
      (compare a b).vars ⊆ a.vars ∪ b.vars := by
    cases a <;> cases b
    all_goals rw [compare]
    all_goals try solve | simp
    all_goals try solve
      | simp only [ACUIE.Term.vars, Finset.empty_union, Finset.union_empty]
        apply vanish_vars
    all_goals try solve | simp [Plan.vars]
    case const.const c d => by_cases h : c = d <;> simp [h, Plan.vars]
    case free.free a b => exact compare_vars a b
    all_goals exact union_bounds (cover_vars _ _) (cover_vars _ _)
  termination_by (nodes a + nodes b, 2)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega

  theorem cover_vars (a b : ACUIE.Term Const Var) :
      (cover a b).vars ⊆ a.vars ∪ b.vars := by
    cases a with
    | zero => rw [cover]; exact Finset.empty_subset _
    | var v => simp [cover, Plan.vars, ACUIE.Term.vars]
    | const c => simpa only [cover, ACUIE.Term.vars, Finset.empty_union] using locateConstant_vars c b
    | add a c =>
      rw [cover]
      apply Finset.union_subset
      · intro v hv
        have := (cover_vars a b) hv
        simp only [ACUIE.Term.vars, Finset.mem_union] at this ⊢
        tauto
      · intro v hv
        have := (cover_vars c b) hv
        simp only [ACUIE.Term.vars, Finset.mem_union] at this ⊢
        tauto
    | free a =>
      rw [cover]
      exact Finset.union_subset ((vanish_vars a).trans Finset.subset_union_left) (locateFree_vars a b)
  termination_by (nodes a + nodes b, 1)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega

  theorem locateFree_vars (a b : ACUIE.Term Const Var) :
      (locateFree a b).vars ⊆ a.vars ∪ b.vars := by
    cases b with
    | zero | const => rw [locateFree]; exact Finset.empty_subset _
    | var v => simp [locateFree, Plan.vars, ACUIE.Term.vars]
    | add b c =>
      rw [locateFree]
      apply Finset.union_subset
      · intro v hv
        have := (locateFree_vars a b) hv
        simp only [ACUIE.Term.vars, Finset.mem_union] at this ⊢
        tauto
      · intro v hv
        have := (locateFree_vars a c) hv
        simp only [ACUIE.Term.vars, Finset.mem_union] at this ⊢
        tauto
    | free b => rw [locateFree]; exact compare_vars a b
  termination_by (nodes a + 1 + nodes b, 0)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega
end

end Branching
end ACUIhE.ACUIESolver
