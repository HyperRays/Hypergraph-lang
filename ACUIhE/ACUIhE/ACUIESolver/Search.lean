import ACUIhE.ACUIESolver.Branching.Correctness
import ACUIhE.ACUIESolver.Branching.Support

/-!
# Terminating symbolic branching and variable elimination

The search explores all constructor alternatives and continues after every
safe binding. Recursive calls strictly reduce finite variable support; no fuel
or guessed depth bound is used. A nonempty residual is not a failure answer.
General variable-containment constraints can still require further solving.
-/

namespace ACUIhE.ACUIESolver

universe u v w

variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Var]

namespace Search

def plan : Problem Const Var → Plan Const Var
  | [] => .accept
  | q :: rest => .both (Branching.compare q.left q.right) (plan rest)

omit [DecidableEq Var] in
theorem plan_correct (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target) :
    (plan p).Holds σ ↔ p.IsUnifier σ := by
  classical
  induction p with
  | nil => simp [plan, Plan.Holds]
  | cons q p ih =>
    simp only [plan, Plan.Holds, ih, Problem.isUnifier_cons, Branching.compare_correct,
      ← Branching.equal_iff_graph]

theorem plan_vars (p : Problem Const Var) : (plan p).vars ⊆ p.vars := by
  induction p with
  | nil => exact Finset.Subset.refl _
  | cons q p ih => exact Finset.union_subset_union (Branching.compare_vars q.left q.right) ih

/-- Constructor alternatives, with universally valid leaves removed. -/
def alternatives (p : Problem Const Var) : List (Problem Const Var) :=
  (plan p).branches.map reduce

theorem alternatives_correct (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target) :
    p.IsUnifier σ ↔ ∃ q ∈ alternatives p, q.IsUnifier σ := by
  rw [← plan_correct, Plan.holds_iff_branch]
  simp only [alternatives, List.mem_map, exists_exists_and_eq_and, reduce_isUnifier_iff]

theorem alternatives_vars (p : Problem Const Var) {q : Problem Const Var}
    (h : q ∈ alternatives p) : q.vars ⊆ p.vars := by
  obtain ⟨branch, member, rfl⟩ := List.mem_map.mp h
  exact (reduce_vars branch).trans ((Plan.branch_vars member).trans (plan_vars p))

def prepend (σ : ACUIE.Substitution Const Var Var) (state : State Const Var) : State Const Var :=
  ⟨σ.compose state.substitution, state.residual⟩

end Search

/-- Exhaustive constructor search with recursively saturated safe bindings.
States retain variable-containment constraints which this stage cannot solve. -/
def search (p : Problem Const Var) : List (State Const Var) :=
  (Search.alternatives p).attach.flatMap fun branch =>
    match selected : Binding.find branch.val with
    | none => [⟨ACUIE.Substitution.identity, branch.val⟩]
    | some b =>
      let σ := ACUIE.Substitution.single b.name b.value
      (search (b.remaining.substitute σ)).map (Search.prepend σ)
termination_by p.vars.card
decreasing_by
  exact lt_of_lt_of_le (Binding.elimination_decreases branch.val selected)
    (Finset.card_le_card (Search.alternatives_vars p branch.property))

/-- Every solution of every returned residual reconstructs an original solution. -/
theorem search_sound (p : Problem Const Var) {state : State Const Var} (member : state ∈ search p)
    (τ : ACUIE.Substitution Const Var Target) (h : state.residual.IsUnifier τ) :
    p.IsUnifier (state.substitution.compose τ) := by
  induction p using (measure (fun p : Problem Const Var => p.vars.card)).wf.induction
    generalizing state
  rename_i p ih
  rw [search] at member
  obtain ⟨⟨q, hq⟩, _, member⟩ := List.mem_flatMap.mp member
  split at member
  next selected =>
    simp only [List.mem_singleton] at member
    subst state
    exact (Search.alternatives_correct p τ).mpr ⟨q, hq, h⟩
  next b selected =>
    obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
    have childSound := ih (b.remaining.substitute (ACUIE.Substitution.single b.name b.value))
      (lt_of_lt_of_le (Binding.elimination_decreases q selected)
        (Finset.card_le_card (Search.alternatives_vars p hq))) childMember h
    apply (Search.alternatives_correct p _).mpr
    refine ⟨q, hq, ?_⟩
    simpa only [Search.prepend, ACUIE.Substitution.compose_assoc] using
      Binding.sound q selected (child.substitution.compose τ) childSound

/-- Every original unifier survives in some returned branch and is recovered
on every variable, not merely on those occurring in the input. -/
theorem search_complete (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target)
    (h : p.IsUnifier σ) : ∃ state ∈ search p, state.residual.IsUnifier σ ∧
      ∀ v, ((state.substitution.compose σ) v).Equal (σ v) := by
  induction p using (measure (fun p : Problem Const Var => p.vars.card)).wf.induction
  rename_i p ih
  obtain ⟨q, hq, uq⟩ := (Search.alternatives_correct p σ).mp h
  cases selected : Binding.find q with
  | none =>
    refine ⟨⟨ACUIE.Substitution.identity, q⟩, ?_, uq, fun _ => ACUIE.Term.Equal.refl _⟩
    rw [search]
    apply List.mem_flatMap.mpr
    refine ⟨⟨q, hq⟩, List.mem_attach _ _, ?_⟩
    split
    · simp
    · rename_i b other
      simp [selected] at other
  | some b =>
    obtain ⟨residualSolution, bindingSame⟩ := Binding.complete q selected σ uq
    obtain ⟨child, childMember, childSolution, childSame⟩ :=
      ih (b.remaining.substitute (ACUIE.Substitution.single b.name b.value))
        (lt_of_lt_of_le (Binding.elimination_decreases q selected)
          (Finset.card_le_card (Search.alternatives_vars p hq))) residualSolution
    refine ⟨Search.prepend (ACUIE.Substitution.single b.name b.value) child, ?_, childSolution, ?_⟩
    · rw [search]
      apply List.mem_flatMap.mpr
      refine ⟨⟨q, hq⟩, List.mem_attach _ _, ?_⟩
      split
      · rename_i other
        simp [selected] at other
      · rename_i b' other
        have same : b' = b := Option.some.inj (other.symm.trans selected)
        subst b'
        exact List.mem_map.mpr ⟨child, childMember, rfl⟩
    · intro v
      change ((((ACUIE.Substitution.single b.name b.value) v).substitute child.substitution).substitute σ).Equal _
      rw [ACUIE.Term.substitute_compose]
      exact ACUIE.Term.Equal.trans
        (((ACUIE.Substitution.single b.name b.value) v).substitute_congr _ _ childSame)
        (bindingSame v)

theorem search_unifiable_iff (p : Problem Const Var) :
    p.Unifiable ↔ ∃ state ∈ search p, state.residual.Unifiable := by
  constructor
  · rintro ⟨σ, h⟩
    obtain ⟨state, member, hs, _⟩ := search_complete p σ h
    exact ⟨state, member, σ, hs⟩
  · rintro ⟨state, member, τ, hτ⟩
    exact ⟨state.substitution.compose τ, search_sound p member τ hτ⟩

theorem search_empty_unsatisfiable (p : Problem Const Var) (h : search p = []) : ¬ p.Unifiable := by
  rw [search_unifiable_iff, h]
  simp

theorem search_unifier_sound (p : Problem Const Var) {state : State Const Var}
    (member : state ∈ search p) (empty : state.residual = []) : p.IsUnifier state.substitution := by
  have h : state.residual.IsUnifier ACUIE.Substitution.identity := by
    rw [empty]
    exact Problem.isUnifier_nil _
  simpa only [ACUIE.Substitution.compose_identity] using search_sound p member ACUIE.Substitution.identity h

end ACUIhE.ACUIESolver
