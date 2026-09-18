import ACUIhE.ACUIESolver.Witness
import ACUIhE.ACUIESolver.Finite.Search
import ACUIhE.ACUIESolver.Matching.FirstSome

/-!
# Complete, verified ACUIE unifiability solver

The public solver directly runs ordered E-matching with complete Horn layer
propagation and cached reconstruction. It does not invoke symbolic preview,
row enumeration, or a fallback. Results contain ordinary substitutions or an
unsatisfiability answer; correctness is established by theorems, not validation.
-/

namespace ACUIhE.ACUIESolver

universe u v
variable {Const : Type u} {Var : Type v} [DecidableEq Const] [DecidableEq Var]

namespace Search

/-- Finish residual branches and compose their witnesses with preprocessing. -/
def completeWitness (states : List (State Const Var)) : Option (ACUIE.Substitution Const Var Var) :=
  Matching.firstSome states (fun state =>
    (Matching.unify state.residual).map state.substitution.compose)

theorem completeWitness_sound (states : List (State Const Var))
    {σ : ACUIE.Substitution Const Var Var} (h : completeWitness states = some σ) :
    ∃ state ∈ states, ∃ τ : ACUIE.Substitution Const Var Var,
      state.residual.IsUnifier τ ∧ σ = state.substitution.compose τ := by
  obtain ⟨state, member, success⟩ := Matching.firstSome_sound _ _ h
  obtain ⟨τ, hτ, eq⟩ := Option.map_eq_some_iff.mp success
  exact ⟨state, member, τ, Matching.unify_sound _ hτ, eq.symm⟩

theorem completeWitness_none_iff (states : List (State Const Var)) :
    completeWitness states = none ↔ ∀ state ∈ states, ¬ state.residual.Unifiable := by
  simp only [completeWitness, Matching.firstSome_none_iff, Option.map_eq_none_iff, Matching.unify_none_iff]

end Search

/-- Plain results of the complete solver. There is no unresolved outcome. -/
inductive Result (Const : Type u) (Var : Type v) where
  | unifier : ACUIE.Substitution Const Var Var → Result Const Var
  | unsatisfiable : Result Const Var

/-- Decide arbitrary finite ACUIE problems directly by ordered E-matching. -/
def solve (p : Problem Const Var) : Result Const Var :=
  match Matching.unify p with
  | some σ => .unifier σ
  | none => .unsatisfiable

theorem solve_unifier_sound (p : Problem Const Var) {σ : ACUIE.Substitution Const Var Var}
    (h : solve p = .unifier σ) : p.IsUnifier σ := by
  unfold solve at h
  cases hm : Matching.unify p with
  | none => simp [hm] at h
  | some τ =>
    have he : τ = σ := Result.unifier.inj (by simpa only [hm] using h)
    subst τ
    exact Matching.unify_sound p hm

theorem solve_unsatisfiable_sound (p : Problem Const Var) (h : solve p = .unsatisfiable) :
    ¬ p.Unifiable := by
  unfold solve at h
  cases hm : Matching.unify p with
  | none => exact (Matching.unify_none_iff p).mp hm
  | some σ => simp [hm] at h

/-- Every unifiable input returns a unifier, with no residual or unknown result. -/
theorem solve_complete (p : Problem Const Var) (h : p.Unifiable) :
    ∃ σ, solve p = .unifier σ := by
  cases hs : solve p with
  | unifier σ => exact ⟨σ, rfl⟩
  | unsatisfiable => exact False.elim (solve_unsatisfiable_sound p hs h)

theorem solve_unifiable_iff (p : Problem Const Var) :
    p.Unifiable ↔ ∃ σ, solve p = .unifier σ :=
  ⟨solve_complete p, fun ⟨σ, hσ⟩ => ⟨σ, solve_unifier_sound p hσ⟩⟩

theorem solve_unsatisfiable_iff (p : Problem Const Var) :
    solve p = .unsatisfiable ↔ ¬ p.Unifiable := by
  refine ⟨solve_unsatisfiable_sound p, ?_⟩
  intro h
  cases hs : solve p with
  | unsatisfiable => rfl
  | unifier σ => exact False.elim (h ⟨σ, solve_unifier_sound p hs⟩)

/-- Computable decidability for the original, solver-independent predicate. -/
instance Problem.decidableUnifiable (p : Problem Const Var) : Decidable p.Unifiable :=
  match h : solve p with
  | .unifier σ => isTrue ⟨σ, solve_unifier_sound p h⟩
  | .unsatisfiable => isFalse (solve_unsatisfiable_sound p h)

def isUnifiable (p : Problem Const Var) : Bool := decide p.Unifiable

@[simp] theorem isUnifiable_eq_true (p : Problem Const Var) :
    isUnifiable p = true ↔ p.Unifiable := by simp [isUnifiable]

@[simp] theorem isUnifiable_eq_false (p : Problem Const Var) :
    isUnifiable p = false ↔ ¬ p.Unifiable := by simp [isUnifiable]

end ACUIhE.ACUIESolver
