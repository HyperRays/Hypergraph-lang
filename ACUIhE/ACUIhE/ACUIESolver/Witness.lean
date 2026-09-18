import ACUIhE.ACUIESolver.Search

/-!
# Structural witness construction and explicit search outcomes

An empty residual admits the identity substitution. Any constant-free problem
admits the all-zero substitution, regardless of cyclic occurrences or nesting
of E. Both are proved synthesis rules, not validation of candidate solutions.
Other nonempty residuals remain unresolved, not falsely classified as failures.
-/

namespace ACUIhE.ACUIE.Term

universe u v w
variable {Const : Type u} {Var : Type v} {Target : Type w}

def constantFree : Term Const Var → Bool
  | .zero | .var _ => true
  | .const _ => false
  | .add a b => a.constantFree && b.constantFree
  | .free a => a.constantFree

theorem zero_substitute_of_constantFree (t : Term Const Var) (h : t.constantFree = true) :
    (t.substitute (fun _ => (.zero : Term Const Target))).Equal .zero := by
  intro α _ ic iv
  induction t with
  | zero | var => rfl
  | const c => simp [constantFree] at h
  | add a b ha hb =>
    have parts : a.constantFree = true ∧ b.constantFree = true := by
      simpa only [constantFree, Bool.and_eq_true] using h
    change (a.substitute _).eval ic iv + (b.substitute _).eval ic iv = 0
    simp only [ha parts.1, hb parts.2, eval, ACUIE.add_zero]
  | free a ha =>
    change E ((a.substitute _).eval ic iv) = 0
    simp only [ha h, eval, E_zero]

end ACUIhE.ACUIE.Term

namespace ACUIhE.ACUIESolver

universe u v w
variable {Const : Type u} {Var : Type v} {Target : Type w}

def Problem.constantFree (p : Problem Const Var) : Bool :=
  p.all (fun q => q.left.constantFree && q.right.constantFree)

theorem Problem.zero_isUnifier (p : Problem Const Var) (h : p.constantFree = true) :
    p.IsUnifier (fun _ => (.zero : ACUIE.Term Const Target)) := by
  intro q hq
  have parts : q.left.constantFree = true ∧ q.right.constantFree = true := by
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp h q hq
  apply ACUIE.Term.Equal.trans (b := (.zero : ACUIE.Term Const Target))
  · exact q.left.zero_substitute_of_constantFree parts.1
  · exact ACUIE.Term.Equal.symm (q.right.zero_substitute_of_constantFree parts.2)

namespace Search

def localWitness : Problem Const Var → Option (ACUIE.Substitution Const Var Var)
  | [] => some ACUIE.Substitution.identity
  | q :: rest => if Problem.constantFree (q :: rest) then some (fun _ => .zero) else none

theorem localWitness_sound (p : Problem Const Var) {σ : ACUIE.Substitution Const Var Var}
    (h : localWitness p = some σ) : p.IsUnifier σ := by
  cases p with
  | nil => exact Problem.isUnifier_nil _
  | cons q rest =>
    simp only [localWitness] at h
    split at h
    · rename_i constantFree
      cases Option.some.inj h
      exact Problem.zero_isUnifier _ constantFree
    · contradiction

/-- Choose a structurally constructed witness, without checking a returned substitution. -/
def findWitness : List (State Const Var) → Option (ACUIE.Substitution Const Var Var)
  | [] => none
  | state :: rest =>
    match localWitness state.residual with
    | some τ => some (state.substitution.compose τ)
    | none => findWitness rest

theorem findWitness_sound (states : List (State Const Var)) {σ : ACUIE.Substitution Const Var Var}
    (h : findWitness states = some σ) : ∃ state ∈ states,
      ∃ τ : ACUIE.Substitution Const Var Var, state.residual.IsUnifier τ ∧
        σ = state.substitution.compose τ := by
  induction states with
  | nil => cases h
  | cons state rest ih =>
    cases hw : localWitness state.residual with
    | none =>
      obtain ⟨child, member, τ, hτ, eq⟩ := ih (by simpa only [findWitness, hw] using h)
      exact ⟨child, List.mem_cons_of_mem _ member, τ, hτ, eq⟩
    | some τ =>
      have eq := Option.some.inj (by simpa only [findWitness, hw] using h)
      exact ⟨state, List.mem_cons_self, τ, localWitness_sound _ hw, eq.symm⟩

end Search

/-- Residual answers are explicitly different from proved unsatisfiability. -/
inductive SearchResult (Const : Type u) (Var : Type v) where
  | unifier : ACUIE.Substitution Const Var Var → SearchResult Const Var
  | unsatisfiable : SearchResult Const Var
  | residual : List (State Const Var) → SearchResult Const Var

variable [DecidableEq Const] [DecidableEq Var]

/-- Run symbolic preprocessing and the cheap synthesis rules. This incremental
interface may retain residuals; `solve` finishes them using finite constraints. -/
def preview (p : Problem Const Var) : SearchResult Const Var :=
  let states := search p
  match Search.findWitness states with
  | some σ => .unifier σ
  | none => match states with
    | [] => .unsatisfiable
    | _ :: _ => .residual states

theorem preview_unifier_sound (p : Problem Const Var) {σ : ACUIE.Substitution Const Var Var}
    (h : preview p = .unifier σ) : p.IsUnifier σ := by
  unfold preview at h
  cases hw : Search.findWitness (search p) with
  | some τ =>
    have eq := SearchResult.unifier.inj (by simpa only [hw] using h)
    subst τ
    obtain ⟨state, member, τ, hτ, rfl⟩ := Search.findWitness_sound _ hw
    exact search_sound p member τ hτ
  | none =>
    simp only [hw] at h
    cases hs : search p <;> simp [hs] at h

theorem preview_unsatisfiable_sound (p : Problem Const Var) (h : preview p = .unsatisfiable) :
    ¬ p.Unifiable := by
  unfold preview at h
  cases hw : Search.findWitness (search p) with
  | some τ => simp [hw] at h
  | none =>
    simp only [hw] at h
    cases hs : search p with
    | nil => exact search_empty_unsatisfiable p hs
    | cons state rest => simp [hs] at h

theorem preview_residual_eq (p : Problem Const Var) {states : List (State Const Var)}
    (h : preview p = .residual states) : states = search p ∧ states ≠ [] := by
  unfold preview at h
  cases hw : Search.findWitness (search p) with
  | some τ => simp [hw] at h
  | none =>
    simp only [hw] at h
    cases hs : search p with
    | nil => simp [hs] at h
    | cons state rest =>
      have eq := SearchResult.residual.inj (by simpa only [hs] using h)
      exact ⟨eq.symm, eq ▸ List.cons_ne_nil _ _⟩

theorem preview_residual_complete (p : Problem Const Var) {states : List (State Const Var)}
    (result : preview p = .residual states) (σ : ACUIE.Substitution Const Var Target)
    (h : p.IsUnifier σ) : ∃ state ∈ states, state.residual.IsUnifier σ ∧
      ∀ v, ((state.substitution.compose σ) v).Equal (σ v) := by
  rw [(preview_residual_eq p result).1]
  exact search_complete p σ h

end ACUIhE.ACUIESolver
