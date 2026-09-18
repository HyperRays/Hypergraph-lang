import ACUIhE.ACUIESolver.Elimination

/-!
# A verified incremental ACUIE solver prototype

One step performs exact E/zero simplification and at most one safe variable
elimination. It returns an ordinary substitution together with explicit
residual equations. It is not a complete search procedure and has no failure
answer, fuel limit, guessed correctness field, or output-validation pass.
-/

namespace ACUIhE.ACUIESolver

universe u v w

structure State (Const : Type u) (Var : Type v) where
  substitution : ACUIE.Substitution Const Var Var
  residual : Problem Const Var

variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Var]

def step (p : Problem Const Var) : State Const Var :=
  let simplified := reduce p
  match Binding.find simplified with
  | none => ⟨ACUIE.Substitution.identity, simplified⟩
  | some b =>
      let σ := ACUIE.Substitution.single b.name b.value
      ⟨σ, b.remaining.substitute σ⟩

/-- Every residual unifier reconstructs a genuine original unifier. -/
theorem step_sound (p : Problem Const Var) (τ : ACUIE.Substitution Const Var Target)
    (h : (step p).residual.IsUnifier τ) :
    p.IsUnifier ((step p).substitution.compose τ) := by
  unfold step at h ⊢
  cases hf : Binding.find (reduce p) with
  | none =>
    simp only [hf] at h ⊢
    exact (reduce_isUnifier_iff p τ).mp h
  | some b =>
    simp only [hf] at h ⊢
    obtain ⟨absent, matching⟩ := Binding.find_correct (Target := Target) (reduce p) hf
    apply (reduce_isUnifier_iff p _).mp
    apply (matching _).mpr
    exact (Problem.isUnifier_cons _ _ _).mp (binding_sound b.name b.value b.remaining absent τ h)

/-- No original unifiers are discarded, and their reconstruction is equal
to the original substitution on every variable. -/
theorem step_complete (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target)
    (h : p.IsUnifier σ) :
    (step p).residual.IsUnifier σ ∧
      ∀ v, (((step p).substitution.compose σ) v).Equal (σ v) := by
  have simplified := (reduce_isUnifier_iff p σ).mpr h
  unfold step
  cases hf : Binding.find (reduce p) with
  | none =>
    simp only [hf]
    exact ⟨simplified, fun _ => ACUIE.Term.Equal.refl _⟩
  | some b =>
    simp only [hf]
    obtain ⟨_, matching⟩ := Binding.find_correct (Target := Target) (reduce p) hf
    exact binding_complete b.name b.value b.remaining σ
      ((Problem.isUnifier_cons _ _ _).mpr ((matching σ).mp simplified))

theorem step_unifiable_iff (p : Problem Const Var) :
    (step p).residual.Unifiable ↔ p.Unifiable := by
  constructor
  · rintro ⟨τ, h⟩
    exact ⟨(step p).substitution.compose τ, step_sound p τ h⟩
  · rintro ⟨σ, h⟩
    exact ⟨σ, (step_complete p σ h).1⟩

/-- Empty residuals need no further solving or checking. -/
theorem step_empty_sound (p : Problem Const Var) (empty : (step p).residual = []) :
    p.IsUnifier (step p).substitution := by
  have residual : (step p).residual.IsUnifier ACUIE.Substitution.identity := by
    rw [empty]
    exact Problem.isUnifier_nil _
  have result := step_sound p ACUIE.Substitution.identity residual
  simpa only [ACUIE.Substitution.compose_identity] using result

/-- Neither constructor claims non-unifiability. Residual states retain all
unresolved constraints and the substitution needed to reconstruct solutions. -/
inductive Outcome (Const : Type u) (Var : Type v) where
  | unifier : ACUIE.Substitution Const Var Var → Outcome Const Var
  | residual : State Const Var → Outcome Const Var

def prototype (p : Problem Const Var) : Outcome Const Var :=
  let state := step p
  match state.residual with
  | [] => .unifier state.substitution
  | _ :: _ => .residual state

theorem prototype_unifier_sound (p : Problem Const Var)
    {σ : ACUIE.Substitution Const Var Var} (h : prototype p = .unifier σ) : p.IsUnifier σ := by
  unfold prototype at h
  cases hr : (step p).residual with
  | nil =>
    have eq := Outcome.unifier.inj (by simpa only [hr] using h)
    subst σ
    exact step_empty_sound p hr
  | cons q rest => simp [hr] at h

/-- A residual answer is exactly the proved step, never a replacement goal. -/
theorem prototype_residual_eq (p : Problem Const Var) {state : State Const Var}
    (h : prototype p = .residual state) : state = step p := by
  unfold prototype at h
  cases hr : (step p).residual with
  | nil => simp [hr] at h
  | cons q rest => exact (Outcome.residual.inj (by simpa only [hr] using h)).symm

end ACUIhE.ACUIESolver
