import ACUIhE.ACUIESolver.Reduction

/-!
# Safe variable elimination and reconstruction

The absence check only enables elimination. A failed check never means
non-unifiability: in particular `X = E(X)` must not be rejected.
-/

namespace ACUIhE.ACUIESolver

universe u v w

variable {Const : Type u} {Var : Type v} {Target : Type w} [DecidableEq Var]

theorem binding_sound (x : Var) (value : ACUIE.Term Const Var) (rest : Problem Const Var)
    (absent : value.occurs x = false) (τ : ACUIE.Substitution Const Var Target)
    (h : (rest.substitute (ACUIE.Substitution.single x value)).IsUnifier τ) :
    Problem.IsUnifier (⟨.var x, value⟩ :: rest)
      ((ACUIE.Substitution.single x value).compose τ) := by
  apply (Problem.isUnifier_cons _ _ _).mpr
  constructor
  · have atX : (ACUIE.Substitution.single x value).compose τ x = value.substitute τ := by
      simp [ACUIE.Substitution.compose, ACUIE.Substitution.single]
    change ((ACUIE.Substitution.single x value).compose τ x).Equal _
    rw [atX, ← ACUIE.Term.substitute_compose,
      value.substitute_single_of_not_occurs x value absent]
    exact ACUIE.Term.Equal.refl _
  · exact (Problem.substitute_isUnifier_iff rest _ τ).mp h

/-- Every original unifier solves the residual problem and is recovered up
to the existing algebraic equality, on all variables, not just those in the input. -/
theorem binding_complete (x : Var) (value : ACUIE.Term Const Var) (rest : Problem Const Var)
    (σ : ACUIE.Substitution Const Var Target)
    (h : Problem.IsUnifier (⟨.var x, value⟩ :: rest) σ) :
    (rest.substitute (ACUIE.Substitution.single x value)).IsUnifier σ ∧
      ∀ v, (((ACUIE.Substitution.single x value).compose σ) v).Equal (σ v) := by
  obtain ⟨head, tail⟩ := (Problem.isUnifier_cons _ _ _).mp h
  have same (v : Var) : (((ACUIE.Substitution.single x value).compose σ) v).Equal (σ v) := by
    by_cases eq : v = x
    · subst v
      simp only [ACUIE.Substitution.compose, ACUIE.Substitution.single]
      exact ACUIE.Term.Equal.symm head
    · simp [ACUIE.Substitution.compose, ACUIE.Substitution.single, eq,
        ACUIE.Term.substitute]
  exact ⟨(Problem.substitute_isUnifier_iff rest _ σ).mpr
    (tail.congr (fun v => ACUIE.Term.Equal.symm (same v))), same⟩

namespace Binding

/-- Orient either side when it is a variable with no occurrence in its value. -/
def candidate : ACUIE.Equation Const Var → Option (Var × ACUIE.Term Const Var)
  | ⟨.var x, t⟩ => if t.occurs x = false then some (x, t) else none
  | ⟨t, .var x⟩ => if t.occurs x = false then some (x, t) else none
  | _ => none

theorem candidate_correct (q : ACUIE.Equation Const Var) {x : Var} {t : ACUIE.Term Const Var}
    (h : candidate q = some (x, t)) :
    t.occurs x = false ∧ ∀ σ : ACUIE.Substitution Const Var Target,
      (q.left.substitute σ).Equal (q.right.substitute σ) ↔ (σ x).Equal (t.substitute σ) := by
  obtain ⟨left, right⟩ := q
  cases left <;> cases right <;> simp only [candidate] at h
  all_goals try contradiction
  all_goals split at h
  all_goals try contradiction
  all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  all_goals refine ⟨by assumption, ?_⟩
  all_goals intro σ
  all_goals first | exact Iff.rfl | exact ⟨ACUIE.Term.Equal.symm, ACUIE.Term.Equal.symm⟩

end Binding

/-- Plain selected binding data; correctness is proved for the selector. -/
structure Binding (Const : Type u) (Var : Type v) where
  name : Var
  value : ACUIE.Term Const Var
  remaining : Problem Const Var

namespace Binding

def find : Problem Const Var → Option (Binding Const Var)
  | [] => none
  | q :: rest =>
      match candidate q with
      | some (x, t) => some ⟨x, t, rest⟩
      | none => (find rest).map (fun b => ⟨b.name, b.value, q :: b.remaining⟩)

theorem find_correct (p : Problem Const Var) {b : Binding Const Var}
    (h : find p = some b) : b.value.occurs b.name = false ∧
      ∀ σ : ACUIE.Substitution Const Var Target,
        p.IsUnifier σ ↔ (σ b.name).Equal (b.value.substitute σ) ∧ b.remaining.IsUnifier σ := by
  induction p generalizing b with
  | nil => cases h
  | cons q rest ih =>
    cases hc : candidate q with
    | some pair =>
      obtain ⟨x, t⟩ := pair
      have eq := Option.some.inj (by simpa [find, hc] using h)
      subst b
      obtain ⟨absent, head⟩ := candidate_correct (Target := Target) q hc
      refine ⟨absent, ?_⟩
      intro σ
      exact (Problem.isUnifier_cons q rest σ).trans (and_congr_left (fun _ => head σ))
    | none =>
      cases ht : find rest with
      | none => simp [find, hc, ht] at h
      | some child =>
        have eq := Option.some.inj (by simpa [find, hc, ht] using h)
        subst b
        obtain ⟨absent, tail⟩ := ih ht
        refine ⟨absent, ?_⟩
        intro σ
        simp only [Problem.isUnifier_cons, tail σ]
        tauto

/-- Reconstruction for the actual selected equation, including orientation
and all equations preceding it. -/
theorem sound (p : Problem Const Var) {b : Binding Const Var} (selected : find p = some b)
    (τ : ACUIE.Substitution Const Var Target)
    (h : (b.remaining.substitute (ACUIE.Substitution.single b.name b.value)).IsUnifier τ) :
    p.IsUnifier ((ACUIE.Substitution.single b.name b.value).compose τ) := by
  obtain ⟨absent, matching⟩ := find_correct (Target := Target) p selected
  exact (matching _).mpr ((Problem.isUnifier_cons _ _ _).mp
    (binding_sound b.name b.value b.remaining absent τ h))

theorem complete (p : Problem Const Var) {b : Binding Const Var} (selected : find p = some b)
    (σ : ACUIE.Substitution Const Var Target) (h : p.IsUnifier σ) :
    (b.remaining.substitute (ACUIE.Substitution.single b.name b.value)).IsUnifier σ ∧
      ∀ v, (((ACUIE.Substitution.single b.name b.value).compose σ) v).Equal (σ v) := by
  obtain ⟨_, matching⟩ := find_correct (Target := Target) p selected
  exact binding_complete b.name b.value b.remaining σ
    ((Problem.isUnifier_cons _ _ _).mpr ((matching σ).mp h))

end Binding

end ACUIhE.ACUIESolver
