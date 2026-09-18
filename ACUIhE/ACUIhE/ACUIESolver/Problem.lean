import ACUIhE.ACUIESolver.Substitution

/-! # Solver-independent equations and unifiers for ACUIE -/

namespace ACUIhE.ACUIESolver

universe u v w x y

abbrev Problem (Const : Type u) (Var : Type v) := List (ACUIE.Equation Const Var)

namespace Problem

variable {Const : Type u} {Var : Type v} {Target : Type w} {Next : Type x}

def Holds {α : Type y} [ACUIE α] (p : Problem Const Var)
    (ic : Const → α) (iv : Var → α) : Prop := ∀ q ∈ p, q.Holds ic iv

/-- Ordinary substitution-based unification, independent of any solver code. -/
def IsUnifier (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target) : Prop :=
  ∀ q ∈ p, (q.left.substitute σ).Equal (q.right.substitute σ)

def Unifiable (p : Problem Const Var) : Prop :=
  ∃ σ : ACUIE.Substitution Const Var Var, p.IsUnifier σ

def GroundUnifiable (p : Problem Const Var) : Prop :=
  ∃ σ : ACUIE.Substitution Const Var Empty, p.IsUnifier σ

def substitute (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target) :
    Problem Const Target := p.map (fun q => ⟨q.left.substitute σ, q.right.substitute σ⟩)

@[simp] theorem holds_nil {α : Type y} [ACUIE α] (ic : Const → α) (iv : Var → α) :
    Holds ([] : Problem Const Var) ic iv := by simp [Holds]

@[simp] theorem holds_cons {α : Type y} [ACUIE α] (q : ACUIE.Equation Const Var)
    (p : Problem Const Var) (ic : Const → α) (iv : Var → α) :
    Holds (q :: p) ic iv ↔ q.Holds ic iv ∧ p.Holds ic iv := by
  simp only [Holds, List.forall_mem_cons]

@[simp] theorem holds_append {α : Type y} [ACUIE α] (p q : Problem Const Var)
    (ic : Const → α) (iv : Var → α) :
    Holds (p ++ q) ic iv ↔ p.Holds ic iv ∧ q.Holds ic iv := by
  simp only [Holds, List.forall_mem_append]

@[simp] theorem isUnifier_nil (σ : ACUIE.Substitution Const Var Target) :
    IsUnifier ([] : Problem Const Var) σ := by simp [IsUnifier]

@[simp] theorem isUnifier_cons (q : ACUIE.Equation Const Var) (p : Problem Const Var)
    (σ : ACUIE.Substitution Const Var Target) :
    IsUnifier (q :: p) σ ↔
      (q.left.substitute σ).Equal (q.right.substitute σ) ∧ p.IsUnifier σ := by
  simp only [IsUnifier, List.forall_mem_cons]

theorem isUnifier_iff_holds (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target) :
    p.IsUnifier σ ↔ ∀ {α : Type (max u w)} [ACUIE α] (ic : Const → α) (iv : Target → α),
      p.Holds ic (fun v => (σ v).eval ic iv) := by
  constructor
  · intro h α _ ic iv q hq
    exact (ACUIE.Term.eval_substitute σ ic iv q.left).symm.trans
      ((h q hq ic iv).trans (ACUIE.Term.eval_substitute σ ic iv q.right))
  · intro h q hq α _ ic iv
    simp only [ACUIE.Term.eval_substitute]
    exact h ic iv q hq

theorem IsUnifier.congr {p : Problem Const Var} {σ τ : ACUIE.Substitution Const Var Target}
    (h : p.IsUnifier σ) (same : ∀ v, (σ v).Equal (τ v)) : p.IsUnifier τ := by
  intro q hq
  exact ACUIE.Term.Equal.trans (ACUIE.Term.Equal.symm (q.left.substitute_congr σ τ same))
    (ACUIE.Term.Equal.trans (h q hq) (q.right.substitute_congr σ τ same))

theorem IsUnifier.compose {p : Problem Const Var} {σ : ACUIE.Substitution Const Var Target}
    (h : p.IsUnifier σ) (τ : ACUIE.Substitution Const Target Next) :
    p.IsUnifier (σ.compose τ) := by
  intro q hq
  rw [← ACUIE.Term.substitute_compose σ τ q.left, ← ACUIE.Term.substitute_compose σ τ q.right]
  exact ACUIE.Term.Equal.substitute (h q hq) τ

theorem substitute_isUnifier_iff (p : Problem Const Var)
    (σ : ACUIE.Substitution Const Var Target) (τ : ACUIE.Substitution Const Target Next) :
    (p.substitute σ).IsUnifier τ ↔ p.IsUnifier (σ.compose τ) := by
  simp only [substitute, IsUnifier, List.forall_mem_map, ACUIE.Equation.left,
    ACUIE.Equation.right, ACUIE.Term.substitute_compose]

/-- General unifiability and existence of a ground unifier coincide: replace
all remaining variables by zero. The converse just embeds the ground values. -/
theorem unifiable_iff_groundUnifiable (p : Problem Const Var) :
    p.Unifiable ↔ p.GroundUnifiable := by
  constructor
  · rintro ⟨σ, h⟩
    exact ⟨σ.compose (fun _ => .zero), h.compose (fun _ => .zero)⟩
  · rintro ⟨σ, h⟩
    exact ⟨σ.compose (fun v => nomatch v), h.compose (fun v => nomatch v)⟩

/-- The existing graph normal form is an exact semantic bridge, not a
post-hoc validation pass or a replacement definition of unifiability. -/
theorem isUnifier_iff_graph (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target) :
    p.IsUnifier σ ↔ ∀ q ∈ p,
      Graph.normalize ((q.left.substitute σ).toACUIhE (Hom := Empty)) =
        Graph.normalize ((q.right.substitute σ).toACUIhE (Hom := Empty)) := by
  simp only [IsUnifier, ACUIE.Term.equal_iff_normalize_eq]

end Problem

def fromInequalities {Const : Type u} {Var : Type v}
    (qs : List (ACUIE.Inequality Const Var)) : Problem Const Var :=
  qs.map ACUIE.Inequality.toEquation

theorem holds_fromInequalities_iff {Const : Type u} {Var : Type v}
    {α : Type y} [ACUIE α] (qs : List (ACUIE.Inequality Const Var))
    (ic : Const → α) (iv : Var → α) :
    (fromInequalities qs).Holds ic iv ↔ ∀ q ∈ qs, q.Holds ic iv := by
  simp only [fromInequalities, Problem.Holds, List.forall_mem_map, ACUIE.Inequality.holds_toEquation]

end ACUIhE.ACUIESolver
