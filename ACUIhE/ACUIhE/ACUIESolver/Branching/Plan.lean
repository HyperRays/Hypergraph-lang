import ACUIhE.ACUIESolver.Prototype

/-!
# Finite symbolic search plans

Disjunction means exhaustive alternatives, conjunction means simultaneous
constraints. Leaves use the central equation objects. This is ordinary data,
not a proof-carrying answer or a check of a proposed substitution.
-/

namespace ACUIhE.ACUIESolver

universe u v w

inductive Plan (Const : Type u) (Var : Type v) where
  | accept
  | reject
  | equation : ACUIE.Equation Const Var → Plan Const Var
  | both : Plan Const Var → Plan Const Var → Plan Const Var
  | either : Plan Const Var → Plan Const Var → Plan Const Var

namespace Plan

variable {Const : Type u} {Var : Type v} {Target : Type w}

def Holds (σ : ACUIE.Substitution Const Var Target) : Plan Const Var → Prop
  | .accept => True
  | .reject => False
  | .equation q => (q.left.substitute σ).Equal (q.right.substitute σ)
  | .both a b => a.Holds σ ∧ b.Holds σ
  | .either a b => a.Holds σ ∨ b.Holds σ

/-- Enumerate symbolic branches, never candidate substitutions. -/
def branches : Plan Const Var → List (Problem Const Var)
  | .accept => [[]]
  | .reject => []
  | .equation q => [[q]]
  | .both a b => a.branches.flatMap (fun p => b.branches.map (p ++ ·))
  | .either a b => a.branches ++ b.branches

theorem holds_iff_branch (plan : Plan Const Var) (σ : ACUIE.Substitution Const Var Target) :
    plan.Holds σ ↔ ∃ p ∈ plan.branches, p.IsUnifier σ := by
  induction plan with
  | accept => simp [Holds, branches]
  | reject => simp [Holds, branches]
  | equation q => simp [Holds, branches, Problem.IsUnifier]
  | both a b ha hb =>
    simp only [Holds, ha, hb, branches, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨⟨p, hp, up⟩, ⟨q, hq, uq⟩⟩
      exact ⟨p ++ q, ⟨p, hp, q, hq, rfl⟩, by
        simpa only [Problem.IsUnifier, List.forall_mem_append] using And.intro up uq⟩
    · rintro ⟨r, ⟨p, hp, q, hq, rfl⟩, ur⟩
      have both : p.IsUnifier σ ∧ q.IsUnifier σ := by
        simpa only [Problem.IsUnifier, List.forall_mem_append] using ur
      exact ⟨⟨p, hp, both.1⟩, ⟨q, hq, both.2⟩⟩
  | either a b ha hb =>
    simp only [Holds, ha, hb, branches, List.mem_append]
    constructor
    · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
      · exact ⟨p, Or.inl hp, h⟩
      · exact ⟨p, Or.inr hp, h⟩
    · rintro ⟨p, hp | hp, h⟩
      · exact Or.inl ⟨p, hp, h⟩
      · exact Or.inr ⟨p, hp, h⟩

end Plan

end ACUIhE.ACUIESolver
