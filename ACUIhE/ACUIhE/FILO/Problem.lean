import ACUIhE.ACUIhNF.linear.Matrix

/-!
# FILO's input and semantic contract

Inputs are the project's inequality objects, not a second equation language.
`Holds` is deliberately independent of any solver, preprocessing, or check.
The paper's subsumption order is opposite to the project's additive order.
-/

namespace ACUIhE.FILO

open ACUIh

universe u v w x

abbrev Problem (Const : Type u) (Var : Type v) (Hom : Type w) :=
  List (ACUIh.Inequality Const Var Hom)

namespace Problem

variable {Const : Type u} {Var : Type v} {Hom : Type w}

def Holds {α : Type x} [ACUIh Hom α] (p : Problem Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Prop :=
  ∀ q ∈ p, q.Holds ic iv

/-- Solvability in a specified algebra with fixed constants. -/
def Solvable {α : Type x} [ACUIh Hom α] (p : Problem Const Var Hom)
    (ic : Const → α) : Prop := ∃ iv, p.Holds ic iv

/-- Ground substitutions use the existing sparse matrix representation. -/
def IsSolution [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (p : Problem Const Var Hom) (matrix : Linear.GroundMatrix Const Var Hom) : Prop :=
  ∀ q ∈ p, Linear.instantiateNF matrix q.left ⊆ Linear.instantiateNF matrix q.right

def Unifiable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (p : Problem Const Var Hom) : Prop := ∃ matrix, p.IsSolution matrix

/-- Ground normal forms provide the algebra used to interpret substitutions. -/
def constants (c : Const) : NF Const Empty Hom := {([], .const c)}

section Ground

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

local instance : ACUIh Hom (NF Const Empty Hom) := NF.algebra

omit [DecidableEq Var] in
theorem eval_matrix (matrix : Linear.GroundMatrix Const Var Hom)
    (t : ACUIh.Term Const Var Hom) :
    t.eval constants (fun v => (matrix v).toNF) = Linear.instantiateNF matrix t := by
  induction t with
  | zero | const | var => rfl
  | add a b ia ib => exact congrArg₂ (fun a b => a ∪ b) ia ib
  | hom r t ih => exact congrArg (NF.prepend r) ih

theorem holds_iff_isSolution (p : Problem Const Var Hom)
    (matrix : Linear.GroundMatrix Const Var Hom) :
    p.Holds constants (fun v => (matrix v).toNF) ↔ p.IsSolution matrix := by
  unfold Holds IsSolution ACUIh.Inequality.Holds Generic.Inequality.Holds
  simp only [eval_matrix]
  change (∀ q ∈ p, Linear.instantiateNF matrix q.left ∪ Linear.instantiateNF matrix q.right =
    Linear.instantiateNF matrix q.right) ↔ _
  simp only [Finset.union_eq_right]

theorem unifiable_iff_solvable (p : Problem Const Var Hom) :
    p.Unifiable ↔ p.Solvable (constants (Hom := Hom)) := by
  constructor
  · rintro ⟨matrix, solution⟩
    exact ⟨fun v => (matrix v).toNF, (holds_iff_isSolution p matrix).mpr solution⟩
  · rintro ⟨iv, solution⟩
    refine ⟨fun v => Linear.Row.ofNF (iv v), ?_⟩
    apply (holds_iff_isSolution p _).mp
    simpa only [Linear.Row.toNF_ofNF] using solution

theorem isSolution_ofSubstitution_iff (p : Problem Const Var Hom)
    (σ : Var → ACUIh.Term Const Empty Hom) :
    p.IsSolution (Linear.GroundMatrix.ofSubstitution σ) ↔
      ∀ q ∈ p, ACUIh.SolvedBelow (Linear.substituteGround σ q.left)
        (Linear.substituteGround σ q.right) := by
  simp only [IsSolution, Linear.instantiateNF_subset_iff, Linear.solvedBelow_substituteGround_iff]

end Ground

end Problem

/-- Reuse the central equation objects; equality is both additive inequalities. -/
def fromEquations {Const : Type u} {Var : Type v} {Hom : Type w}
    (equations : List (ACUIh.Equation Const Var Hom)) : Problem Const Var Hom :=
  equations.flatMap fun q => [⟨q.left, q.right⟩, ⟨q.right, q.left⟩]

theorem holds_fromEquations_iff {Const : Type u} {Var : Type v} {Hom : Type w}
    {α : Type x} [ACUIh Hom α] (equations : List (ACUIh.Equation Const Var Hom))
    (ic : Const → α) (iv : Var → α) :
    (fromEquations equations).Holds ic iv ↔ ∀ q ∈ equations, q.Holds ic iv := by
  simp only [Problem.Holds, fromEquations, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, forall_exists_index, and_imp]
  constructor
  · intro h q hq
    have forward := h _ q hq (.inl rfl)
    have backward := h _ q hq (.inr rfl)
    change q.left.eval ic iv + q.right.eval ic iv = q.right.eval ic iv at forward
    change q.right.eval ic iv + q.left.eval ic iv = q.left.eval ic iv at backward
    exact (backward.symm.trans (ACUIh.add_comm _ _)).trans forward
  · intro h _ q hq member
    have eq := h q hq
    change q.left.eval ic iv = q.right.eval ic iv at eq
    rcases member with rfl | rfl <;>
      change _ + _ = _ <;> rw [eq] <;> exact ACUIh.add_idem _

end ACUIhE.FILO
