import ACUIhE.Equation.Generic

/-! # Shared solvedness proofs

Groundness is supplied by each syntax. The common proofs require only the
stated groundness and relation laws, not any particular term constructors.
-/

namespace ACUIhE.Generic

universe u
variable {Expr : Type u}

def Solved (Ground : Expr → Prop) (Rel : Expr → Expr → Prop) (a b : Expr) : Prop :=
  Ground a ∧ Ground b ∧ Rel a b

theorem solved_iff (Ground : Expr → Prop) (Rel : Expr → Expr → Prop) (a b : Expr) :
    Solved Ground Rel a b ↔ Ground a ∧ Ground b ∧ Rel a b := Iff.rfl

theorem Solved.valid {Ground : Expr → Prop} {Rel : Expr → Expr → Prop} {a b : Expr}
    (h : Solved Ground Rel a b) : Rel a b := h.2.2

theorem Solved.symm {Ground : Expr → Prop} {Rel : Expr → Expr → Prop}
    (symm : ∀ {a b}, Rel a b → Rel b a) {a b : Expr} (h : Solved Ground Rel a b) :
    Solved Ground Rel b a := ⟨h.2.1, h.1, symm h.2.2⟩

/-- The only syntactic fact needed to transfer solvedness from an inequality
to its associated equation is that addition is ground exactly when both inputs are. -/
theorem solvedBelow_iff_solved_add {Ground : Expr → Prop} (Equal : Expr → Expr → Prop)
    {add : Expr → Expr → Expr}
    (ground_add : ∀ a b, Ground (add a b) ↔ Ground a ∧ Ground b) (a b : Expr) :
    Solved Ground (fun a b => Equal (add a b) b) a b ↔ Solved Ground Equal (add a b) b := by
  constructor
  · intro h
    exact ⟨(ground_add a b).mpr ⟨h.1, h.2.1⟩, h.2.1, h.2.2⟩
  · intro h
    exact ⟨((ground_add a b).mp h.1).1, h.2.1, h.2.2⟩

def Equation.Solved (Ground : Expr → Prop) (Equal : Expr → Expr → Prop)
    (q : Equation Expr) : Prop := Generic.Solved Ground Equal q.left q.right

def Inequality.Solved (Ground : Expr → Prop) (add : Expr → Expr → Expr)
    (Equal : Expr → Expr → Prop) (q : Inequality Expr) : Prop :=
  Generic.Solved Ground (fun a b => Equal (add a b) b) q.left q.right

@[simp] theorem Equation.solved_iff (Ground : Expr → Prop) (Equal : Expr → Expr → Prop)
    (q : Equation Expr) : q.Solved Ground Equal ↔ Ground q.left ∧ Ground q.right ∧ q.Valid Equal :=
  Iff.rfl

@[simp] theorem Inequality.solved_iff (Ground : Expr → Prop) (add : Expr → Expr → Expr)
    (Equal : Expr → Expr → Prop) (q : Inequality Expr) :
    q.Solved Ground add Equal ↔ Ground q.left ∧ Ground q.right ∧ q.Valid add Equal := Iff.rfl

theorem Equation.Solved.valid {Ground : Expr → Prop} {Equal : Expr → Expr → Prop}
    {q : Equation Expr} (h : q.Solved Ground Equal) : q.Valid Equal := Generic.Solved.valid h

theorem Inequality.Solved.valid {Ground : Expr → Prop} {add : Expr → Expr → Expr}
    {Equal : Expr → Expr → Prop} {q : Inequality Expr} (h : q.Solved Ground add Equal) :
    q.Valid add Equal := Generic.Solved.valid (Rel := fun a b => Equal (add a b) b) h

theorem Equation.solved_swap (Ground : Expr → Prop) {Equal : Expr → Expr → Prop}
    (symm : ∀ {a b}, Equal a b → Equal b a) (q : Equation Expr) :
    q.swap.Solved Ground Equal ↔ q.Solved Ground Equal :=
  ⟨Generic.Solved.symm symm, Generic.Solved.symm symm⟩

theorem Inequality.solved_toEquation {Ground : Expr → Prop} {add : Expr → Expr → Expr}
    (Equal : Expr → Expr → Prop)
    (ground_add : ∀ a b, Ground (add a b) ↔ Ground a ∧ Ground b) (q : Inequality Expr) :
    (q.toEquation add).Solved Ground Equal ↔ q.Solved Ground add Equal :=
  (Generic.solvedBelow_iff_solved_add Equal ground_add q.left q.right).symm

/-- All executable solvedness APIs use this same certified Boolean view. -/
def isSolved (Ground : Expr → Prop) (Rel : Expr → Expr → Prop) (a b : Expr)
    [Decidable (Generic.Solved Ground Rel a b)] : Bool := decide (Generic.Solved Ground Rel a b)

@[simp] theorem isSolved_eq_true (Ground : Expr → Prop) (Rel : Expr → Expr → Prop) (a b : Expr)
    [Decidable (Generic.Solved Ground Rel a b)] :
    isSolved Ground Rel a b = true ↔ Generic.Solved Ground Rel a b := by
  simp only [isSolved, decide_eq_true_eq]

@[simp] theorem isSolved_eq_false (Ground : Expr → Prop) (Rel : Expr → Expr → Prop) (a b : Expr)
    [Decidable (Generic.Solved Ground Rel a b)] :
    isSolved Ground Rel a b = false ↔ ¬ Generic.Solved Ground Rel a b := by
  simp [isSolved]

end ACUIhE.Generic
