import Mathlib.Logic.Basic

/-!
# Representation-independent equation objects

The three fragment APIs specialize these objects and proofs to their own
syntax, equality relation, and interpretation. No operators are invented or
forgotten, and constructing an object does not assert its validity.
-/

namespace ACUIhE.Generic

universe u v

structure Equation (Expr : Type u) where
  left : Expr
  right : Expr

structure Inequality (Expr : Type u) where
  left : Expr
  right : Expr

variable {Expr : Type u} {Value : Type v}

def Equation.Holds (eval : Expr → Value) (q : Equation Expr) : Prop :=
  eval q.left = eval q.right

def Equation.Valid (Equal : Expr → Expr → Prop) (q : Equation Expr) : Prop :=
  Equal q.left q.right

def Inequality.Holds (join : Value → Value → Value) (eval : Expr → Value)
    (q : Inequality Expr) : Prop := join (eval q.left) (eval q.right) = eval q.right

def Inequality.Valid (add : Expr → Expr → Expr) (Equal : Expr → Expr → Prop)
    (q : Inequality Expr) : Prop := Equal (add q.left q.right) q.right

def Inequality.toEquation (add : Expr → Expr → Expr) (q : Inequality Expr) : Equation Expr :=
  ⟨add q.left q.right, q.right⟩

def Equation.swap (q : Equation Expr) : Equation Expr := ⟨q.right, q.left⟩

@[simp] theorem Equation.swap_swap (q : Equation Expr) : q.swap.swap = q := rfl

@[simp] theorem Equation.holds_swap (eval : Expr → Value) (q : Equation Expr) :
    q.swap.Holds eval ↔ q.Holds eval := eq_comm

theorem Equation.valid_swap {Equal : Expr → Expr → Prop}
    (symm : ∀ {a b}, Equal a b → Equal b a) (q : Equation Expr) :
    q.swap.Valid Equal ↔ q.Valid Equal := ⟨symm, symm⟩

@[simp] theorem Inequality.valid_toEquation (add : Expr → Expr → Expr)
    (Equal : Expr → Expr → Prop) (q : Inequality Expr) :
    (q.toEquation add).Valid Equal ↔ q.Valid add Equal := Iff.rfl

theorem Inequality.holds_toEquation {add : Expr → Expr → Expr}
    {join : Value → Value → Value} {eval : Expr → Value}
    (map_add : ∀ a b, eval (add a b) = join (eval a) (eval b)) (q : Inequality Expr) :
    (q.toEquation add).Holds eval ↔ q.Holds join eval := by
  change eval (add q.left q.right) = eval q.right ↔ _
  rw [map_add]
  rfl

theorem Equation.Valid.holds {Equal : Expr → Expr → Prop} {eval : Expr → Value}
    (sound : ∀ {a b}, Equal a b → eval a = eval b)
    {q : Equation Expr} (h : q.Valid Equal) : q.Holds eval := sound h

theorem Inequality.Valid.holds {add : Expr → Expr → Expr} {Equal : Expr → Expr → Prop}
    {join : Value → Value → Value} {eval : Expr → Value}
    (sound : ∀ {a b}, Equal a b → eval a = eval b)
    (map_add : ∀ a b, eval (add a b) = join (eval a) (eval b))
    {q : Inequality Expr} (h : q.Valid add Equal) : q.Holds join eval :=
  (map_add q.left q.right).symm.trans (sound h)

def Equation.isValid (Equal : Expr → Expr → Prop) (q : Equation Expr)
    [Decidable (q.Valid Equal)] : Bool := decide (q.Valid Equal)

def Inequality.isValid (add : Expr → Expr → Expr) (Equal : Expr → Expr → Prop)
    (q : Inequality Expr) [Decidable (q.Valid add Equal)] : Bool := decide (q.Valid add Equal)

@[simp] theorem Equation.isValid_eq_true (Equal : Expr → Expr → Prop) (q : Equation Expr)
    [Decidable (q.Valid Equal)] : q.isValid Equal = true ↔ q.Valid Equal := by
  simp only [isValid, decide_eq_true_eq]

@[simp] theorem Equation.isValid_eq_false (Equal : Expr → Expr → Prop) (q : Equation Expr)
    [Decidable (q.Valid Equal)] : q.isValid Equal = false ↔ ¬ q.Valid Equal := by
  simp [isValid]

@[simp] theorem Inequality.isValid_eq_true (add : Expr → Expr → Expr)
    (Equal : Expr → Expr → Prop) (q : Inequality Expr) [Decidable (q.Valid add Equal)] :
    q.isValid add Equal = true ↔ q.Valid add Equal := by
  simp only [isValid, decide_eq_true_eq]

@[simp] theorem Inequality.isValid_eq_false (add : Expr → Expr → Expr)
    (Equal : Expr → Expr → Prop) (q : Inequality Expr) [Decidable (q.Valid add Equal)] :
    q.isValid add Equal = false ↔ ¬ q.Valid add Equal := by
  simp [isValid]

@[simp] theorem Inequality.isValid_toEquation (add : Expr → Expr → Expr)
    (Equal : Expr → Expr → Prop) (q : Inequality Expr) [Decidable (q.Valid add Equal)]
    [Decidable ((q.toEquation add).Valid Equal)] :
    (q.toEquation add).isValid Equal = q.isValid add Equal := by
  simp only [Equation.isValid, isValid, valid_toEquation]

end ACUIhE.Generic
