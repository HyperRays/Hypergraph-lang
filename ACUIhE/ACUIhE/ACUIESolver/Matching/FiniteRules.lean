import ACUIhE.ACUIESolver.Matching.Rules
import ACUIhE.ACUIESolver.Layers.Flat

/-! # Finite-set interpretation of the shared E conditions -/

namespace ACUIhE.ACUIESolver.Matching.FiniteRules

variable {n : Nat}

def expression : Rules.Expr (Layers.Expr n) n → Layers.Expr n
  | .layer e => e
  | .atoms s => Layers.Expr.atoms s

def condition : Rules.Condition (Layers.Expr n) n → Layers.System n
  | .equal a b => Layers.equation (expression a) (expression b)
  | .below a b => [(expression a, expression b)]
  | .supported e allowed => [(e, Layers.Expr.atoms allowed)]

def compile (cs : Rules.System (Layers.Expr n) n) : Layers.System n :=
  cs.flatMap condition

def interpretation (rows : Layers.Rows n) :
    Rules.Interpretation (Layers.Expr n) (Finset (Fin n)) n where
  layer := Layers.Expr.eval rows
  atoms := id
  below := (· ⊆ ·)
  support := id

@[simp] theorem eval_expression (rows : Layers.Rows n) (e : Rules.Expr (Layers.Expr n) n) :
    (expression e).eval rows = e.eval (interpretation rows) := by
  cases e <;> simp [expression, Rules.Expr.eval, interpretation]

theorem condition_exact (rows : Layers.Rows n) (c : Rules.Condition (Layers.Expr n) n) :
    Layers.Holds (condition c) rows ↔ c.Holds (interpretation rows) := by
  cases c with
  | equal a b =>
    simp only [condition, Layers.holds_equation, eval_expression, Rules.Condition.Holds]
  | below a b =>
    change Layers.Holds [(expression a, expression b)] rows ↔
      a.eval (interpretation rows) ⊆ b.eval (interpretation rows)
    simp [Layers.Holds]
  | supported e allowed => simp [condition, Layers.Holds, Rules.Condition.Holds, interpretation]

theorem compile_exact (rows : Layers.Rows n) (cs : Rules.System (Layers.Expr n) n) :
    Layers.Holds (compile cs) rows ↔ Rules.Holds (interpretation rows) cs := by
  simp [compile, Layers.holds_flatMap, condition_exact, Rules.Holds]

@[simp] theorem compile_complete (self child : Layers.Expr n) (children : Fin n → Layers.Expr n)
    (group lower : Finset (Fin n)) :
    compile (Rules.complete self child children group lower) =
      Layers.equation self (Layers.Expr.atoms group) ++
      (if group = ∅ then Layers.equation child (Layers.Expr.atoms ∅) else []) ++
      ((List.finRange n).filter (fun j => j ∈ group)).flatMap
        (fun j => Layers.equation (children j) child) ++
      [(child, Layers.Expr.atoms lower)] := by
  by_cases empty : group = ∅ <;>
    simp [compile, Rules.complete, condition, expression, empty, List.flatMap_append,
      List.flatMap_map]

@[simp] theorem compile_pending (self child : Layers.Expr n)
    (remaining : Finset (Fin n)) (i : Fin n) :
    compile (Rules.pending self child remaining i) =
      [(Layers.Expr.atoms {i}, self), (self, Layers.Expr.atoms remaining),
       (child, Layers.Expr.atoms (Finset.univ.erase i))] := rfl

end ACUIhE.ACUIESolver.Matching.FiniteRules
