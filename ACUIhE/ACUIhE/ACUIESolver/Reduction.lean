import ACUIhE.ACUIESolver.Problem

/-!
# Exact deterministic reductions

These transformations preserve every interpretation, hence every unifier.
They never split `E(a + b)` into `E(a) + E(b)`, cancel shared sum summands,
or reject a cyclic variable occurrence. Unhandled equations remain present.
-/

namespace ACUIhE.ACUIESolver

universe u v w x

namespace Algebra

variable {α : Type x} [ACUIE α]

theorem zero_add (a : α) : 0 + a = a := (ACUIE.add_comm _ _).trans (ACUIE.add_zero _)

theorem add_eq_zero_iff (a b : α) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha : a = 0 := calc
      a = a + 0 := (ACUIE.add_zero a).symm
      _ = a + (a + b) := congrArg (a + ·) h.symm
      _ = a + b := by rw [← ACUIE.add_assoc, ACUIE.add_idem]
      _ = 0 := h
    exact ⟨ha, by simpa only [ha, zero_add] using h⟩
  · rintro ⟨rfl, rfl⟩
    exact ACUIE.add_zero _

end Algebra

variable {Const : Type u} {Var : Type v}

/-- `a + b = 0` requires both children to vanish; `E(a) = 0` requires `a = 0`. -/
def reduceZero : ACUIE.Term Const Var → Problem Const Var
  | .zero => []
  | .const c => [⟨.const c, .zero⟩]
  | .var v => [⟨.var v, .zero⟩]
  | .add a b => reduceZero a ++ reduceZero b
  | .free a => reduceZero a

theorem reduceZero_holds_iff {α : Type x} [ACUIE α] (t : ACUIE.Term Const Var)
    (ic : Const → α) (iv : Var → α) :
    (reduceZero t).Holds ic iv ↔ t.eval ic iv = 0 := by
  induction t with
  | zero => simp [reduceZero, ACUIE.Term.eval]
  | const c | var c =>
    simp [reduceZero, Problem.Holds, ACUIE.Equation.Holds, Generic.Equation.Holds, ACUIE.Term.eval]
  | add a b ha hb =>
    simp only [reduceZero, Problem.holds_append, ha, hb, ACUIE.Term.eval, Algebra.add_eq_zero_iff]
  | free a ha =>
    simpa only [reduceZero, ACUIE.Term.eval, ACUIE.E_eq_zero_iff] using ha

variable [DecidableEq Const] [DecidableEq Var]

/-- Descend through equal outer E constructors and zero equations, otherwise
delete only universally valid equations. All remaining constraints are retained. -/
def reduceEquation : ACUIE.Term Const Var → ACUIE.Term Const Var → Problem Const Var
  | .free a, .free b => reduceEquation a b
  | .zero, b => reduceZero b
  | a, .zero => reduceZero a
  | a, b => if a.Equal b then [] else [⟨a, b⟩]

theorem reduceEquation_holds_iff {α : Type x} [ACUIE α]
    (a b : ACUIE.Term Const Var) (ic : Const → α) (iv : Var → α) :
    (reduceEquation a b).Holds ic iv ↔ a.eval ic iv = b.eval ic iv := by
  fun_induction reduceEquation a b
  · rename_i ih
    exact ih.trans ⟨congrArg (ACUIE.E (α := α)), fun h => ACUIE.E_injective h⟩
  · simpa only [ACUIE.Term.eval, eq_comm] using reduceZero_holds_iff _ ic iv
  · exact reduceZero_holds_iff _ ic iv
  · rename_i valid
    simp only [Problem.holds_nil, true_iff]
    exact valid.sound ic iv
  · simp [Problem.Holds, ACUIE.Equation.Holds, Generic.Equation.Holds]

def reduce (p : Problem Const Var) : Problem Const Var :=
  p.flatMap (fun q => reduceEquation q.left q.right)

/-- Pointwise equivalence: reduction preserves the entire solution set. -/
theorem reduce_holds_iff {α : Type x} [ACUIE α] (p : Problem Const Var)
    (ic : Const → α) (iv : Var → α) : (reduce p).Holds ic iv ↔ p.Holds ic iv := by
  simp only [reduce, Problem.Holds, List.forall_mem_flatMap]
  exact forall_congr' (fun q => forall_congr' (fun _ => reduceEquation_holds_iff q.left q.right ic iv))

theorem reduce_isUnifier_iff {Target : Type w} (p : Problem Const Var)
    (σ : ACUIE.Substitution Const Var Target) : (reduce p).IsUnifier σ ↔ p.IsUnifier σ := by
  simp only [Problem.isUnifier_iff_holds, reduce_holds_iff]

theorem reduce_unifiable_iff (p : Problem Const Var) : (reduce p).Unifiable ↔ p.Unifiable := by
  simp only [Problem.Unifiable, reduce_isUnifier_iff]

end ACUIhE.ACUIESolver
