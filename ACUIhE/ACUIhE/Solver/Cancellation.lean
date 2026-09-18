import ACUIhE.Solver.Problem
import ACUIhE.Graph.Semantics

/-! # Cancellation of exposed free-operator edges

This is equality cancellation, not monotonicity of E. It preserves every
interpretation and hence every substitution, including nonground ones.
No cancellation of homomorphism prefixes is performed.
-/

namespace ACUIhE.Solver.Cancellation

open Graph.Presentation
universe u v w x
variable {Const : Type u} {Var : Type v} {Hom : Type w}

def cancel : Forest Const Var Hom → Forest Const Var Hom →
    Generic.Equation (Forest Const Var Hom)
  | [.edge [] a as], [.edge [] b bs] => cancel (a :: as) (b :: bs)
  | [.edge [] a as], [] => cancel (a :: as) []
  | [], [.edge [] b bs] => cancel [] (b :: bs)
  | left, right => ⟨left, right⟩
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_all only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
  Tree.edge.sizeOf_spec]; omega

variable {α : Type x} [ACUIhE Hom α]

private theorem eval_edge (a : Tree Const Var Hom) (as : Forest Const Var Hom)
    (ic : Const → α) (iv : Var → α) :
    (reify [.edge [] a as]).eval ic iv = E (Hom := Hom) ((reify (a :: as)).eval ic iv) := by
  simp only [reify, Tree.reify, applyWord, Term.eval, ACUIhE.add_zero]

private theorem E_zero_iff (a : α) : E (Hom := Hom) a = 0 ↔ a = 0 := by
  simpa only [E, ACUIhE.free_zero] using
    (E_injective (Hom := Hom) (α := α)).eq_iff (a := a) (b := 0)

theorem cancel_correct (left right : Forest Const Var Hom) (ic : Const → α) (iv : Var → α) :
    (reify (cancel left right).left).eval ic iv = (reify (cancel left right).right).eval ic iv ↔
      (reify left).eval ic iv = (reify right).eval ic iv := by
  fun_induction cancel left right
  · rename_i ih
    exact ih.trans (by rw [eval_edge, eval_edge]; exact E_injective.eq_iff.symm)
  · rename_i ih
    exact ih.trans (by
      rw [eval_edge]
      change _ = 0 ↔ E (Hom := Hom) _ = 0
      exact (E_zero_iff _).symm)
  · rename_i b bs ih
    exact ih.trans (by
      rw [eval_edge]
      change 0 = _ ↔ 0 = E (Hom := Hom) _
      simpa only [eq_comm (a := (0 : α))] using (E_zero_iff
        ((reify (b :: bs)).eval ic iv)).symm)
  · rfl

end ACUIhE.Solver.Cancellation
