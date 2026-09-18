import Mathlib.Data.Fintype.Fin
import Init.Data.Vector.OfFn

/-! # Cached reconstruction along finite strict dependencies -/

namespace ACUIhE.ACUIESolver.Matching.Iteration

universe u
variable {Value : Type u} {n : Nat}

/-- One cached vector per round. Every entry reads the previous vector. -/
def run (initial : Fin n → Value) (step : (Fin n → Value) → Fin n → Value) :
    Nat → Vector Value n
  | 0 => Vector.ofFn initial
  | k + 1 =>
    let previous := run initial step k
    Vector.ofFn (step (fun i => previous[i.val]))

@[simp] theorem run_zero (initial : Fin n → Value)
    (step : (Fin n → Value) → Fin n → Value) (i : Fin n) :
    (run initial step 0)[i.val] = initial i := by simp [run]

theorem run_succ (initial : Fin n → Value)
    (step : (Fin n → Value) → Fin n → Value) (k : Nat) (i : Fin n) :
    (run initial step (k + 1))[i.val] = step (fun j => (run initial step k)[j.val]) i := by
  simp [run]

/-- After a node's rank has been passed, further rounds do not change it.
This is a derived finite bound, not a user-supplied depth or search fuel. -/
theorem stable (initial : Fin n → Value) (step : (Fin n → Value) → Fin n → Value)
    (rank : Fin n → Fin (n + 1))
    (depends : ∀ a b i, (∀ j, rank j < rank i → a j = b j) → step a i = step b i)
    (k : Nat) (i : Fin n) (bound : (rank i).val < k) :
    (run initial step (k + 1))[i.val] = (run initial step k)[i.val] := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [run_succ, run_succ]
    apply depends
    intro j lower
    apply ih
    have strict : (rank j).val < (rank i).val := lower
    omega

theorem fixed (initial : Fin n → Value) (step : (Fin n → Value) → Fin n → Value)
    (rank : Fin n → Fin (n + 1))
    (depends : ∀ a b i, (∀ j, rank j < rank i → a j = b j) → step a i = step b i)
    (i : Fin n) :
    (run initial step (n + 1))[i.val] =
      step (fun j => (run initial step (n + 1))[j.val]) i := by
  exact (stable initial step rank depends (n + 1) i (rank i).isLt).symm.trans
    (run_succ initial step (n + 1) i)

end ACUIhE.ACUIESolver.Matching.Iteration
