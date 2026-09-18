import ACUIhE.ACUIESolver.Problem
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Fin

/-! # Executable finite joins and their ACUIE interpretation -/

namespace ACUIhE.ACUIESolver.Finite

universe u v w
variable {Const : Type u} {Var : Type v} {α : Type w} {n : Nat}

def joinList (f : Fin n → ACUIE.Term Const Var) : List (Fin n) → ACUIE.Term Const Var
  | [] => .zero
  | i :: rest => .add (f i) (joinList f rest)

/-- A fixed finite enumeration, without choice of a Finset representative. -/
def join (f : Fin n → ACUIE.Term Const Var) (s : Finset (Fin n)) : ACUIE.Term Const Var :=
  joinList f ((List.finRange n).filter (fun i => i ∈ s))

theorem join_congr {f g : Fin n → ACUIE.Term Const Var} {s : Finset (Fin n)}
    (h : ∀ i ∈ s, f i = g i) : join f s = join g s := by
  unfold join
  generalize he : (List.finRange n).filter (fun i => i ∈ s) = xs
  have members : ∀ i ∈ xs, i ∈ s := by
    intro i hi
    rw [← he] at hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  clear he
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [joinList, joinList, h i (members i (by simp)), ih (fun j hj => members j (by simp [hj]))]

@[simp] theorem join_empty (f : Fin n → ACUIE.Term Const Var) : join f ∅ = .zero := by
  simp [join, joinList]

section Interpretation
variable [ACUIE α]

@[simp] theorem zero_add (a : α) : 0 + a = a := (ACUIE.add_comm _ _).trans (ACUIE.add_zero _)

local instance : Std.Commutative (fun a b : α => a + b) := ⟨ACUIE.add_comm⟩
local instance : Std.Associative (fun a b : α => a + b) := ⟨ACUIE.add_assoc⟩
local instance : Std.IdempotentOp (fun a b : α => a + b) := ⟨ACUIE.add_idem⟩

def sum (f : Fin n → α) (s : Finset (Fin n)) : α := s.fold (· + ·) 0 f

@[simp] theorem sum_empty (f : Fin n → α) : sum f ∅ = 0 := rfl

@[simp] theorem sum_insert (f : Fin n → α) (i : Fin n) (s : Finset (Fin n)) :
    sum f (insert i s) = f i + sum f s := Finset.fold_insert_idem

@[simp] theorem sum_union (f : Fin n → α) (s t : Finset (Fin n)) :
    sum f (s ∪ t) = sum f s + sum f t := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ ih =>
    rw [Finset.insert_union, sum_insert, sum_insert, ih, ACUIE.add_assoc]

theorem sum_congr {f g : Fin n → α} {s : Finset (Fin n)}
    (h : ∀ i ∈ s, f i = g i) : sum f s = sum g s := Finset.fold_congr h

theorem sum_constant (f : Fin n → α) (s : Finset (Fin n)) (a : α)
    (nonempty : s.Nonempty) (h : ∀ i ∈ s, f i = a) : sum f s = a := by
  rw [sum_congr h]
  unfold sum
  rw [Finset.fold_const]
  · simp [nonempty.ne_empty]
  · simp [ACUIE.add_idem]

theorem eval_joinList (f : Fin n → ACUIE.Term Const Var) (xs : List (Fin n))
    (ic : Const → α) (iv : Var → α) :
    (joinList f xs).eval ic iv = sum (fun i => (f i).eval ic iv) xs.toFinset := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [joinList, ACUIE.Term.eval, List.toFinset_cons, sum_insert, ih]

theorem eval_join (f : Fin n → ACUIE.Term Const Var) (s : Finset (Fin n))
    (ic : Const → α) (iv : Var → α) :
    (join f s).eval ic iv = sum (fun i => (f i).eval ic iv) s := by
  rw [join, eval_joinList]
  congr 1
  ext i
  simp

end Interpretation
end ACUIhE.ACUIESolver.Finite
