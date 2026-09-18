import ACUIhE.Graph.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-! # A finite ranking extracted from canonical E dependencies -/

namespace ACUIhE.ACUIESolver.Finite

universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

private def heightAlgebra : Graph.FoldAlgebra Const Var Hom Nat where
  atom := fun _ _ => 0
  edge := fun _ _ height => height + 1
  layer := fun entries values => entries.attach.sup values

def height (g : Graph Const Var Hom) : Nat := Graph.fold heightAlgebra g

theorem height_child {a b : Graph Const Var Hom} (h : Graph.Child a b) : height a < height b := by
  obtain ⟨word, nonzero, member⟩ := h
  have bound : height a + 1 ≤ height b := by
    unfold height
    rw [Graph.fold_eq heightAlgebra b]
    exact Finset.le_sup (f := fun s => heightAlgebra.summand b
      (fun child _ => Graph.fold heightAlgebra child) s.val s.property)
      (Finset.mem_attach _ ⟨(word, .inr ⟨a, nonzero⟩), member⟩)
  omega

@[simp] theorem height_zero : height (0 : Graph Const Var Hom) = 0 := by
  simp [height, heightAlgebra]

/-- Compress any finite family of natural heights to a bounded ranking. -/
def compressedRank {n : Nat} (score : Fin n → Nat) (i : Fin n) : Fin (n + 1) :=
  ⟨(Finset.univ.filter (fun j => score j < score i)).card,
    Nat.lt_succ_of_le (by
      have bound := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun j => score j < score i)
      simpa using bound)⟩

theorem compressedRank_strict {n : Nat} (score : Fin n → Nat) {i j : Fin n}
    (h : score i < score j) : compressedRank score i < compressedRank score j := by
  change (Finset.univ.filter (fun k => score k < score i)).card <
    (Finset.univ.filter (fun k => score k < score j)).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_trans hk h
  · intro eq
    have hi : i ∈ Finset.univ.filter (fun k => score k < score j) := by simp [h]
    rw [← eq] at hi
    simp at hi

end ACUIhE.ACUIESolver.Finite
