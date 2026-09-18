import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.SplitIfs

/-!
# Finite ordered identifications extracted from arbitrary values

Equal values receive equal labels; zero receives zero. Different nonzero values
are ordered by height, with their first occurrence breaking ties. Compressing
this order gives at most as many positive labels as nonzero input occurrences.
This is a completeness construction, not data requested from the caller.
-/

namespace ACUIhE.ACUIESolver.Matching.Order

variable {n : Nat} {α : Type*} [DecidableEq α]

def representative (f : Fin n → α) (i : Fin n) : Fin n :=
  (Finset.univ.filter (fun j => f j = f i)).min' ⟨i, by simp⟩

theorem representative_value (f : Fin n → α) (i : Fin n) : f (representative f i) = f i := by
  have h := Finset.min'_mem (Finset.univ.filter (fun j => f j = f i)) ⟨i, by simp⟩
  exact (Finset.mem_filter.mp h).2

theorem representative_eq_iff (f : Fin n → α) (i j : Fin n) :
    representative f i = representative f j ↔ f i = f j := by
  constructor
  · intro he
    rw [← representative_value f i, ← representative_value f j, he]
  · intro he
    simp only [representative, he]

def score (height : α → Nat) (f : Fin n → α) (i : Fin n) : Nat :=
  height (f i) * (n + 1) + (representative f i).val

theorem score_strict (height : α → Nat) (f : Fin n → α) {i j : Fin n}
    (h : height (f i) < height (f j)) : score height f i < score height f j := by
  have hm' : (height (f i) + 1) * (n + 1) ≤ height (f j) * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) h
  have hi := (representative f i).isLt
  simp only [Nat.add_mul, Nat.one_mul] at hm'
  unfold score
  omega

theorem score_eq_iff (height : α → Nat) (f : Fin n → α) (i j : Fin n) :
    score height f i = score height f j ↔ f i = f j := by
  constructor
  · intro he
    have hh : height (f i) = height (f j) := by
      rcases lt_trichotomy (height (f i)) (height (f j)) with h | h | h
      · exact ((ne_of_lt (score_strict height f h)) he).elim
      · exact h
      · exact ((ne_of_gt (score_strict height f h)) he).elim
    have hr : (representative f i).val = (representative f j).val := by
      apply Nat.add_left_cancel (n := height (f j) * (n + 1))
      simpa only [score, hh] using he
    exact (representative_eq_iff f i j).mp (Fin.ext hr)
  · intro he
    simp only [score, he, (representative_eq_iff f i j).mpr he]

variable [Zero α]

def active (f : Fin n → α) : Finset (Fin n) := Finset.univ.filter (fun j => f j ≠ 0)

def predecessors (height : α → Nat) (f : Fin n → α) (i : Fin n) : Finset (Fin n) :=
  (active f).filter (fun j => score height f j < score height f i)

theorem predecessors_lt (height : α → Nat) (f : Fin n → α) (i : Fin n) (hi : f i ≠ 0) :
    (predecessors height f i).card < (active f).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have mem : i ∈ active f := by simp [active, hi]
  rw [← he] at mem
  simp [predecessors] at mem

def label (height : α → Nat) (f : Fin n → α) (i : Fin n) : Fin (n + 1) :=
  if hi : f i = 0 then 0 else
    ⟨(predecessors height f i).card + 1, by
      have hlt := predecessors_lt height f i hi
      have hb : (active f).card ≤ n := by simpa using Finset.card_le_univ (active f)
      omega⟩

@[simp] theorem label_zero_iff (height : α → Nat) (f : Fin n → α) (i : Fin n) :
    label height f i = 0 ↔ f i = 0 := by
  unfold label
  split_ifs <;> simp_all

theorem label_bound (height : α → Nat) (f : Fin n → α) (i : Fin n) :
    (label height f i).val ≤ (active f).card := by
  unfold label
  split_ifs with hi
  · exact Nat.zero_le _
  · exact predecessors_lt height f i hi

theorem label_strict_score (height : α → Nat) (f : Fin n → α) {i j : Fin n}
    (hi : f i ≠ 0) (hj : f j ≠ 0) (h : score height f i < score height f j) :
    label height f i < label height f j := by
  have hs : predecessors height f i ⊂ predecessors height f j := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro k hk
      simp only [predecessors, Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, lt_trans hk.2 h⟩
    · intro he
      have mem : i ∈ predecessors height f j := by simp [predecessors, active, hi, h]
      rw [← he] at mem
      simp [predecessors] at mem
  have hc := Finset.card_lt_card hs
  simpa only [label, dif_neg hi, dif_neg hj, Fin.mk_lt_mk, Nat.add_lt_add_iff_right] using hc

theorem label_eq_iff (height : α → Nat) (f : Fin n → α) (i j : Fin n) :
    label height f i = label height f j ↔ f i = f j := by
  constructor
  · intro he
    by_cases hi : f i = 0
    · have hj : f j = 0 := (label_zero_iff height f j).mp
        (he.symm.trans ((label_zero_iff height f i).mpr hi))
      exact hi.trans hj.symm
    · have hj : f j ≠ 0 := by
        intro hz
        exact hi ((label_zero_iff height f i).mp (he.trans ((label_zero_iff height f j).mpr hz)))
      rcases lt_trichotomy (score height f i) (score height f j) with h | h | h
      · exact ((ne_of_lt (label_strict_score height f hi hj h)) he).elim
      · exact (score_eq_iff height f i j).mp h
      · exact ((ne_of_gt (label_strict_score height f hj hi h)) he).elim
  · intro he
    have hs := (score_eq_iff height f i j).mpr he
    simp only [label, predecessors, he, hs]

theorem label_strict (height : α → Nat) (f : Fin n → α) {i j : Fin n}
    (hj : f j ≠ 0) (h : height (f i) < height (f j)) :
    label height f i < label height f j := by
  by_cases hi : f i = 0
  · have hz := (label_zero_iff height f i).mpr hi
    have hn : label height f j ≠ 0 := fun hz => hj ((label_zero_iff height f j).mp hz)
    rw [hz]
    exact Fin.pos_iff_ne_zero.mpr hn
  · exact label_strict_score height f hi hj (score_strict height f h)

end ACUIhE.ACUIESolver.Matching.Order
