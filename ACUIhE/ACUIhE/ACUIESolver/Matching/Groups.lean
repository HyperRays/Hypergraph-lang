import ACUIhE.ACUIESolver.Matching.Partial
import Mathlib.Data.Finset.Max

/-!
# Descending ordered groups

A branch chooses a whole nonempty group from the remaining positive edges.
Its rank is the number of remaining edges. This removes arbitrary numeric
labels while retaining the strict dependency order needed for reconstruction.
-/

namespace ACUIhE.ACUIESolver.Matching

variable {n : Nat}

def groupRank (r : Finset (Fin n)) : Fin (n + 1) :=
  ⟨r.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ r)⟩

def assignGroup (r b : Finset (Fin n)) (labels : Labels n) : Labels n :=
  fun i => if i ∈ b then groupRank r else labels i

theorem assignGroup_mem (r b : Finset (Fin n)) (labels : Labels n) {i : Fin n} (hi : i ∈ b) :
    assignGroup r b labels i = groupRank r := if_pos hi

theorem assignGroup_not_mem (r b : Finset (Fin n)) (labels : Labels n) {i : Fin n} (hi : i ∉ b) :
    assignGroup r b labels i = labels i := if_neg hi

theorem group_progress {r b : Finset (Fin n)} (hb : b ⊆ r) (hne : b.Nonempty) :
    (r \ b).card < r.card := Finset.card_lt_card (Finset.sdiff_ssubset hb hne)

/-- A canonical completion determines an available next group with exactly the computed rank. -/
theorem next_group {r : Finset (Fin n)} {labels target : Labels n}
    (hc : Completion r labels target) (hcan : CanonicalLabels target) (hr : r.Nonempty) :
    ∃ b, b ⊆ r ∧ b.Nonempty ∧ Completion (r \ b) (assignGroup r b labels) target := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image r target hr
  let b := r.filter (fun j => target j = target i)
  have hb : b ⊆ r := Finset.filter_subset _ _
  have hbi : i ∈ b := by simp only [b, Finset.mem_filter, hi, eq_self, and_self]
  have hrank : target i = groupRank r := by
    have he : Finset.univ.filter (fun j => target j ≠ 0 ∧ target j ≤ target i) = r := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hjz, hjle⟩
        by_contra hj
        have hz : labels j ≠ 0 := by rw [hc.assigned j hj]; exact hjz
        have ht := hc.below i hi j hj hz
        rw [hc.assigned j hj] at ht
        exact not_le_of_gt ht hjle
      · intro hj
        exact ⟨(hc.pending j hj).2, hmax j hj⟩
    have hh := congrFun hcan i
    apply Fin.ext
    have hv := congrArg Fin.val hh
    change (Finset.univ.filter (fun j => target j ≠ 0 ∧ target j ≤ target i)).card =
      (target i).val at hv
    simpa only [he, groupRank] using hv.symm
  refine ⟨b, hb, ⟨i, hbi⟩, ?_⟩
  constructor
  · intro j hj
    obtain ⟨hjr, hjb⟩ := Finset.mem_sdiff.mp hj
    exact ⟨by simp only [assignGroup, if_neg hjb, (hc.pending j hjr).1], (hc.pending j hjr).2⟩
  · intro j hj
    by_cases hjb : j ∈ b
    · rw [assignGroup, if_pos hjb, ← hrank, (Finset.mem_filter.mp hjb).2]
    · have hjr : j ∉ r := fun h => hj (Finset.mem_sdiff.mpr ⟨h, hjb⟩)
      simp only [assignGroup, if_neg hjb, hc.assigned j hjr]
  · intro j hj k hk hkz
    obtain ⟨hjr, hjb⟩ := Finset.mem_sdiff.mp hj
    by_cases hkb : k ∈ b
    · rw [assignGroup, if_pos hkb, ← hrank]
      apply lt_of_le_of_ne (hmax j hjr)
      intro he
      exact hjb (Finset.mem_filter.mpr ⟨hjr, he⟩)
    · have hkr : k ∉ r := fun h => hk (Finset.mem_sdiff.mpr ⟨h, hkb⟩)
      rw [assignGroup, if_neg hkb] at hkz ⊢
      exact hc.below j hjr k hkr hkz

/-- The initial split only chooses which E edges are positive. -/
def positiveSupport (labels : Labels n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => labels i ≠ 0)

theorem initial_completion (target : Labels n) :
    Completion (positiveSupport target) (fun _ => 0) target := by
  constructor
  · intro i hi
    exact ⟨rfl, (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    symm
    simpa only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      using hi
  · intro i hi j hj hz
    exact (hz rfl).elim

/-- Already assigned positive names at or below a given assigned group. -/
def positivePrefix (labels : Labels n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => labels j ≠ 0 ∧ labels j ≤ labels i)

/-- The ranks computed along a search path count groups, rather than arbitrary label slots. -/
structure GroupState (r : Finset (Fin n)) (labels : Labels n) : Prop where
  pendingZero : ∀ i ∈ r, labels i = 0
  aboveRemaining : ∀ i, labels i ≠ 0 → r.card < (labels i).val
  counted : ∀ i, labels i ≠ 0 → (labels i).val = r.card + (positivePrefix labels i).card

theorem initial_groupState (r : Finset (Fin n)) : GroupState r (fun _ => 0) := by
  exact ⟨fun _ _ => rfl, fun _ h => (h rfl).elim, fun _ h => (h rfl).elim⟩

theorem GroupState.assign {r b : Finset (Fin n)} {labels : Labels n}
    (h : GroupState r labels) (hb : b ⊆ r) (hne : b.Nonempty) :
    GroupState (r \ b) (assignGroup r b labels) := by
  have hprogress := group_progress hb hne
  have hcard := Finset.card_sdiff_add_card_eq_card hb
  have hrpos : 0 < r.card := Finset.card_pos.mpr (hne.mono hb)
  have hrankpos : groupRank r ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    change r.card = 0 at this
    omega
  constructor
  · intro i hi
    obtain ⟨hir, hib⟩ := Finset.mem_sdiff.mp hi
    simp only [assignGroup, if_neg hib, h.pendingZero i hir]
  · intro i hi
    by_cases hib : i ∈ b
    · simpa only [assignGroup, if_pos hib, groupRank] using hprogress
    · rw [assignGroup, if_neg hib] at hi ⊢
      exact lt_trans hprogress (h.aboveRemaining i hi)
  · intro i hi
    by_cases hib : i ∈ b
    · have hp : positivePrefix (assignGroup r b labels) i = b := by
        ext j
        simp only [positivePrefix, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [assignGroup_mem r b labels hib]
        by_cases hjb : j ∈ b
        · simp [assignGroup, hjb, hrankpos]
        · rw [assignGroup, if_neg hjb]
          constructor
          · rintro ⟨hjz, hjle⟩
            have hh := h.aboveRemaining j hjz
            change (labels j).val ≤ r.card at hjle
            omega
          · exact fun hj => (hjb hj).elim
      rw [assignGroup, if_pos hib, hp]
      exact hcard.symm
    · have hiz : labels i ≠ 0 := by simpa only [assignGroup, if_neg hib] using hi
      have hp : positivePrefix (assignGroup r b labels) i = b ∪ positivePrefix labels i := by
        ext j
        simp only [positivePrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        rw [assignGroup_not_mem r b labels hib]
        by_cases hjb : j ∈ b
        · have hle : groupRank r ≤ labels i := (h.aboveRemaining i hiz).le
          simp [assignGroup, hjb, hrankpos, hle]
        · simp [assignGroup, hjb]
      have hdis : Disjoint b (positivePrefix labels i) := by
        apply Finset.disjoint_left.mpr
        intro j hjb hjp
        exact (Finset.mem_filter.mp hjp).2.1 (h.pendingZero j (hb hjb))
      rw [assignGroup, if_neg hib, hp, Finset.card_union_of_disjoint hdis]
      have hh := h.counted i hiz
      omega

/-- Every completed path has canonical labels; canonicality is not a runtime filter. -/
theorem GroupState.canonical {labels : Labels n} (h : GroupState ∅ labels) :
    CanonicalLabels labels := by
  funext i
  by_cases hz : labels i = 0
  · exact ((canonicalizeLabels_zero labels i).mpr hz).trans hz.symm
  · apply Fin.ext
    have hh := h.counted i hz
    simpa only [Finset.card_empty, zero_add, canonicalizeLabels, positivePrefix] using hh.symm

end ACUIhE.ACUIESolver.Matching
