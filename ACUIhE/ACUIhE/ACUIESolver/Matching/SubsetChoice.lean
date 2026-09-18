import Mathlib.Data.Finset.Sort

/-!
# Streaming subset choices

The continuation is called depth first, without constructing a powerset. The
subset proof is internal and erased: it certifies a structural choice, never
the correctness of a proposed solution.
-/

namespace ACUIhE.ACUIESolver.Matching

variable {α β : Type*} [DecidableEq α]

def chooseSubsets : (xs : List α) →
    ((s : Finset α) → s ⊆ xs.toFinset → Option β) → Option β
  | [], accept => accept ∅ (by simp)
  | a :: xs, accept => chooseSubsets xs fun s hs =>
      (accept s (by simpa only [List.toFinset_cons] using
        (hs.trans (Finset.subset_insert a xs.toFinset)))).orElse fun _ =>
      accept (insert a s) (by simpa only [List.toFinset_cons] using
        (Finset.insert_subset_insert a hs))

theorem chooseSubsets_none_iff (xs : List α)
    (accept : (s : Finset α) → s ⊆ xs.toFinset → Option β) :
    chooseSubsets xs accept = none ↔ ∀ s hs, accept s hs = none := by
  induction xs with
  | nil =>
    simp only [chooseSubsets]
    constructor
    · intro h s hs
      have : s = ∅ := Finset.subset_empty.mp hs
      subst s
      exact h
    · intro h
      exact h ∅ (by simp)
  | cons a xs ih =>
    rw [chooseSubsets, ih]
    constructor
    · intro h s hs
      have he : s.erase a ⊆ xs.toFinset := by
        intro i hi
        have hi' := hs (Finset.mem_of_mem_erase hi)
        simpa only [List.toFinset_cons, Finset.mem_insert,
          (Finset.mem_erase.mp hi).1, false_or] using hi'
      have hh := h (s.erase a) he
      cases ha : accept (s.erase a) (by simpa only [List.toFinset_cons] using
          (he.trans (Finset.subset_insert a xs.toFinset))) with
      | some b => simp only [ha, Option.orElse_some] at hh; contradiction
      | none =>
        simp only [ha, Option.orElse_none] at hh
        by_cases has : a ∈ s
        · simpa only [Finset.insert_erase has] using hh
        · simpa only [Finset.erase_eq_of_notMem has] using ha
    · intro h s hs
      simp only [h, Option.orElse_none]

theorem chooseSubsets_sound (xs : List α)
    (accept : (s : Finset α) → s ⊆ xs.toFinset → Option β) {b : β}
    (h : chooseSubsets xs accept = some b) : ∃ s hs, accept s hs = some b := by
  induction xs with
  | nil => exact ⟨∅, by simp, h⟩
  | cons a xs ih =>
    obtain ⟨s, hs, hh⟩ := ih _ h
    cases ha : accept s (by simpa only [List.toFinset_cons] using
        (hs.trans (Finset.subset_insert a xs.toFinset))) with
    | some c =>
      simp only [ha, Option.orElse_some, Option.some.injEq] at hh
      subst c
      exact ⟨s, _, ha⟩
    | none =>
      simp only [ha, Option.orElse_none] at hh
      exact ⟨insert a s, _, hh⟩

def chooseSubset {n : Nat} (r : Finset (Fin n))
    (accept : (s : Finset (Fin n)) → s ⊆ r → Option β) : Option β :=
  chooseSubsets (r.sort (· ≤ ·)) fun s hs =>
    accept s (by simpa only [Finset.sort_toFinset] using hs)

theorem chooseSubset_none_iff {n : Nat} (r : Finset (Fin n))
    (accept : (s : Finset (Fin n)) → s ⊆ r → Option β) :
    chooseSubset r accept = none ↔ ∀ s hs, accept s hs = none := by
  unfold chooseSubset
  rw [chooseSubsets_none_iff]
  simp only [Finset.sort_toFinset]

theorem chooseSubset_sound {n : Nat} (r : Finset (Fin n))
    (accept : (s : Finset (Fin n)) → s ⊆ r → Option β) {b : β}
    (h : chooseSubset r accept = some b) : ∃ s hs, accept s hs = some b := by
  obtain ⟨s, hs, hh⟩ := chooseSubsets_sound _ _ h
  exact ⟨s, _, hh⟩

/-- At each choice there is exactly one include/exclude decomposition. -/
theorem subset_choice_unique {a : α} {r s : Finset α} (ha : a ∉ r) (hs : s ⊆ insert a r) :
    ∃! choice : Bool × Finset α,
      choice.2 ⊆ r ∧ s = if choice.1 then insert a choice.2 else choice.2 := by
  refine ⟨(decide (a ∈ s), s.erase a), ?_, ?_⟩
  · constructor
    · intro i hi
      have hm := hs (Finset.mem_of_mem_erase hi)
      simpa only [Finset.mem_insert, (Finset.mem_erase.mp hi).1, false_or] using hm
    · by_cases h : a ∈ s <;> simp [h]
  · rintro ⟨b, t⟩ ⟨ht, he⟩
    have hat : a ∉ t := fun h => ha (ht h)
    cases b <;> simp_all

end ACUIhE.ACUIESolver.Matching
