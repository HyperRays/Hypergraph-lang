import ACUIhE.ACUIESolver.Matching.Groups

/-!
# Uniqueness of ordered-group search paths

This proof-only relation describes the structural choices of the executable
search. A final rank assignment has one path, including its initial positive
support. Together with canonical-rank uniqueness, this rules out repeated
numeric encodings of an ordered partition.
-/

namespace ACUIhE.ACUIESolver.Matching

variable {n : Nat}

inductive GroupPath : Finset (Fin n) → Labels n → List (Finset (Fin n)) → Labels n → Prop
  | done (labels : Labels n) : GroupPath ∅ labels [] labels
  | step {r b : Finset (Fin n)} {labels target : Labels n} {rest : List (Finset (Fin n))}
      (subset : b ⊆ r) (nonempty : b.Nonempty)
      (tail : GroupPath (r \ b) (assignGroup r b labels) rest target) :
      GroupPath r labels (b :: rest) target

theorem GroupPath.canonical {r : Finset (Fin n)} {labels target : Labels n}
    {path : List (Finset (Fin n))} (hp : GroupPath r labels path target)
    (state : GroupState r labels) : CanonicalLabels target := by
  induction hp with
  | done => exact state.canonical
  | step hb hne _ ih => exact ih (state.assign hb hne)

theorem GroupPath.completion {r : Finset (Fin n)} {labels target : Labels n}
    {path : List (Finset (Fin n))} (hp : GroupPath r labels path target)
    (state : GroupState r labels) : Completion r labels target := by
  induction hp with
  | done => exact ⟨by simp, by simp, by simp⟩
  | @step r b labels target rest hb hne tail ih =>
    have hc := ih (state.assign hb hne)
    have hrpos : groupRank r ≠ 0 := by
      apply Fin.ne_of_val_ne
      exact Nat.ne_of_gt (Finset.card_pos.mpr (hne.mono hb))
    have hgroup (i : Fin n) (hi : i ∈ b) : target i = groupRank r := by
      rw [← hc.assigned i (by simp [hi]), assignGroup_mem r b labels hi]
    constructor
    · intro i hi
      refine ⟨state.pendingZero i hi, ?_⟩
      by_cases hib : i ∈ b
      · rw [hgroup i hib]; exact hrpos
      · exact (hc.pending i (Finset.mem_sdiff.mpr ⟨hi, hib⟩)).2
    · intro i hi
      have hib : i ∉ b := fun h => hi (hb h)
      simpa only [assignGroup_not_mem r b labels hib] using
        (hc.assigned i (fun h => hi (Finset.mem_sdiff.mp h).1))
    · intro i hi j hj hjz
      have hjb : j ∉ b := fun h => hj (hb h)
      by_cases hib : i ∈ b
      · rw [hgroup i hib]
        exact state.aboveRemaining j hjz
      · simpa only [assignGroup_not_mem r b labels hjb] using
          (hc.below i (Finset.mem_sdiff.mpr ⟨hi, hib⟩) j
            (fun h => hj (Finset.mem_sdiff.mp h).1)
            (by simpa only [assignGroup_not_mem r b labels hjb] using hjz))

/-- The next group is recoverable from any completion of that step. -/
theorem group_recovered {r b : Finset (Fin n)} {labels target : Labels n}
    (hb : b ⊆ r) (hne : b.Nonempty)
    (hc : Completion (r \ b) (assignGroup r b labels) target) :
    b = r.filter (fun i => target i = groupRank r) := by
  obtain ⟨k, hk⟩ := hne
  have hrpos : groupRank r ≠ 0 := by
    apply Fin.ne_of_val_ne
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨k, hb hk⟩)
  ext i
  constructor
  · intro hi
    refine Finset.mem_filter.mpr ⟨hb hi, ?_⟩
    rw [← hc.assigned i (by simp [hi]), assignGroup_mem r b labels hi]
  · intro hi
    obtain ⟨hir, hit⟩ := Finset.mem_filter.mp hi
    by_contra hib
    have ht := hc.below i (Finset.mem_sdiff.mpr ⟨hir, hib⟩) k (by simp [hk])
      (by simpa only [assignGroup_mem r b labels hk] using hrpos)
    rw [assignGroup_mem r b labels hk, hit] at ht
    exact lt_irrefl _ ht

theorem GroupPath.unique {r : Finset (Fin n)} {labels target : Labels n}
    {a b : List (Finset (Fin n))} (ha : GroupPath r labels a target)
    (hb : GroupPath r labels b target) (state : GroupState r labels) : a = b := by
  induction ha generalizing b with
  | done =>
    cases hb with
    | done => rfl
    | step hs hn _ => exact (hn.ne_empty (Finset.subset_empty.mp hs)).elim
  | @step r c labels target rest hc hcne tail ih =>
    cases hb with
    | done => exact (hcne.ne_empty (Finset.subset_empty.mp hc)).elim
    | @step _ d _ _ other hd hdne ht =>
      have he : c = d := (group_recovered hc hcne (tail.completion (state.assign hc hcne))).trans
        (group_recovered hd hdne (ht.completion (state.assign hd hdne))).symm
      subst d
      exact congrArg (List.cons c) (ih ht (state.assign hc hcne))

theorem GroupPath.support {r : Finset (Fin n)} {target : Labels n}
    {path : List (Finset (Fin n))} (hp : GroupPath r (fun _ => 0) path target) :
    r = positiveSupport target := by
  have hc := hp.completion (initial_groupState r)
  ext i
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hi => (hc.pending i hi).2
  · intro hn
    by_contra hi
    exact hn (hc.assigned i hi).symm

/-- The same ordered partition has exactly one support, group path, and numeric encoding. -/
theorem orderedPartition_path_unique {r s : Finset (Fin n)} {a b : List (Finset (Fin n))}
    {left right : Labels n} (ha : GroupPath r (fun _ => 0) a left)
    (hb : GroupPath s (fun _ => 0) b right)
    (hz : ∀ i, left i = 0 ↔ right i = 0)
    (ho : ∀ i j, left i ≤ left j ↔ right i ≤ right j) :
    r = s ∧ a = b ∧ left = right := by
  have he := canonicalLabels_unique (ha.canonical (initial_groupState r))
    (hb.canonical (initial_groupState s)) hz ho
  subst right
  have hs := ha.support.trans hb.support.symm
  subst s
  exact ⟨rfl, ha.unique hb (initial_groupState r), rfl⟩

end ACUIhE.ACUIESolver.Matching
