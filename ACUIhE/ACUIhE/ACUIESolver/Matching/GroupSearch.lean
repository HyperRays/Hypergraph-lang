import ACUIhE.ACUIESolver.Matching.GroupPaths
import ACUIhE.ACUIESolver.Matching.SubsetChoice

/-!
# Pruned traversal of ordered E groups

A layer decision procedure is called at every partial matching, before
selecting another group. Completed states reuse that call's result. The
traversal lemmas take soundness and preservation of completions as explicit
mathematical hypotheses; the concrete solvers prove these from the E rules.
-/

namespace ACUIhE.ACUIESolver.Matching.GroupSearch

universe u
variable {n : Nat} {Row : Type u}

abbrev LayerSolver (n : Nat) (Row : Type u) :=
  Finset (Fin n) → Labels n → Option Row

/-- The one recursive ordered-group traversal, with propagation at every state. -/
def run (solve : LayerSolver n Row) (remaining : Finset (Fin n)) (labels : Labels n) :
    Option (Labels n × Row) :=
  match solve remaining labels with
  | none => none
  | some rows =>
    if remaining = ∅ then some (labels, rows)
    else chooseSubset remaining fun chosen _hsub =>
      if _hne : chosen.Nonempty then
        run solve (remaining \ chosen) (assignGroup remaining chosen labels)
      else none
termination_by remaining.card
decreasing_by exact group_progress _hsub _hne

/-- A successful result is the actual accepted leaf, together with its path. -/
theorem run_leaf_path (solve : LayerSolver n Row) (remaining : Finset (Fin n))
    (labels : Labels n) {result : Labels n × Row}
    (h : run solve remaining labels = some result) :
    solve ∅ result.1 = some result.2 ∧
      ∃ path, GroupPath remaining labels path result.1 := by
  rw [run] at h
  cases hs : solve remaining labels with
  | none => simp only [hs] at h; contradiction
  | some rows =>
    simp only [hs] at h
    split_ifs at h with empty
    · cases Option.some.inj h
      exact ⟨empty ▸ hs, ⟨[], empty ▸ GroupPath.done labels⟩⟩
    · obtain ⟨chosen, hsub, hc⟩ := chooseSubset_sound _ _ h
      split_ifs at hc with hne
      · obtain ⟨leaf, path, hp⟩ := run_leaf_path solve (remaining \ chosen)
          (assignGroup remaining chosen labels) hc
        exact ⟨leaf, ⟨chosen :: path, GroupPath.step hsub hne hp⟩⟩
termination_by remaining.card
decreasing_by exact group_progress hsub hne

theorem run_ne_none (solve : LayerSolver n Row) (target : Labels n)
    (canonical : CanonicalLabels target)
    (survives : ∀ remaining labels, Completion remaining labels target →
      solve remaining labels ≠ none)
    (remaining : Finset (Fin n)) (labels : Labels n)
    (completion : Completion remaining labels target) :
    run solve remaining labels ≠ none := by
  rw [run]
  cases hs : solve remaining labels with
  | none => exact (survives remaining labels completion hs).elim
  | some rows =>
    simp only
    split_ifs with empty
    · exact Option.some_ne_none _
    · intro failed
      obtain ⟨chosen, hsub, hne, hc⟩ := next_group completion canonical
        (Finset.nonempty_iff_ne_empty.mpr empty)
      have absent := (chooseSubset_none_iff _ _).mp failed chosen hsub
      simp only [dif_pos hne] at absent
      exact run_ne_none solve target canonical survives (remaining \ chosen)
        (assignGroup remaining chosen labels) hc absent
termination_by remaining.card
decreasing_by exact group_progress hsub hne

/-- The initial zero/positive split is shared as well as the recursive traversal. -/
def search (eligible : Finset (Fin n)) (solve : LayerSolver n Row) :
    Option (Labels n × Row) :=
  chooseSubset eligible fun remaining _ => run solve remaining (fun _ => 0)

/-- Enumerate only the undecided part of the initial support. The ordered-group
traversal is unchanged; `required` names have already been proved positive. -/
def searchRequired (eligible required : Finset (Fin n)) (solve : LayerSolver n Row) :
    Option (Labels n × Row) :=
  chooseSubset (eligible \ required) fun remaining _ =>
    run solve (required ∪ remaining) (fun _ => 0)

theorem searchRequired_sound (eligible required : Finset (Fin n))
    (solve : LayerSolver n Row) {Valid : Labels n → Row → Prop}
    (sound : ∀ labels rows, solve ∅ labels = some rows → Valid labels rows)
    {result : Labels n × Row} (h : searchRequired eligible required solve = some result) :
    Valid result.1 result.2 := by
  obtain ⟨remaining, _, found⟩ := chooseSubset_sound _ _ h
  exact sound _ _ (run_leaf_path solve _ _ found).1

theorem searchRequired_complete (eligible required : Finset (Fin n))
    (solve : LayerSolver n Row) {Valid : Labels n → Row → Prop}
    (preserves : ∀ target rows, Valid target rows →
      ∀ remaining labels, Completion remaining labels target → solve remaining labels ≠ none)
    (target : Labels n) (rows : Row) (valid : Valid target rows)
    (canonical : CanonicalLabels target) (support : positiveSupport target ⊆ eligible)
    (forced : required ⊆ positiveSupport target) :
    ∃ result, searchRequired eligible required solve = some result := by
  cases hs : searchRequired eligible required solve with
  | some result => exact ⟨result, rfl⟩
  | none =>
    have sub : positiveSupport target \ required ⊆ eligible \ required :=
      by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨support (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
    have absent := (chooseSubset_none_iff _ _).mp hs (positiveSupport target \ required) sub
    have same : required ∪ (positiveSupport target \ required) = positiveSupport target := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    rw [same] at absent
    exact (run_ne_none solve target canonical (preserves target rows valid)
      _ _ (initial_completion target) absent).elim

theorem search_leaf_path (eligible : Finset (Fin n)) (solve : LayerSolver n Row)
    {result : Labels n × Row} (h : search eligible solve = some result) :
    solve ∅ result.1 = some result.2 ∧
      ∃ remaining path, remaining ⊆ eligible ∧
        GroupPath remaining (fun _ => 0) path result.1 := by
  obtain ⟨remaining, sub, hr⟩ := chooseSubset_sound _ _ h
  obtain ⟨leaf, path, hp⟩ := run_leaf_path solve remaining (fun _ => 0) hr
  exact ⟨leaf, remaining, path, sub, hp⟩

theorem search_canonical (eligible : Finset (Fin n)) (solve : LayerSolver n Row)
    {result : Labels n × Row} (h : search eligible solve = some result) :
    CanonicalLabels result.1 := by
  obtain ⟨_, remaining, path, _, hp⟩ := search_leaf_path eligible solve h
  exact hp.canonical (initial_groupState remaining)

theorem search_support (eligible : Finset (Fin n)) (solve : LayerSolver n Row)
    {result : Labels n × Row} (h : search eligible solve = some result) :
    positiveSupport result.1 ⊆ eligible := by
  obtain ⟨_, remaining, path, sub, hp⟩ := search_leaf_path eligible solve h
  exact hp.support ▸ sub

theorem search_unique_path (eligible : Finset (Fin n)) (solve : LayerSolver n Row)
    {result : Labels n × Row} (h : search eligible solve = some result) :
    ∃! choice : Finset (Fin n) × List (Finset (Fin n)),
      choice.1 ⊆ eligible ∧ GroupPath choice.1 (fun _ => 0) choice.2 result.1 := by
  obtain ⟨_, remaining, path, sub, hp⟩ := search_leaf_path eligible solve h
  refine ⟨(remaining, path), ⟨sub, hp⟩, ?_⟩
  rintro ⟨other, steps⟩ ⟨_, ho⟩
  have eq : other = remaining := ho.support.trans hp.support.symm
  subst other
  exact Prod.ext rfl (ho.unique hp (initial_groupState remaining))

theorem search_sound (eligible : Finset (Fin n)) (solve : LayerSolver n Row)
    {Valid : Labels n → Row → Prop}
    (sound : ∀ labels rows, solve ∅ labels = some rows → Valid labels rows)
    {result : Labels n × Row} (h : search eligible solve = some result) :
    Valid result.1 result.2 :=
  sound _ _ (search_leaf_path eligible solve h).1

theorem search_complete (eligible : Finset (Fin n)) (solve : LayerSolver n Row)
    {Valid : Labels n → Row → Prop}
    (preserves : ∀ target rows, Valid target rows →
      ∀ remaining labels, Completion remaining labels target → solve remaining labels ≠ none)
    (target : Labels n) (rows : Row) (valid : Valid target rows)
    (canonical : CanonicalLabels target) (support : positiveSupport target ⊆ eligible) :
    ∃ result, search eligible solve = some result := by
  cases hs : search eligible solve with
  | some result => exact ⟨result, rfl⟩
  | none =>
    have absent := (chooseSubset_none_iff _ _).mp hs (positiveSupport target) support
    exact (run_ne_none solve target canonical (preserves target rows valid)
      _ _ (initial_completion target) absent).elim

theorem search_none_iff (eligible : Finset (Fin n)) (solve : LayerSolver n Row)
    {Valid : Labels n → Row → Prop}
    (sound : ∀ labels rows, solve ∅ labels = some rows → Valid labels rows)
    (preserves : ∀ target rows, Valid target rows →
      ∀ remaining labels, Completion remaining labels target → solve remaining labels ≠ none) :
    search eligible solve = none ↔
      ¬ ∃ labels rows, CanonicalLabels labels ∧ positiveSupport labels ⊆ eligible ∧
        Valid labels rows := by
  constructor
  · rintro failed ⟨labels, rows, canonical, support, valid⟩
    obtain ⟨result, found⟩ := search_complete eligible solve preserves labels rows valid canonical support
    rw [failed] at found
    cases found
  · intro no
    cases hs : search eligible solve with
    | none => rfl
    | some result =>
      exact (no ⟨result.1, result.2, search_canonical eligible solve hs,
        search_support eligible solve hs, search_sound eligible solve sound hs⟩).elim

end ACUIhE.ACUIESolver.Matching.GroupSearch
