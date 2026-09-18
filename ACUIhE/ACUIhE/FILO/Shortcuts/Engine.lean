import ACUIhE.FILO.Shortcuts.Generation

/-! # The paper's shortcut loop: stored resolvers and actual early stopping -/

namespace ACUIhE.FILO.Shortcuts.Engine

open Components ACUIh.Linear Goal Table

universe v w

structure Found (Var : Type v) (Hom : Type w) where
  older : Store Var Hom
  initial : Entry Var Hom

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

/-- Stop when the initial shortcut is resolved, or when no new shortcut is
generated. Recursive calls strictly shrink the finite unexplored universe. -/
def search (g : Prepared Var Hom) (table : Store Var Hom) : Option (Found Var Hom) :=
  match make g.source table g.root with
  | some initial => some ⟨table, initial⟩
  | none =>
    let added := fresh g table
    if added = [] then none else search g (added ++ table)
termination_by (allNodes g \ nodes table).card
decreasing_by exact fresh_decreases g table (by assumption)

theorem search_sound (g : Prepared Var Hom) (table : Store Var Hom) (certified : Certified g table)
    {found : Found Var Hom} (h : search g table = some found) :
    Certified g found.older ∧ found.initial.node = g.root ∧ found.initial.Good g.source found.older := by
  revert certified h
  fun_induction search g table
  · intro certified h
    have eq := Option.some.inj h
    subst found
    rename_i hm
    exact ⟨certified, make_some g.source _ g.root hm⟩
  · intro certified h; cases h
  · rename_i ih
    intro certified h
    exact ih (fresh_certified g _ certified) h

theorem search_complete (g : Prepared Var Hom) (valid : g.Valid) (table : Store Var Hom)
    (iv : Column Var Hom) (solution : g.source.Solution iv)
    (hc : Choices.Classifies g.source g.choice iv) : search g table ≠ none := by
  fun_induction search g table
  · simp
  · rename_i _ stalled
    have ready := stalled_ready g valid _ stalled iv solution hc
    exact False.elim ((make_none_iff g.source _ g.root).mp (by assumption) ready)
  · assumption

def Found.reconstruct (g : Prepared Var Hom) (found : Found Var Hom) : Column Var Hom :=
  assignment (trace g.source (materialize g.source found.older) found.initial)

theorem found_solution (g : Prepared Var Hom) (valid : g.Valid) (flat : g.Flat g.root)
    (found : Found Var Hom) (certified : Certified g found.older)
    (root : found.initial.node = g.root) (good : found.initial.Good g.source found.older) :
    g.source.Solution (found.reconstruct g) := by
  have localRoot := g.compatible_local valid true g.root g.root_compatible flat
  have realizes := trace_correct g valid found.older (certified_normal g _ certified)
    (materialize g.source found.older) (materialize_nodes _ _)
    (materialize_correct g valid _ certified) found.initial true (root.symm ▸ localRoot) good
  exact trace_solution g.source found.initial.node _ (root.symm ▸ localRoot) realizes

def solve (g : Prepared Var Hom) : Option (Column Var Hom) :=
  if g.Flat g.root then (search g []).map (Found.reconstruct g) else none

theorem solve_sound (g : Prepared Var Hom) (valid : g.Valid) {iv : Column Var Hom}
    (h : solve g = some iv) : g.source.Solution iv := by
  unfold solve at h
  split at h
  · rename_i flat
    cases hs : search g [] with
    | none => simp [hs] at h
    | some found =>
      have eq := Option.some.inj (by simpa [hs] using h)
      subst iv
      obtain ⟨certified, root, good⟩ := search_sound g [] trivial hs
      exact found_solution g valid flat found certified root good
  · cases h

theorem solve_complete (g : Prepared Var Hom) (valid : g.Valid) (iv : Column Var Hom)
    (solution : g.source.Solution iv) (hc : Choices.Classifies g.source g.choice iv) :
    ∃ result, solve g = some result := by
  have flat : g.Flat g.root := by
    rw [← g.atWord_root iv hc]
    exact g.atWord_flat valid iv solution hc []
  cases hs : search g [] with
  | none => exact False.elim (search_complete g valid [] iv solution hc hs)
  | some found => exact ⟨found.reconstruct g, by simp [solve, flat, hs]⟩

end ACUIhE.FILO.Shortcuts.Engine
