import ACUIhE.FILO.Choices.Indexing
import ACUIhE.FILO.Goal.Starts
import ACUIhE.FILO.Shortcuts.Engine

/-!
# FILO's choice loop, implicit solver, and shortcut solver

Search returns a plain-data reconstruction plan. Both the no-unsolved and
shortcut paths have proofs against the original generic-system semantics.
The decision-only API does not perform reconstruction.
-/

namespace ACUIhE.FILO.GenericSolver

open Components ACUIh.Linear Choices Goal

universe v w

inductive Plan (Var : Type v) (Hom : Type w) where
  | starts : Prepared Var Hom → Plan Var Hom
  | shortcuts : Prepared Var Hom → Shortcuts.Engine.Found Var Hom → Plan Var Hom

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def Plan.Correct (s : System Var Hom) : Plan Var Hom → Prop
  | .starts g => g.source = s ∧ g.Valid ∧ g.unsolved = []
  | .shortcuts g found => g.source = s ∧ g.Valid ∧ g.Flat g.root ∧
      Shortcuts.Table.Certified g found.older ∧ found.initial.node = g.root ∧
      found.initial.Good g.source found.older

def Plan.reconstruct : Plan Var Hom → Column Var Hom
  | .starts g => Starts.solve g
  | .shortcuts g found => found.reconstruct g

theorem Plan.reconstruct_correct (s : System Var Hom) (plan : Plan Var Hom) (h : plan.Correct s) :
    s.Solution plan.reconstruct := by
  cases plan with
  | starts g =>
    obtain ⟨rfl, valid, empty⟩ := h
    exact Starts.solve_sound g valid empty
  | shortcuts g found =>
    obtain ⟨rfl, valid, flat, certified, root, good⟩ := h
    exact Shortcuts.Engine.found_solution g valid flat found certified root good

/-- One consistent choice, with Figure 3 applied before shortcut generation. -/
def runChoice (s : System Var Hom) (choice : Choice Var Hom) : Option (Plan Var Hom) :=
  if Consistent s choice then
    match Implicit.reduce s choice with
    | none => none
    | some residual =>
      let g : Prepared Var Hom := ⟨s, choice, residual⟩
      if residual = [] then some (.starts g)
      else if g.Flat g.root then (Shortcuts.Engine.search g []).map (.shortcuts g) else none
  else none

theorem runChoice_sound (s : System Var Hom) (choice : Choice Var Hom) {plan : Plan Var Hom}
    (h : runChoice s choice = some plan) : plan.Correct s := by
  unfold runChoice at h
  split at h
  · rename_i consistent
    cases hr : Implicit.reduce s choice with
    | none => simp [hr] at h
    | some residual =>
      simp only [hr] at h
      split at h
      · rename_i empty
        have eq := Option.some.inj h
        subst plan
        exact ⟨rfl, ⟨consistent, hr⟩, empty⟩
      · split at h
        · rename_i flat
          let g : Prepared Var Hom := ⟨s, choice, residual⟩
          cases hs : Shortcuts.Engine.search g [] with
          | none => simp [show Shortcuts.Engine.search ⟨s, choice, residual⟩ [] = none from hs] at h
          | some found =>
            have eq := Option.some.inj (by simpa [show Shortcuts.Engine.search ⟨s, choice, residual⟩ [] = some found from hs] using h)
            subst plan
            obtain ⟨certified, root, good⟩ := Shortcuts.Engine.search_sound g [] trivial hs
            exact ⟨rfl, ⟨consistent, hr⟩, flat, certified, root, good⟩
        · cases h
  · cases h

theorem runChoice_complete (s : System Var Hom) (choice : Choice Var Hom) (iv : Column Var Hom)
    (solution : s.Solution iv) (hc : Classifies s choice iv) : ∃ plan, runChoice s choice = some plan := by
  have consistent : Consistent s choice := consistent_congr s choice (ofAssignment iv) hc
    (ofAssignment_consistent s iv solution.1)
  obtain ⟨residual, hr⟩ := Implicit.reduce_complete s choice iv solution hc
  let g : Prepared Var Hom := ⟨s, choice, residual⟩
  have valid : g.Valid := ⟨consistent, hr⟩
  by_cases empty : residual = []
  · refine ⟨.starts g, ?_⟩
    simp only [runChoice, if_pos consistent, hr, if_pos empty]
    rfl
  · have flat : g.Flat g.root := by
      rw [← g.atWord_root iv hc]
      exact g.atWord_flat valid iv solution hc []
    cases hs : Shortcuts.Engine.search g [] with
    | none => exact False.elim (Shortcuts.Engine.search_complete g valid [] iv solution hc hs)
    | some found =>
      refine ⟨.shortcuts g found, ?_⟩
      change (if Consistent s choice then _ else _) = _
      rw [if_pos consistent]
      simp only [hr]
      change (if residual = [] then _ else if g.Flat g.root then _ else _) = _
      rw [if_neg empty, if_pos flat, hs]
      rfl

/-- Compile the occurrence lists once, then propagate after each partial choice. -/
def search (s : System Var Hom) : Option (Plan Var Hom) :=
  let cs := clauses s
  if ∀ q ∈ cs, q.Feasible then
    Indexing.run s.names cs (runChoice s)
  else none

theorem search_sound (s : System Var Hom) {plan : Plan Var Hom} (h : search s = some plan) :
    plan.Correct s := by
  unfold search at h
  dsimp only at h
  split at h
  swap
  · cases h
  obtain ⟨choice, found⟩ := Indexing.run_sound _ _ _ h
  exact runChoice_sound s choice found

theorem search_complete (s : System Var Hom) (h : s.Solvable) : ∃ plan, search s = some plan := by
  obtain ⟨iv, solution⟩ := h
  have feasible : ∀ q ∈ clauses s, q.Feasible :=
    fun q hq => Clause.feasible_of_holds _ q (clauses_sound s iv solution q hq)
  have found : search s ≠ none := by
    rw [search, if_pos feasible]
    exact Indexing.run_complete s.names (clauses s)
      (ofAssignment iv) (clauses_sound s iv solution)
      (runChoice s) (by
        intro choice same absent
        obtain ⟨plan, hp⟩ := runChoice_complete s choice iv solution same
        rw [absent] at hp
        cases hp)
  cases hs : search s with
  | none => exact False.elim (found hs)
  | some result => exact ⟨result, rfl⟩

theorem search_none_iff (s : System Var Hom) : search s = none ↔ ¬ s.Solvable := by
  constructor
  · intro h solvable
    obtain ⟨plan, found⟩ := search_complete s solvable
    rw [h] at found
    cases found
  · intro no
    cases h : search s with
    | none => rfl
    | some plan => exact False.elim (no ⟨plan.reconstruct,
        plan.reconstruct_correct s (search_sound s h)⟩)

def solve (s : System Var Hom) : Option (Column Var Hom) := (search s).map Plan.reconstruct

theorem solve_sound (s : System Var Hom) {iv : Column Var Hom} (h : solve s = some iv) :
    s.Solution iv := by
  unfold solve at h
  cases hs : search s with
  | none => simp [hs] at h
  | some plan =>
    have eq := Option.some.inj (by simpa [hs] using h)
    subst iv
    exact plan.reconstruct_correct s (search_sound s hs)

theorem solve_none_iff (s : System Var Hom) : solve s = none ↔ ¬ s.Solvable := by
  simp only [solve, Option.map_eq_none_iff, search_none_iff]

theorem search_isSome_iff (s : System Var Hom) : (search s).isSome = true ↔ s.Solvable := by
  cases hs : search s with
  | none => simp [show ¬ s.Solvable from (search_none_iff s).mp hs]
  | some plan => simp [show s.Solvable from
      ⟨plan.reconstruct, plan.reconstruct_correct s (search_sound s hs)⟩]

end ACUIhE.FILO.GenericSolver
