import ACUIhE.ACUIESolver.Matching.Completeness
import ACUIhE.ACUIESolver.Matching.GroupSearch
import ACUIhE.ACUIESolver.Matching.Reconstruction

/-!
# Complete ordered E-matching search

Choose the zero edges and an ordered partition of the positive edges, with
necessary Horn propagation at every partial matching. Ranks are determined by
groups, never guessed. There is no row enumeration, fallback, assumed depth
bound, or validation of a candidate substitution.
-/

namespace ACUIhE.ACUIESolver.Matching

open ACUIhE.ACUIESolver.Finite

universe u v
variable {Const : Type u} {Var : Type v}
variable [DecidableEq Const] [DecidableEq Var]

def layerSolver (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var) :
    GroupSearch.LayerSolver ts.length (Layers.Rows ts.length) :=
  fun remaining labels => Layers.solve (partialConstraints ts p remaining labels)

theorem layerSolver_sound (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (labels : Labels ts.length) (rows : Layers.Rows ts.length)
    (h : layerSolver ts p ∅ labels = some rows) : Layers.Holds (constraints ts p labels) rows :=
  Layers.solve_sound _ (by simpa only [layerSolver, partialConstraints_empty] using h)

theorem layerSolver_preserves (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (target : Labels ts.length) (rows : Layers.Rows ts.length)
    (valid : Layers.Holds (constraints ts p target) rows)
    (remaining : Finset (Fin ts.length)) (labels : Labels ts.length)
    (completion : Completion remaining labels target) : layerSolver ts p remaining labels ≠ none :=
  fun failed => prune_sound ts p remaining labels failed target completion ⟨rows, valid⟩

def findTable (p : Problem Const Var) : Option (Table (pool p).length) :=
  (GroupSearch.search (edges (pool p)) (layerSolver (pool p) p)).map
    (fun result => table result.1 result.2)

theorem findTable_sound (p : Problem Const Var) {d : Table (pool p).length}
    (h : findTable p = some d) : Table.Valid (pool p) p d := by
  obtain ⟨result, found, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ((constraints_exact _ _ _ _).mp
    (GroupSearch.search_sound _ _ (layerSolver_sound _ _) found)).1

theorem findTable_canonical (p : Problem Const Var) {d : Table (pool p).length}
    (h : findTable p = some d) : CanonicalLabels d.rank := by
  obtain ⟨result, found, rfl⟩ := Option.map_eq_some_iff.mp h
  exact GroupSearch.search_canonical _ _ found

/-- A returned matching has a unique ordered-group path; no path is stored at runtime. -/
theorem findTable_unique_path (p : Problem Const Var) {d : Table (pool p).length}
    (h : findTable p = some d) :
    ∃! choice : Finset (Fin (pool p).length) × List (Finset (Fin (pool p).length)),
      choice.1 ⊆ edges (pool p) ∧ GroupPath choice.1 (fun _ => 0) choice.2 d.rank := by
  obtain ⟨result, found, rfl⟩ := Option.map_eq_some_iff.mp h
  exact GroupSearch.search_unique_path _ _ found

theorem findTable_complete (p : Problem Const Var) (h : p.Unifiable) :
    ∃ d, findTable p = some d := by
  obtain ⟨σ, hσ⟩ := h
  let target := canonicalizeLabels (extractedLabels (pool p) σ)
  have hcan : CanonicalLabels target := canonicalizeLabels_idempotent _
  have hsub : positiveSupport target ⊆ edges (pool p) := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
    cases he : isEdge ((pool p).get i) with
    | true => rfl
    | false =>
      exact (hn ((canonicalizeLabels_zero _ i).mpr
        (extractedLabels_nonedge (pool p) σ i he))).elim
  have hh : Layers.Holds (constraints (pool p) p target) (projectedRows (pool p) σ) := by
    rw [constraints_canonicalize]
    exact (constraints_exact _ _ _ _).mpr
      ⟨projected_valid p σ hσ, projected_exactNames (pool p) σ⟩
  obtain ⟨result, found⟩ := GroupSearch.search_complete _ _ (layerSolver_preserves (pool p) p)
    target (projectedRows (pool p) σ) hh hcan hsub
  exact ⟨table result.1 result.2, by simp only [findTable, found, Option.map_some]⟩

theorem findTable_none_iff (p : Problem Const Var) : findTable p = none ↔ ¬ p.Unifiable := by
  constructor
  · intro hn hu
    obtain ⟨d, hd⟩ := findTable_complete p hu
    simp [hn] at hd
  · intro hu
    cases hd : findTable p with
    | none => rfl
    | some d =>
      exact (hu ⟨Table.reconstruct (pool p) d, Table.reconstruct_sound p d (findTable_sound p hd)⟩).elim

/-- Construct one ordinary unifier, or decide that no unifier exists. -/
def unify (p : Problem Const Var) : Option (ACUIE.Substitution Const Var Var) :=
  (findTable p).map (reconstruct (pool p))

theorem unify_sound (p : Problem Const Var) {σ : ACUIE.Substitution Const Var Var}
    (h : unify p = some σ) : p.IsUnifier σ := by
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  exact reconstruct_sound p d (findTable_sound p hd)

theorem unify_none_iff (p : Problem Const Var) : unify p = none ↔ ¬ p.Unifiable := by
  rw [unify, Option.map_eq_none_iff, findTable_none_iff]

theorem unify_complete (p : Problem Const Var) (h : p.Unifiable) : ∃ σ, unify p = some σ := by
  obtain ⟨d, hd⟩ := findTable_complete p h
  exact ⟨reconstruct (pool p) d, by simp [unify, hd]⟩

end ACUIhE.ACUIESolver.Matching
