import ACUIhE.Solver.Compatibility
import ACUIhE.FILO.Deferred
import ACUIhE.ACUIESolver.Matching.GroupSearch
import ACUIhE.ACUIESolver.Matching.WordRules

/-!
# Ordered E search with the shared matching rules and FILO

There is no second E-rule generator or recursive matching traversal here.
This module supplies the mixed layers to the existing rules and interprets
their conditions using FILO's word-valued coordinates.
-/

namespace ACUIhE.Solver

open ACUIh.Linear ACUIESolver.Matching

universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Hom]

namespace Prepared

abbrev Matrix (p : Prepared Const Var Hom) := GroundMatrix (Const ⊕ Fin p.edges.length) Var Hom
abbrev Layer (p : Prepared Const Var Hom) := WordRules.Layer Const Var Hom p.edges.length

def root (p : Prepared Const Var Hom) (i : Fin p.edges.length) : p.Layer :=
  .var (p.edges.get i).root

def child (p : Prepared Const Var Hom) (i : Fin p.edges.length) : p.Layer :=
  lift (p.edges.get i).child

def layerRules (p : Prepared Const Var Hom) : Rules.System p.Layer p.edges.length :=
  p.equations.map (fun q => .equal (.layer (lift q.left)) (.layer (lift q.right)))

def edgeRules (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (i : Fin p.edges.length) : Rules.System p.Layer p.edges.length :=
  Rules.complete (p.root i) (p.child i) p.child (Rules.group Finset.univ labels i) (lower labels i)

def partialEdgeRules (p : Prepared Const Var Hom) (remaining : Finset (Fin p.edges.length))
    (labels : Labels p.edges.length) (i : Fin p.edges.length) : Rules.System p.Layer p.edges.length :=
  if i ∈ remaining then Rules.pending (p.root i) (p.child i) remaining i else p.edgeRules labels i

def conditions (p : Prepared Const Var Hom) (remaining : Finset (Fin p.edges.length))
    (labels : Labels p.edges.length) : Rules.System p.Layer p.edges.length :=
  p.layerRules ++ (List.finRange p.edges.length).flatMap (p.partialEdgeRules remaining labels)

/-- Satisfaction of a completed symbolic matching, independently of search. -/
def Matches (p : Prepared Const Var Hom) (labels : Labels p.edges.length) (m : p.Matrix) : Prop :=
  Rules.Holds (WordRules.interpretation m) (p.conditions ∅ labels)

theorem matches_iff (p : Prepared Const Var Hom) (labels : Labels p.edges.length) (m : p.Matrix) :
    p.Matches labels m ↔
      Rules.Holds (WordRules.interpretation m) p.layerRules ∧
      ∀ i, Rules.Holds (WordRules.interpretation m) (p.edgeRules labels i) := by
  simp only [Matches, conditions, Rules.holds_append, Rules.holds_flatMap,
    List.mem_finRange, forall_true_left, partialEdgeRules, Finset.notMem_empty, if_false]

theorem partial_necessary (p : Prepared Const Var Hom)
    {remaining : Finset (Fin p.edges.length)} {labels target : Labels p.edges.length}
    (completion : Completion remaining labels target) (m : p.Matrix) (valid : p.Matches target m) :
    Rules.Holds (WordRules.interpretation m) (p.conditions remaining labels) := by
  obtain ⟨layers, edges⟩ := (p.matches_iff target m).mp valid
  rw [conditions, Rules.holds_append]
  refine ⟨layers, ?_⟩
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  have node : Rules.Holds (WordRules.interpretation m) (p.partialEdgeRules remaining labels i) := by
    by_cases pending : i ∈ remaining
    · rw [partialEdgeRules, if_pos pending]
      apply Rules.pending_of_complete (WordRules.interpretation m) (WordRules.atoms_mono m)
        _ _ _ _ _ _ _ (edges i)
      · simp [Rules.group, (completion.pending i pending).2]
      · intro j hj
        exact completion.pending_group_mem pending ((Rules.mem_group _ _ _ _).mp hj).2.1
      · simp [lower]
    · rw [partialEdgeRules, if_neg pending]
      have group : Rules.group Finset.univ labels i = Rules.group Finset.univ target i := by
        ext j
        simp only [Rules.mem_group, Finset.mem_univ, true_and,
          completion.same_group_assigned pending]
      simpa only [edgeRules, group, completion.lower_eq pending] using edges i
  exact node c hc

theorem matches_canonicalize (p : Prepared Const Var Hom)
    (labels : Labels p.edges.length) (m : p.Matrix) :
    p.Matches (canonicalizeLabels labels) m ↔ p.Matches labels m := by
  have same (i : Fin p.edges.length) : p.edgeRules (canonicalizeLabels labels) i = p.edgeRules labels i := by
    have group : Rules.group Finset.univ (canonicalizeLabels labels) i = Rules.group Finset.univ labels i := by
      ext j
      simp only [Rules.mem_group, canonicalizeLabels_eq, ne_eq, canonicalizeLabels_zero]
    simp only [edgeRules, group, lower_canonicalize]
  simp only [matches_iff, same]

variable [DecidableEq Var]

def solveLayers (p : Prepared Const Var Hom) (remaining : Finset (Fin p.edges.length))
    (labels : Labels p.edges.length) : Option p.Matrix :=
  FILO.Coordinates.solve (WordRules.compile (p.conditions remaining labels))

theorem solveLayers_sound (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (found : p.solveLayers ∅ labels = some m) : p.Matches labels m :=
  (WordRules.compile_exact m _).mp (FILO.Coordinates.solve_sound _ found)

theorem solveLayers_preserves (p : Prepared Const Var Hom) (target : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches target m)
    (remaining : Finset (Fin p.edges.length)) (labels : Labels p.edges.length)
    (completion : Completion remaining labels target) : p.solveLayers remaining labels ≠ none := by
  intro failed
  exact (FILO.Coordinates.solve_none_iff _).mp failed
    ⟨m, (WordRules.compile_exact m _).mpr (p.partial_necessary completion m valid)⟩

omit [DecidableEq Var] in
/-- Rigid constants force positive support in every satisfying matching. -/
theorem required_positive (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) : p.required ⊆ positiveSupport labels := by
  intro i hi
  have hc : hasConstant (p.edges.get i).child = true := (Finset.mem_filter.mp hi).2
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hz
  have empty : Rules.group Finset.univ labels i = ∅ := by
    ext j
    simp [Rules.group, hz]
  have edge := (p.matches_iff labels m).mp valid |>.2 i
  have zero := (Rules.complete_iff (WordRules.interpretation m) _ _ _ _ _).mp edge |>.2.1 empty
  have nonempty := constant_nonempty (lift (n := p.edges.length) (p.edges.get i).child) m
    (by simpa only [hasConstant_lift] using hc)
  apply nonempty.ne_empty
  simpa only [child, WordRules.interpretation, WordRules.atoms, Finset.image_empty] using zero

/-- A positive E root occurring in a child contributes its own coordinate,
so the completed support restriction forces a strictly smaller rank. -/
theorem dependency_order (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) (i j : Fin p.edges.length)
    (occurs : hasVariable (p.edges.get j).root (p.edges.get i).child = true)
    (positive : labels j ≠ 0) : labels j < labels i := by
  have edges := (p.matches_iff labels m).mp valid |>.2
  have rootj := (Rules.complete_iff (WordRules.interpretation m) _ _ _ _ _).mp (edges j) |>.1
  have own : ([], ACUIh.Particle.const (.inr j)) ∈ (m (p.edges.get j).root).toNF := by
    change ([], ACUIh.Particle.const (.inr j)) ∈ (WordRules.interpretation m).layer (p.root j)
    rw [rootj]
    exact Finset.mem_image.mpr ⟨j, by simp [Rules.group, positive], rfl⟩
  obtain ⟨word, member⟩ := variable_support (lift (n := p.edges.length) (p.edges.get i).child)
    (p.edges.get j).root m (.inr j) (by simpa using occurs) ⟨[], own⟩
  have nonzero : Row.ofNF (instantiateNF m (p.child i)) (.inr j) ≠ 0 := by
    intro zero
    have hm := (mem_coefficient (instantiateNF m (p.child i)) (.const (.inr j)) word).mpr member
    change word ∈ (Row.ofNF (instantiateNF m (p.child i)) (.inr j)).words at hm
    rw [zero] at hm
    exact Finset.notMem_empty word hm
  have supported := (Rules.complete_iff (WordRules.interpretation m) _ _ _ _ _).mp (edges i) |>.2.2.2
  have lower := supported (Finset.mem_filter.mpr ⟨Finset.mem_univ j, nonzero⟩)
  exact (Finset.mem_filter.mp lower).2

theorem dependencies_ready (p : Prepared Const Var Hom) (target : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches target m) (remaining : Finset (Fin p.edges.length))
    (labels : Labels p.edges.length) (completion : Completion remaining labels target) :
    p.dependencies.all (fun ij => decide (dependencyReady remaining labels ij)) = true := by
  apply List.all_eq_true.mpr
  intro ij member
  obtain ⟨i, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨j, hj, eq⟩ := List.mem_map.mp member
  subst ij
  have occurs := (List.mem_filter.mp hj).2
  exact decide_eq_true (dependencyReady_of_completion remaining labels target completion i j
    (p.dependency_order target m valid i j occurs))

omit [DecidableEq Var] in
theorem matching_compatible (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) (i j : Fin p.edges.length)
    (positive : labels i ≠ 0) (same : labels j = labels i) :
    compatible (p.edges.get i).child (p.edges.get j).child = true := by
  have edge := (p.matches_iff labels m).mp valid |>.2 i
  have full := (Rules.complete_iff (WordRules.interpretation m) _ _ _ _ _).mp edge
  have eq := full.2.2.1 j (by simp [Rules.group, positive, same])
  have comp := compatible_necessary (p.child i) (p.child j) m eq.symm
  simpa only [child, compatible_lift] using comp

def separateGroups {n : Nat} (labels : Labels n) (ij : Fin n × Fin n) : Bool :=
  decide (labels ij.1 = 0 ∨ labels ij.2 = 0 ∨ labels ij.1 ≠ labels ij.2)

theorem incompatible_ready (p : Prepared Const Var Hom) (target : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches target m) (remaining : Finset (Fin p.edges.length))
    (labels : Labels p.edges.length) (completion : Completion remaining labels target) :
    p.incompatible.all (separateGroups labels) = true := by
  apply List.all_eq_true.mpr
  intro ij member
  obtain ⟨i, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨j, hj, eq⟩ := List.mem_map.mp member
  subst ij
  have bad : compatible (p.edges.get i).child (p.edges.get j).child = false := by
    simpa using (List.mem_filter.mp hj).2
  apply decide_eq_true
  by_cases hi : labels i = 0
  · exact Or.inl hi
  by_cases hj : labels j = 0
  · exact Or.inr (Or.inl hj)
  right; right
  intro same
  have ni : i ∉ remaining := fun h => hi (completion.pending i h).1
  have nj : j ∉ remaining := fun h => hj (completion.pending j h).1
  have good := p.matching_compatible target m valid i j
    (by rwa [← completion.assigned i ni])
    (by rw [← completion.assigned j nj, ← completion.assigned i ni]; exact same.symm)
  rw [bad] at good
  contradiction

/-- Intermediate E states retain FILO plans without materializing matrices. -/
def deferredLayers (p : Prepared Const Var Hom) (remaining : Finset (Fin p.edges.length))
    (labels : Labels p.edges.length) : Option (Unit → p.Matrix) :=
  FILO.Coordinates.defer (WordRules.compile (p.conditions remaining labels))

theorem deferredLayers_eq (p : Prepared Const Var Hom) (remaining : Finset (Fin p.edges.length))
    (labels : Labels p.edges.length) :
    (p.deferredLayers remaining labels).map (fun f => f ()) = p.solveLayers remaining labels :=
  FILO.Coordinates.defer_eq _

theorem deferredLayers_sound (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (f : Unit → p.Matrix) (found : p.deferredLayers ∅ labels = some f) : p.Matches labels (f ()) := by
  apply p.solveLayers_sound labels (f ())
  rw [← p.deferredLayers_eq, found]
  rfl

theorem deferredLayers_preserves (p : Prepared Const Var Hom) (target : Labels p.edges.length)
    (f : Unit → p.Matrix) (valid : p.Matches target (f ()))
    (remaining : Finset (Fin p.edges.length)) (labels : Labels p.edges.length)
    (completion : Completion remaining labels target) : p.deferredLayers remaining labels ≠ none := by
  intro failed
  apply p.solveLayers_preserves target (f ()) valid remaining labels completion
  rw [← p.deferredLayers_eq, failed]
  rfl

/-- The dependency list is shared by all callbacks of this traversal. -/
def guardedLayers (p : Prepared Const Var Hom)
    (dependencies incompatible : List (Fin p.edges.length × Fin p.edges.length))
    (remaining : Finset (Fin p.edges.length)) (labels : Labels p.edges.length) : Option (Unit → p.Matrix) :=
  if dependencies.all (fun ij => decide (dependencyReady remaining labels ij)) &&
      incompatible.all (separateGroups labels) then
    p.deferredLayers remaining labels else none

theorem guardedLayers_sound (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (f : Unit → p.Matrix) (found : p.guardedLayers p.dependencies p.incompatible ∅ labels = some f) :
    p.Matches labels (f ()) := by
  unfold guardedLayers at found
  split_ifs at found
  exact p.deferredLayers_sound labels f found

theorem guardedLayers_preserves (p : Prepared Const Var Hom) (target : Labels p.edges.length)
    (f : Unit → p.Matrix) (valid : p.Matches target (f ()))
    (remaining : Finset (Fin p.edges.length)) (labels : Labels p.edges.length)
    (completion : Completion remaining labels target) : p.guardedLayers p.dependencies p.incompatible remaining labels ≠ none := by
  simpa only [guardedLayers, p.dependencies_ready target (f ()) valid remaining labels completion,
    p.incompatible_ready target (f ()) valid remaining labels completion, Bool.and_self,
    if_true] using p.deferredLayers_preserves target f valid remaining labels completion

def searchDeferred (p : Prepared Const Var Hom) : Option (Labels p.edges.length × (Unit → p.Matrix)) :=
  GroupSearch.searchRequired Finset.univ p.required (p.guardedLayers p.dependencies p.incompatible)

theorem searchDeferred_sound (p : Prepared Const Var Hom)
    {result : Labels p.edges.length × (Unit → p.Matrix)}
    (found : p.searchDeferred = some result) : p.Matches result.1 (result.2 ()) :=
  GroupSearch.searchRequired_sound _ _ _ p.guardedLayers_sound found

theorem searchDeferred_complete (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) : ∃ result, p.searchDeferred = some result :=
  GroupSearch.searchRequired_complete _ _ _ p.guardedLayers_preserves
    (canonicalizeLabels labels) (fun _ => m)
    ((p.matches_canonicalize labels m).mpr valid) (canonicalizeLabels_idempotent labels)
    (Finset.subset_univ _)
    (p.required_positive _ m ((p.matches_canonicalize labels m).mpr valid))

/-- Materialize only the accepted leaf, sharing the traversal with the Boolean API. -/
def search (p : Prepared Const Var Hom) : Option (Labels p.edges.length × p.Matrix) :=
  p.searchDeferred.map (fun result => (result.1, result.2 ()))

theorem search_sound (p : Prepared Const Var Hom) {result : Labels p.edges.length × p.Matrix}
    (found : p.search = some result) : p.Matches result.1 result.2 := by
  cases h : p.searchDeferred with
  | none => simp [search, h] at found
  | some plan =>
    have eq : (plan.1, plan.2 ()) = result := by simpa only [search, h, Option.map_some,
      Option.some.injEq] using found
    cases eq
    exact p.searchDeferred_sound h

theorem search_complete (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) : ∃ result, p.search = some result := by
  obtain ⟨result, found⟩ := p.searchDeferred_complete labels m valid
  exact ⟨(result.1, result.2 ()), by simp only [search, found, Option.map_some]⟩

theorem search_none_iff (p : Prepared Const Var Hom) :
    p.search = none ↔ ¬ ∃ labels m, p.Matches labels m := by
  constructor
  · rintro failed ⟨labels, m, valid⟩
    obtain ⟨result, found⟩ := p.search_complete labels m valid
    rw [failed] at found
    cases found
  · intro no
    cases found : p.search with
    | none => rfl
    | some result => exact (no ⟨result.1, result.2, p.search_sound found⟩).elim

end Prepared
end ACUIhE.Solver
