import ACUIHE.Optimized.FILO.Soundness

/-!
# Completeness of FILO shortcut saturation

For the small-model argument only, shortcuts are indexed by their positions
in the explicit candidate list.  This yields a finite automaton with exactly
`shortcutList.length` states.  The generic productive-state theorem supplies
a witness of at most that height; the executable FILO builder is then proved
to reconstruct such a witness without enumerating automaton states.
-/

namespace ACUIHE.Solver.Search.FiniteLanguageSystem

set_option maxHeartbeats 800000

open ACUIHE.Optimized.FILO
open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

local instance encodableDecidableEqCompleteness
    {Alpha : Type*} [Encodable Alpha] : DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

variable {Row Variable Hom : Type u}
  [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]

/-- A numeric shortcut state.  Duplicates in the explicit enumeration are
harmless and keep this indexing entirely executable. -/
abbrev ShortcutIndex (problem : FiniteLanguageSystem Row Variable Hom) :=
  ULift.{u} (Fin problem.shortcutList.length)

/-- Decode an indexed shortcut state. -/
def shortcutAt (problem : FiniteLanguageSystem Row Variable Hom)
    (index : problem.ShortcutIndex) :
    Shortcut (Variable := Variable) (Hom := Hom) :=
  problem.shortcutList.get index.down

@[simp]
theorem shortcutAt_mem_list
    (problem : FiniteLanguageSystem Row Variable Hom)
    (index : problem.ShortcutIndex) :
    problem.shortcutAt index ∈ problem.shortcutList := by
  exact List.get_mem _ _

theorem shortcutAt_subset_atoms
    (problem : FiniteLanguageSystem Row Variable Hom)
    (index : problem.ShortcutIndex) :
    problem.shortcutAt index ⊆ problem.atoms :=
  (problem.mem_shortcutList_iff _).mp (problem.shortcutAt_mem_list index)

/-- The finite automaton used only to justify the small-model bound.  A label
chooses one indexed child for each role. -/
def boundAutomaton (problem : FiniteLanguageSystem Row Variable Hom) :
    Automaton problem.ShortcutIndex Hom (Hom → problem.ShortcutIndex) where
  locallyValid state children := decide
    (problem.ShortcutValid (problem.shortcutAt state) ∧
      ∀ role, problem.Resolves (problem.shortcutAt state) role
        (problem.shortcutAt (children role)))
  terminal state _ := decide
    (problem.ShortcutValid (problem.shortcutAt state) ∧
      problem.Terminal (problem.shortcutAt state))
  next _ children role := children role

theorem buildChild?_complete
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom)))
    (build : Shortcut (Variable := Variable) (Hom := Hom) →
      Option (Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))))
    (parent child : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) (childInCandidates : child ∈ candidates)
    (resolves : problem.Resolves parent role child)
    {tree} (built : build child = some tree) :
    ∃ result, problem.buildChild? candidates build parent role = some result := by
  unfold buildChild?
  exact Automaton.firstResult?_complete _ candidates
    (candidate := child) (result := tree) childInCandidates
    (by simp [resolves, built])

/-- The dedicated builder realizes every bounded witness of the proof
automaton. -/
theorem build?_complete_of_boundAutomaton
    (problem : FiniteLanguageSystem Row Variable Hom) :
    ∀ bound (state : problem.ShortcutIndex)
      (tree : BoundedTree Hom (Hom → problem.ShortcutIndex) bound),
      problem.boundAutomaton.Accepts state (tree.toTree bound) →
      ∃ result, problem.build? problem.shortcutList bound
        (problem.shortcutAt state) = some result := by
  intro bound
  induction bound with
  | zero =>
      intro state label accepted
      cases accepted with
      | leaf locallyValid terminal =>
          have facts : problem.ShortcutValid (problem.shortcutAt state) ∧
              problem.Terminal (problem.shortcutAt state) := by
            simpa [boundAutomaton] using of_decide_eq_true terminal
          exact ⟨.leaf (problem.shortcutAt state), by
            simp [build?, facts]⟩
  | succ bound inductionHypothesis =>
      intro state tree accepted
      rcases tree with ⟨label, children⟩
      cases children with
      | none =>
          cases accepted with
          | leaf locallyValid terminal =>
              have facts : problem.ShortcutValid (problem.shortcutAt state) ∧
                  problem.Terminal (problem.shortcutAt state) := by
                simpa [boundAutomaton] using of_decide_eq_true terminal
              exact ⟨.leaf (problem.shortcutAt state), by
                simp [build?, facts]⟩
      | some children =>
          cases accepted with
          | node locallyValid descendants =>
              have localFacts :
                  problem.ShortcutValid (problem.shortcutAt state) ∧
                    ∀ role, problem.Resolves (problem.shortcutAt state) role
                      (problem.shortcutAt (label role)) := by
                simpa [boundAutomaton] using of_decide_eq_true locallyValid
              by_cases terminal : problem.Terminal (problem.shortcutAt state)
              · exact ⟨.leaf (problem.shortcutAt state), by
                  simp [build?, localFacts.1, terminal]⟩
              · have childResults : ∀ role,
                    (problem.buildChild? problem.shortcutList
                      (problem.build? problem.shortcutList bound)
                      (problem.shortcutAt state) role).isSome := by
                  intro role
                  rcases inductionHypothesis (label role) (children role)
                      (descendants role) with ⟨childTree, childBuilt⟩
                  rcases problem.buildChild?_complete problem.shortcutList
                      (problem.build? problem.shortcutList bound)
                      (problem.shortcutAt state)
                      (problem.shortcutAt (label role)) role
                      (problem.shortcutAt_mem_list (label role))
                      (localFacts.2 role) childBuilt with
                    ⟨result, found⟩
                  rw [found]
                  trivial
                let child? := problem.buildChild? problem.shortcutList
                  (problem.build? problem.shortcutList bound)
                  (problem.shortcutAt state)
                exact ⟨.node (problem.shortcutAt state) fun role =>
                    (child? role).get (childResults role), by
                  simp only [build?]
                  simp [localFacts.1, terminal, childResults, child?]⟩

theorem semanticShortcut_mem_shortcutList
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom) :
    problem.semanticShortcut values word ∈ problem.shortcutList := by
  apply (problem.mem_shortcutList_iff _).mpr
  exact problem.semanticShortcut_subset_atoms values word

/-- A proof-only index for the semantic shortcut at `word`. -/
noncomputable def semanticIndex
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom) :
    problem.ShortcutIndex :=
  ULift.up <| Classical.choose <| List.exists_mem_iff_get.mp
    ⟨problem.semanticShortcut values word,
      problem.semanticShortcut_mem_shortcutList values word, rfl⟩

@[simp]
theorem shortcutAt_semanticIndex
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom) :
    problem.shortcutAt (problem.semanticIndex values word) =
      problem.semanticShortcut values word := by
  unfold semanticIndex shortcutAt
  exact (Classical.choose_spec (List.exists_mem_iff_get.mp
    ⟨problem.semanticShortcut values word,
      problem.semanticShortcut_mem_shortcutList values word, rfl⟩)).symm

theorem semanticShortcut_empty_of_length_gt
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom)
    (tooLong : valuesPathBound values + problem.pathBound < word.length) :
    problem.semanticShortcut values word = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro atom membership
  rcases (problem.mem_semanticShortcut_iff values word atom).mp membership with
    ⟨atomInUniverse, holds⟩
  cases atom with
  | var index path =>
      rcases holds with ⟨suffix, suffixMembership, equality⟩
      have pathBound := (problem.var_mem_atoms_iff index path).mp atomInUniverse
      have suffixBound := value_path_length_le_valuesPathBound
        values index suffixMembership
      have total : word.length ≤ valuesPathBound values + problem.pathBound := by
        rw [← equality, List.length_append]
        omega
      omega
  | constant path =>
      have pathBound := (problem.constant_mem_atoms_iff path).mp atomInUniverse
      subst word
      omega

theorem semanticShortcut_terminal_of_child_empty
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom)
    (emptyChildren : ∀ role,
      problem.semanticShortcut values (role :: word) = ∅) :
    problem.Terminal (problem.semanticShortcut values word) := by
  intro role
  rw [← emptyChildren role]
  exact problem.semanticShortcut_resolves values word role

/-- Complete semantic shortcut tree for a supplied solution. -/
noncomputable def semanticTree
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) :
    Tree Hom (Hom → problem.ShortcutIndex) :=
  Tree.completeAt
    (fun mirrored role =>
      problem.semanticIndex values (role :: mirrored.reverse))
    (valuesPathBound values + problem.pathBound) []

theorem semanticTree_accepts_from
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom)
    (solution : problem.IsSolution values)
    (totalDepth depth : Nat) (mirrored : List Hom)
    (totalDepthEq : totalDepth = valuesPathBound values + problem.pathBound)
    (lengthEq : mirrored.length + depth = totalDepth) :
    problem.boundAutomaton.Accepts
      (problem.semanticIndex values mirrored.reverse)
      (Tree.completeAt
        (fun path role =>
          problem.semanticIndex values (role :: path.reverse))
        depth mirrored) := by
  induction depth generalizing mirrored with
  | zero =>
      apply Automaton.Accepts.leaf
      · simp only [boundAutomaton, shortcutAt_semanticIndex,
          decide_eq_true_eq]
        exact ⟨problem.semanticShortcut_valid values solution mirrored.reverse,
          fun role => by
            simpa using problem.semanticShortcut_resolves
              values mirrored.reverse role⟩
      · simp only [boundAutomaton, shortcutAt_semanticIndex,
          decide_eq_true_eq]
        refine ⟨problem.semanticShortcut_valid values solution mirrored.reverse, ?_⟩
        apply problem.semanticShortcut_terminal_of_child_empty values
        intro role
        apply problem.semanticShortcut_empty_of_length_gt values
        rw [← totalDepthEq, ← lengthEq]
        simp
  | succ depth inductionHypothesis =>
      apply Automaton.Accepts.node
      · simp only [boundAutomaton, shortcutAt_semanticIndex,
          decide_eq_true_eq]
        exact ⟨problem.semanticShortcut_valid values solution mirrored.reverse,
          fun role => by
            simpa using problem.semanticShortcut_resolves
              values mirrored.reverse role⟩
      · intro role
        simpa [boundAutomaton, List.reverse_append] using
          inductionHypothesis (mirrored ++ [role]) (by
            simp only [List.length_append, List.length_singleton]
            omega)

theorem semanticTree_accepts
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom)
    (solution : problem.IsSolution values) :
    problem.boundAutomaton.Accepts (problem.semanticIndex values [])
      (problem.semanticTree values) := by
  unfold semanticTree
  apply problem.semanticTree_accepts_from values solution
    (valuesPathBound values + problem.pathBound)
    (valuesPathBound values + problem.pathBound) [] rfl
  simp

/-- Any genuine finite-language solution makes the executable root search
succeed. -/
theorem buildRoot?_complete
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom)
    (solution : problem.IsSolution values) :
    ∃ tree, problem.buildRoot? = some tree := by
  let automaton := problem.boundAutomaton
  let initial := problem.semanticIndex values []
  have accepted : automaton.Accepts initial (problem.semanticTree values) :=
    problem.semanticTree_accepts values solution
  have productive : initial ∈ automaton.productiveStates :=
    automaton.accepts_mem_productiveStates accepted
  have atBound : initial ∈ automaton.productiveStages
      problem.shortcutList.length := by
    simpa [Automaton.productiveStates, automaton] using productive
  rcases automaton.mem_productiveStages_has_boundedTree
      problem.shortcutList.length initial atBound with
    ⟨boundedTree, boundedAccepted⟩
  rcases problem.build?_complete_of_boundAutomaton
      problem.shortcutList.length initial boundedTree boundedAccepted with
    ⟨tree, built⟩
  have initialValue : problem.shortcutAt initial =
      problem.semanticShortcut values [] := by
    simp [initial]
  have rootCompatible : problem.RootCompatible (problem.shortcutAt initial) := by
    rw [initialValue]
    exact problem.semanticShortcut_rootCompatible values
  unfold buildRoot?
  apply Automaton.firstResult?_complete _ problem.shortcutList
    (candidate := problem.shortcutAt initial) (result := tree)
  · exact problem.shortcutAt_mem_list initial
  · simp [rootCompatible, built]

end ACUIHE.Solver.Search.FiniteLanguageSystem
