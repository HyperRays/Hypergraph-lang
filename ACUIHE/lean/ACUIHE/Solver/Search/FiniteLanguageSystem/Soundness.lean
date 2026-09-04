import ACUIHE.Solver.Search.FiniteLanguageSystem.Outputs

/-!
Decoding candidate trees and proving automaton acceptance sound.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u

attribute [local instance]
  finiteLanguageDecidableEq finiteLanguageBoolFinEnum

/-- Decode a membership-labelled tree to finite languages for the variables.
Tree paths are mirrored back to the coefficient-first
orientation used by `HomContext`. -/
def decodeVariableLanguages
    {Variable Hom : Type u}
    [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (tree : Tree Hom (VariableLabel Variable)) : Variable → HomContext Hom :=
  fun index =>
    ⟨(tree.language (fun label => decide (index ∈ label))).image List.reverse⟩

@[simp]
theorem mem_paths_finset_sum
    {Index Hom : Type u} [DecidableEq Index] [Encodable Hom]
    (indices : Finset Index) (contexts : Index → HomContext Hom)
    (path : List Hom) :
    path ∈ (∑ index ∈ indices, contexts index).paths ↔
      ∃ index ∈ indices, path ∈ (contexts index).paths := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices fresh inductionHypothesis =>
      simp [Finset.sum_insert fresh, inductionHypothesis]

theorem variableCoefficient_path_length_le_pathBound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (side : Bool) (row : Row) (index : Variable)
    {path : List Hom}
    (membership : path ∈
      (problem.coefficient side row index).paths) :
    path.length ≤ problem.pathBound := by
  cases side with
  | false =>
      exact problem.coefficient_path_length_le_pathBound false row index membership
  | true =>
      exact problem.coefficient_path_length_le_pathBound true row index membership

theorem constantCoefficient_path_length_le_pathBound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (side : Bool) (row : Row) {path : List Hom}
    (membership : path ∈
      (problem.constant side row).paths) :
    path.length ≤ problem.pathBound := by
  cases side with
  | false =>
      exact problem.constant_path_length_le_pathBound false row membership
  | true =>
      exact problem.constant_path_length_le_pathBound true row membership

/-- At the initial state, the direct mirrored output language is exactly the
reverse of the ordinary coefficient-first matrix evaluation. -/
theorem mem_evaluated_initial_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (tree : Tree Hom (VariableLabel Variable))
    (row : Row) (side : Bool) (word : List Hom) :
    word ∈ evaluatedOutputs problem
        (initialPendingState problem) tree row side ↔
      word.reverse ∈
        ((∑ index,
            problem.coefficient side row index *
              decodeVariableLanguages tree index) +
          problem.constant side row).paths := by
  rw [mem_evaluatedOutputs_iff]
  simp only [HomContext.mem_add, mem_paths_finset_sum,
    Finset.mem_univ, true_and, HomContext.mem_mul]
  constructor
  · rintro (⟨pending, pendingMembership, pendingValue⟩ |
        ⟨index, assignmentPath, coefficient, assignmentMembership,
          coefficientMembership, generatedValue⟩)
    · apply Or.inr
      have selected := (mem_constantCoefficientWords_iff
        problem side row pending).mp (by
          change pending ∈ constantCoefficientWords problem side row at pendingMembership
          exact pendingMembership)
      simpa [pendingValue] using selected
    · apply Or.inl
      refine ⟨index, coefficient.1.reverse, ?_, assignmentPath.reverse, ?_, ?_⟩
      · exact (mem_variableCoefficientWords_iff
          problem side row index coefficient).mp coefficientMembership
      · exact Finset.mem_image.mpr ⟨assignmentPath,
          assignmentMembership, rfl⟩
      · simpa [List.reverse_append] using congrArg List.reverse generatedValue
  · rintro (⟨index, coefficientPath, coefficientMembership,
          valuePath, valueMembership, generatedValue⟩ |
        constantMembership)
    · rcases Finset.mem_image.mp valueMembership with
        ⟨assignmentPath, assignmentMembership, valuePathEquality⟩
      subst valuePath
      let coefficient : PendingWord problem :=
        BoundedWord.reverseOf coefficientPath
          (variableCoefficient_path_length_le_pathBound
            problem side row index coefficientMembership)
      apply Or.inr
      refine ⟨index, assignmentPath, coefficient, assignmentMembership, ?_, ?_⟩
      · apply (mem_variableCoefficientWords_iff
          problem side row index coefficient).mpr
        simpa [coefficient, BoundedWord.reverseOf]
      · have reversed := congrArg List.reverse generatedValue
        simpa [coefficient, BoundedWord.reverseOf, List.reverse_append] using reversed
    · have wordBound : word.length ≤ problem.pathBound := by
        simpa using constantCoefficient_path_length_le_pathBound
          problem side row constantMembership
      let pending : PendingWord problem :=
        ⟨word, (mem_wordsUpTo_iff _ _).mpr wordBound⟩
      apply Or.inl
      refine ⟨pending, ?_, ?_⟩
      · change pending ∈ constantCoefficientWords problem side row
        apply (mem_constantCoefficientWords_iff
          problem side row pending).mpr
        simpa [pending]
      · rfl

/-- A candidate tree stops only after every pending coefficient suffix has
been consumed. -/
def PendingWordsTerminate
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (state : PendingState problem) :
    Tree Hom (VariableLabel Variable) → Prop
  | .leaf label => ∀ row side word,
      word ∈ activePendingWords problem state label row side →
        word.1 = []
  | .node label children => ∀ branch,
      PendingWordsTerminate problem
        ((finiteLanguageAutomaton problem).next state label branch)
        (children branch)

/-- A complete tree whose outputs fit below its depth necessarily consumes
all pending suffixes before its leaves. -/
theorem pendingWordsTerminate_completeAt_of_length_le
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (labelAt : List Hom → VariableLabel Variable)
    (depth : Nat) (pathPrefix : List Hom)
    (state : PendingState problem)
    (bounded : ∀ row side word,
      word ∈ generatedOutputs problem state row side
        (Tree.completeAt labelAt depth pathPrefix) →
      word.length ≤ depth) :
    PendingWordsTerminate problem state
      (Tree.completeAt labelAt depth pathPrefix) := by
  induction depth generalizing pathPrefix state with
  | zero =>
      intro row side word membership
      apply List.length_eq_zero_iff.mp
      have lengthBound := bounded row side word.1
        (active_value_mem_generatedOutputs problem state
          (.leaf (labelAt pathPrefix)) row side word membership)
      omega
  | succ depth inductionHypothesis =>
      intro branch
      apply inductionHypothesis (pathPrefix ++ [branch])
      intro row side word membership
      have parentMembership : branch :: word ∈
          generatedOutputs problem state row side
            (Tree.completeAt labelAt (depth + 1) pathPrefix) := by
        apply (cons_mem_generatedOutputs_node_iff problem state
          (labelAt pathPrefix)
          (fun selected => Tree.completeAt labelAt depth
            (pathPrefix ++ [selected])) row side branch word).mpr
        exact membership
      have parentBound := bounded row side (branch :: word) parentMembership
      simpa using parentBound

/-- Output-language inclusion and proper leaf termination are sufficient for
automaton acceptance. -/
theorem finiteLanguageAutomaton_accepts_of_generated_subset
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (state : PendingState problem)
    (tree : Tree Hom (VariableLabel Variable))
    (included : ∀ row,
      generatedOutputs problem state row false tree ⊆
        generatedOutputs problem state row true tree)
    (terminates : PendingWordsTerminate problem state tree) :
    (finiteLanguageAutomaton problem).Accepts state tree := by
  induction tree generalizing state with
  | leaf label =>
      apply Automaton.Accepts.leaf
      · simp only [finiteLanguageAutomaton, decide_eq_true_eq]
        intro row endpoint
        apply (nil_mem_generatedOutputs_iff problem state
          (.leaf label) row true).mp
        apply included row
        exact (nil_mem_generatedOutputs_iff problem state
          (.leaf label) row false).mpr endpoint
      · simpa [finiteLanguageAutomaton, PendingWordsTerminate] using terminates
  | node label children inductionHypothesis =>
      apply Automaton.Accepts.node
      · simp only [finiteLanguageAutomaton, decide_eq_true_eq]
        intro row endpoint
        apply (nil_mem_generatedOutputs_iff problem state
          (.node label children) row true).mp
        apply included row
        exact (nil_mem_generatedOutputs_iff problem state
          (.node label children) row false).mpr endpoint
      · intro branch
        apply inductionHypothesis branch
        · intro row word membership
          apply (cons_mem_generatedOutputs_node_iff problem state
            label children row true branch word).mp
          apply included row
          exact (cons_mem_generatedOutputs_node_iff problem state
            label children row false branch word).mpr membership
        · exact terminates branch

/-- Every accepted tree decodes to a genuine solution of the original
unbounded finite-language system. -/
theorem finiteLanguageAutomaton_accepts_sound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (tree : Tree Hom (VariableLabel Variable))
    (accepted : (finiteLanguageAutomaton problem).Accepts
      (initialPendingState problem) tree) :
    problem.IsSolution (decodeVariableLanguages tree) := by
  intro row
  apply (HomContext.le_iff_paths_subset _ _).mpr
  intro path pathMembership
  let word := path.reverse
  have leftExpected : word ∈ evaluatedOutputs problem
      (initialPendingState problem) tree row false :=
    (mem_evaluated_initial_iff problem tree row false word).mpr (by
      simpa only [FiniteLanguageSystem.evaluate, word,
        List.reverse_reverse] using pathMembership)
  have leftOutput : word ∈ generatedOutputs problem
      (initialPendingState problem) row false tree := by
    rw [generatedOutputs_eq_evaluatedOutputs]
    exact leftExpected
  have rightOutput :=
    finiteLanguageAutomaton_accepts_generated_subset problem
      (initialPendingState problem) tree accepted row leftOutput
  have rightExpected : word ∈ evaluatedOutputs problem
      (initialPendingState problem) tree row true := by
    rw [← generatedOutputs_eq_evaluatedOutputs]
    exact rightOutput
  have rightPath :=
    (mem_evaluated_initial_iff problem tree row true word).mp rightExpected
  change word.reverse ∈
    ((∑ index, problem.coefficient true row index * decodeVariableLanguages tree index) +
      problem.constant true row).paths at rightPath
  simpa only [FiniteLanguageSystem.evaluate, word,
    List.reverse_reverse] using rightPath

end ACUIHE.Solver.Search
