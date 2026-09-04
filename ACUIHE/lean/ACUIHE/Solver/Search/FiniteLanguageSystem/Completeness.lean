import ACUIHE.Solver.Search.FiniteLanguageSystem.Soundness

/-!
Encoding finite-language assignments and proving automaton completeness.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u

attribute [local instance]
  finiteLanguageDecidableEq finiteLanguageBoolFinEnum

/-- Maximum path length in a concrete finite-language assignment. -/
def valuesPathBound
    {Variable Hom : Type u} [FinEnum Variable] [Encodable Hom]
    (values : Variable → HomContext Hom) : Nat :=
  Finset.univ.sup fun index => contextPathBound (values index)

theorem value_path_length_le_valuesPathBound
    {Variable Hom : Type u} [FinEnum Variable] [Encodable Hom]
    (values : Variable → HomContext Hom) (index : Variable)
    {path : List Hom} (membership : path ∈ (values index).paths) :
    path.length ≤ valuesPathBound values := by
  apply le_trans (path_length_le_contextPathBound _ membership)
  exact Finset.le_sup (s := Finset.univ)
    (f := fun selected => contextPathBound (values selected))
    (Finset.mem_univ index)

/-- Label a mirrored path by exactly the variables whose assigned language
contains the corresponding ordinary path. -/
def variableLanguageLabel
    {Variable Hom : Type u} [FinEnum Variable] [Encodable Hom]
    (values : Variable → HomContext Hom) (mirroredPath : List Hom) :
    VariableLabel Variable :=
  Finset.univ.filter fun index => mirroredPath.reverse ∈ (values index).paths

/-- A finite complete tree that represents a supplied assignment and is deep
enough to consume every input coefficient. -/
def encodeVariableLanguages
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (values : Variable → HomContext Hom) :
    Tree Hom (VariableLabel Variable) :=
  Tree.completeAt (variableLanguageLabel values)
    (valuesPathBound values + problem.pathBound) []

/-- Encoding and decoding a concrete assignment loses no paths. -/
theorem decode_encodeVariableLanguages
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (values : Variable → HomContext Hom) :
    decodeVariableLanguages (encodeVariableLanguages problem values) = values := by
  funext index
  apply HomContext.ext
  ext path
  simp [decodeVariableLanguages, encodeVariableLanguages, variableLanguageLabel]
  constructor
  · aesop
  · intro membership
    refine ⟨path.reverse, ?_, by simp⟩
    refine ⟨?_, by simpa using membership⟩
    have bounded := value_path_length_le_valuesPathBound
      values index membership
    simpa using le_trans bounded (Nat.le_add_right _ _)

theorem encodeVariableLanguages_generated_length_le
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (values : Variable → HomContext Hom)
    (row : Row) (side : Bool) (word : List Hom)
    (membership : word ∈ generatedOutputs problem
      (initialPendingState problem) row side
      (encodeVariableLanguages problem values)) :
    word.length ≤
      valuesPathBound values + problem.pathBound := by
  rw [generatedOutputs_eq_evaluatedOutputs, mem_evaluatedOutputs_iff] at membership
  rcases membership with
    ⟨pending, pendingMembership, pendingValue⟩ |
      ⟨index, assignmentPath, coefficient, assignmentMembership,
        coefficientMembership, generatedValue⟩
  · have constantMembership := (mem_constantCoefficientWords_iff
      problem side row pending).mp (by
        change pending ∈ constantCoefficientWords problem side row at pendingMembership
        exact pendingMembership)
    have coefficientBound := constantCoefficient_path_length_le_pathBound
      problem side row constantMembership
    rw [← pendingValue]
    simpa using le_trans (by simpa using coefficientBound)
      (Nat.le_add_left _ _)
  · have languageFacts := (Tree.mem_language_completeAt_iff
      (variableLanguageLabel values)
      (fun label => decide (index ∈ label))
      (valuesPathBound values + problem.pathBound)
      [] assignmentPath).mp assignmentMembership
    have selected : index ∈ variableLanguageLabel values assignmentPath := by
      exact of_decide_eq_true (by simpa using languageFacts.2)
    have valueMembership : assignmentPath.reverse ∈ (values index).paths := by
      simpa [variableLanguageLabel] using selected
    have assignmentBound := value_path_length_le_valuesPathBound
      values index valueMembership
    have coefficientBound := (mem_wordsUpTo_iff _ coefficient.1).mp coefficient.2
    rw [← generatedValue, List.length_append]
    exact Nat.add_le_add (by simpa using assignmentBound) coefficientBound

theorem encodeVariableLanguages_terminate
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (values : Variable → HomContext Hom) :
    PendingWordsTerminate problem (initialPendingState problem)
      (encodeVariableLanguages problem values) := by
  apply pendingWordsTerminate_completeAt_of_length_le
  intro row side word membership
  exact encodeVariableLanguages_generated_length_le
    problem values row side word membership

theorem encodeVariableLanguages_generated_subset
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (values : Variable → HomContext Hom)
    (solution : problem.IsSolution values)
    (row : Row) :
    generatedOutputs problem (initialPendingState problem)
        row false (encodeVariableLanguages problem values) ⊆
      generatedOutputs problem (initialPendingState problem)
        row true (encodeVariableLanguages problem values) := by
  intro word membership
  rw [generatedOutputs_eq_evaluatedOutputs] at membership ⊢
  have leftPath := (mem_evaluated_initial_iff problem
    (encodeVariableLanguages problem values) row false word).mp membership
  change word.reverse ∈
    ((∑ index, problem.coefficient false row index *
      decodeVariableLanguages (encodeVariableLanguages problem values) index) +
      problem.constant false row).paths at leftPath
  rw [decode_encodeVariableLanguages problem values] at leftPath
  have rightPath := (HomContext.le_iff_paths_subset _ _).mp
    (solution row) leftPath
  apply (mem_evaluated_initial_iff problem
    (encodeVariableLanguages problem values) row true word).mpr
  rwa [decode_encodeVariableLanguages problem values]

/-- Every finite-language solution is represented by an accepted tree. -/
theorem finiteLanguageAutomaton_accepts_complete
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (values : Variable → HomContext Hom)
    (solution : problem.IsSolution values) :
    (finiteLanguageAutomaton problem).Accepts
      (initialPendingState problem)
      (encodeVariableLanguages problem values) := by
  apply finiteLanguageAutomaton_accepts_of_generated_subset
  · exact encodeVariableLanguages_generated_subset problem values solution
  · exact encodeVariableLanguages_terminate problem values

end ACUIHE.Solver.Search
