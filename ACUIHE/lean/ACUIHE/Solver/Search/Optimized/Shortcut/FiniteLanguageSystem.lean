import ACUIHE.Solver.Search.Optimized.Shortcut.Automaton
import ACUIHE.Solver.Search.FiniteLanguageSystem.Completeness

/-! The finite-language adapter for witness-carrying shortcut saturation. -/

namespace ACUIHE.Solver.Search.Optimized.Shortcut

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

/-- Exact finite-language search whose saturation table stores the accepted
subtree for every resolved state. -/
def solveFiniteLanguage?
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Option (Variable → HomContext Hom) :=
  (solve? (finiteLanguageAutomaton problem)
    (initialPendingState problem)).map decodeVariableLanguages

theorem solveFiniteLanguage?_sound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    {values : Variable → HomContext Hom}
    (found : solveFiniteLanguage? problem = some values) :
    problem.IsSolution values := by
  unfold solveFiniteLanguage? at found
  cases treeResult : solve? (finiteLanguageAutomaton problem)
      (initialPendingState problem) with
  | none => simp [treeResult] at found
  | some tree =>
      simp only [treeResult, Option.map_some] at found
      cases found
      apply finiteLanguageAutomaton_accepts_sound
      exact solve?_sound (finiteLanguageAutomaton problem)
        (initialPendingState problem) treeResult

theorem solveFiniteLanguage?_complete
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (solution : ∃ values : Variable → HomContext Hom,
      problem.IsSolution values) :
    ∃ values, solveFiniteLanguage? problem = some values := by
  rcases solution with ⟨values, solved⟩
  have accepted : ∃ tree,
      (finiteLanguageAutomaton problem).Accepts
        (initialPendingState problem) tree :=
    ⟨encodeVariableLanguages problem values,
      finiteLanguageAutomaton_accepts_complete problem values solved⟩
  rcases solve?_complete (finiteLanguageAutomaton problem)
      (initialPendingState problem) accepted with ⟨tree, found⟩
  exact ⟨decodeVariableLanguages tree,
    by simp [solveFiniteLanguage?, found]⟩

theorem solveFiniteLanguage?_eq_none_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :
    solveFiniteLanguage? problem = none ↔
      ¬ ∃ values : Variable → HomContext Hom, problem.IsSolution values := by
  constructor
  · intro failed solution
    rcases solveFiniteLanguage?_complete problem solution with
      ⟨values, found⟩
    rw [failed] at found
    contradiction
  · intro rejected
    cases found : solveFiniteLanguage? problem with
    | none => rfl
    | some values =>
        exact False.elim (rejected ⟨values,
          solveFiniteLanguage?_sound problem found⟩)

end ACUIHE.Solver.Search.Optimized.Shortcut
