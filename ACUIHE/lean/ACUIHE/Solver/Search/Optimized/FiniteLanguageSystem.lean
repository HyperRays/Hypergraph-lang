import ACUIHE.Solver.Search.Optimized.Automaton
import ACUIHE.Solver.Search.FiniteLanguageSystem.Completeness

/-! The finite-language adapter for the separate optimized automaton solver. -/

namespace ACUIHE.Solver.Search.Optimized

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

/-- Exact finite-language search using shallow-first search followed by
reachable-state saturation. -/
def solveFiniteLanguage?
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shallowBound : Nat := 8) : Option (Variable → HomContext Hom) :=
  (Automaton.solve? (finiteLanguageAutomaton problem)
    (initialPendingState problem) shallowBound).map decodeVariableLanguages

theorem solveFiniteLanguage?_sound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shallowBound : Nat := 8) {values : Variable → HomContext Hom}
    (found : solveFiniteLanguage? problem shallowBound = some values) :
    problem.IsSolution values := by
  unfold solveFiniteLanguage? at found
  cases treeResult : Automaton.solve? (finiteLanguageAutomaton problem)
      (initialPendingState problem) shallowBound with
  | none => simp [treeResult] at found
  | some tree =>
      simp only [treeResult, Option.map_some] at found
      cases found
      apply finiteLanguageAutomaton_accepts_sound
      exact Automaton.solve?_sound (finiteLanguageAutomaton problem)
        (initialPendingState problem) shallowBound treeResult

theorem solveFiniteLanguage?_complete
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shallowBound : Nat := 8)
    (solution : ∃ values : Variable → HomContext Hom,
      problem.IsSolution values) :
    ∃ values, solveFiniteLanguage? problem shallowBound = some values := by
  rcases solution with ⟨values, solved⟩
  have accepted : ∃ tree,
      (finiteLanguageAutomaton problem).Accepts
        (initialPendingState problem) tree :=
    ⟨encodeVariableLanguages problem values,
      finiteLanguageAutomaton_accepts_complete problem values solved⟩
  rcases Automaton.solve?_complete (finiteLanguageAutomaton problem)
      (initialPendingState problem) shallowBound accepted with ⟨tree, found⟩
  exact ⟨decodeVariableLanguages tree, by simp [solveFiniteLanguage?, found]⟩

theorem solveFiniteLanguage?_eq_none_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shallowBound : Nat := 8) :
    solveFiniteLanguage? problem shallowBound = none ↔
      ¬ ∃ values : Variable → HomContext Hom, problem.IsSolution values := by
  constructor
  · intro failed solution
    rcases solveFiniteLanguage?_complete problem shallowBound solution with
      ⟨values, found⟩
    rw [failed] at found
    contradiction
  · intro rejected
    cases found : solveFiniteLanguage? problem shallowBound with
    | none => rfl
    | some values =>
        exact False.elim (rejected ⟨values,
          solveFiniteLanguage?_sound problem shallowBound found⟩)

end ACUIHE.Solver.Search.Optimized
