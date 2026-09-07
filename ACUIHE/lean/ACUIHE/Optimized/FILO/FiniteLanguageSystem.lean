import ACUIHE.Optimized.FILO.Saturation

/-! Public, exact finite-language API for the FILO backend. -/

namespace ACUIHE.Optimized.FILO

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

/-- Solve a finite-language inequality system by exact FILO shortcut search.
There is no public depth or fuel parameter. -/
def solveFiniteLanguage?
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Option (Variable → HomContext Hom) :=
  problem.saturateRootFast?.map FiniteLanguageSystem.decode

theorem solveFiniteLanguage?_sound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    {values : Variable → HomContext Hom}
    (found : solveFiniteLanguage? problem = some values) :
    problem.IsSolution values := by
  unfold solveFiniteLanguage? at found
  cases treeResult : problem.saturateRootFast? with
  | none => simp [treeResult] at found
  | some tree =>
      simp only [treeResult, Option.map_some] at found
      have valuesEquality : FiniteLanguageSystem.decode tree = values :=
        Option.some.inj found
      have certified := problem.saturateRootFast?_sound treeResult
      rw [← valuesEquality]
      exact certified.2.decode_isSolution problem tree certified.1

theorem solveFiniteLanguage?_complete
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (solution : ∃ values : Variable → HomContext Hom,
      problem.IsSolution values) :
    ∃ values, solveFiniteLanguage? problem = some values := by
  rcases solution with ⟨values, solved⟩
  rcases problem.saturateRootFast?_complete values solved with ⟨tree, found⟩
  exact ⟨FiniteLanguageSystem.decode tree, by
    simp [solveFiniteLanguage?, found]⟩

theorem solveFiniteLanguage?_eq_none_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :
    solveFiniteLanguage? problem = none ↔
      ¬ ∃ values : Variable → HomContext Hom, problem.IsSolution values := by
  constructor
  · intro failed solution
    rcases solveFiniteLanguage?_complete problem solution with ⟨values, found⟩
    rw [failed] at found
    contradiction
  · intro rejected
    cases found : solveFiniteLanguage? problem with
    | none => rfl
    | some values =>
        exact False.elim (rejected ⟨values,
          solveFiniteLanguage?_sound problem found⟩)

end ACUIHE.Optimized.FILO
