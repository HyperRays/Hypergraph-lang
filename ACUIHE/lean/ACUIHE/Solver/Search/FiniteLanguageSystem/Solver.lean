import ACUIHE.Solver.Search.FiniteLanguageSystem.Completeness

/-!
Exact search and decision theorems for finite-language inequality systems.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u

attribute [local instance]
  finiteLanguageDecidableEq finiteLanguageBoolFinEnum

namespace FiniteLanguageSystem

/-- Exact, total search for one finite-language system. The only internal
height is the proved finite-state saturation bound. -/
def solve?
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) : Option (Variable → HomContext Hom) :=
  ((finiteLanguageAutomaton problem).solve?
    (initialPendingState problem)).map decodeVariableLanguages

/-- Any assignment returned by search satisfies every input row. -/
theorem solve?_sound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) {values : Variable → HomContext Hom}
    (result : problem.solve? = some values) :
    problem.IsSolution values := by
  unfold solve? at result
  cases found : (finiteLanguageAutomaton problem).solve?
      (initialPendingState problem) with
  | none => simp [found] at result
  | some tree =>
      simp only [found, Option.map_some] at result
      cases result
      apply finiteLanguageAutomaton_accepts_sound
      exact (finiteLanguageAutomaton problem).solve?_sound
        (initialPendingState problem) found

/-- Every finite-language solution is found; there is no caller-selected
search cutoff or completeness side condition. -/
theorem solve?_complete
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (solution : ∃ values : Variable → HomContext Hom,
      problem.IsSolution values) :
    ∃ values, problem.solve? = some values := by
  rcases solution with ⟨values, solved⟩
  have accepted : ∃ tree,
      (finiteLanguageAutomaton problem).Accepts
        (initialPendingState problem) tree :=
    ⟨encodeVariableLanguages problem values,
      finiteLanguageAutomaton_accepts_complete problem values solved⟩
  rcases (finiteLanguageAutomaton problem).solve?_complete
      (initialPendingState problem) accepted with ⟨tree, found⟩
  exact ⟨decodeVariableLanguages tree, by simp [solve?, found]⟩

/-- Search failure is equivalent to genuine unsatisfiability. -/
theorem solve?_eq_none_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :
    problem.solve? = none ↔
      ¬ ∃ values : Variable → HomContext Hom,
        problem.IsSolution values := by
  constructor
  · intro failed solution
    rcases problem.solve?_complete solution with ⟨values, found⟩
    rw [failed] at found
    contradiction
  · intro unsatisfiable
    cases found : problem.solve? with
    | none => rfl
    | some values =>
        exact False.elim (unsatisfiable ⟨values,
          problem.solve?_sound found⟩)

end FiniteLanguageSystem

end ACUIHE.Solver.Search
