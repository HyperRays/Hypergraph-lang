import ACUIHE.Optimized.Optimized.Automaton
import ACUIHE.Solver.Search.FiniteLanguageSystem.Completeness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

set_option linter.dupNamespace false

/-! The finite-language adapter for the separate optimized automaton solver. -/

namespace ACUIHE.Optimized.Optimized

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

/--
The exact cardinality of the pending-state type, computed compositionally.

Writing this as powers is crucial.  `FinEnum.card (PendingState problem)` uses
the generic function-space `FinEnum`, which first materializes every function
and then deduplicates the resulting list.  Pending states are functions from
rows and sides to finite sets, so that implementation is already exponential
before the fixed-point solver performs its first step.
-/
def pendingStateCard
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) : Nat :=
  ((2 ^ FinEnum.card (PendingWord problem)) ^ 2) ^ FinEnum.card Row

theorem pendingStateCard_eq
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :
    pendingStateCard problem = FinEnum.card (PendingState problem) := by
  unfold pendingStateCard
  rw [FinEnum.card_eq_fintypeCard (α := PendingState problem)]
  simp only [Fintype.card_fun, Fintype.card_finset, Fintype.card_bool]
  rw [← FinEnum.card_eq_fintypeCard (α := PendingWord problem)]
  rw [← FinEnum.card_eq_fintypeCard (α := Row)]

/-- Exact finite-language search using shallow-first search followed by
reachable-state saturation. -/
def solveFiniteLanguage?
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shallowBound : Nat := 8) : Option (Variable → HomContext Hom) :=
  (Automaton.solveWithCardAndBranchShortcut? (finiteLanguageAutomaton problem)
    (initialPendingState problem) (pendingStateCard problem)
    (pendingStateCard_eq problem) shallowBound).map decodeVariableLanguages

theorem solveFiniteLanguage?_sound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shallowBound : Nat := 8) {values : Variable → HomContext Hom}
    (found : solveFiniteLanguage? problem shallowBound = some values) :
    problem.IsSolution values := by
  unfold solveFiniteLanguage? at found
  cases treeResult : Automaton.solveWithCardAndBranchShortcut?
      (finiteLanguageAutomaton problem)
      (initialPendingState problem) (pendingStateCard problem)
      (pendingStateCard_eq problem) shallowBound with
  | none => simp [treeResult] at found
  | some tree =>
      simp only [treeResult, Option.map_some] at found
      cases found
      apply finiteLanguageAutomaton_accepts_sound
      exact Automaton.solveWithCardAndBranchShortcut?_sound
        (finiteLanguageAutomaton problem)
        (initialPendingState problem) (pendingStateCard problem)
        (pendingStateCard_eq problem) shallowBound treeResult

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
  rcases Automaton.solveWithCardAndBranchShortcut?_complete
      (finiteLanguageAutomaton problem)
      (initialPendingState problem) (pendingStateCard problem)
      (pendingStateCard_eq problem) shallowBound accepted with ⟨tree, found⟩
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

end ACUIHE.Optimized.Optimized
