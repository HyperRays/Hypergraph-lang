import ACUIHE.Optimized.Optimized.FiniteLanguageSystem
import ACUIHE.Solver.Search.ColumnAutomaton

set_option linter.dupNamespace false

/-! Optimized finite-language search exposed through the ACUIh column API. -/

namespace ACUIHE.Optimized.Optimized

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

/-- Exact search for one ACUIh matrix column. -/
def solveColumn?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (shallowBound : Nat := 8) :
    Option (Variable → HomContext Hom) :=
  solveFiniteLanguage? (matrixColumnSystem left right basis) shallowBound

theorem solveColumn?_sound
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (shallowBound : Nat := 8)
    {values : Variable → HomContext Hom}
    (found : solveColumn? left right basis shallowBound = some values) :
    columnRepresentationBelow left right basis values := by
  apply (matrixColumnSystem_isSolution_iff left right basis values).mp
  exact solveFiniteLanguage?_sound
    (matrixColumnSystem left right basis) shallowBound found

theorem solveColumn?_complete
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (shallowBound : Nat := 8)
    (solution : ∃ values : Variable → HomContext Hom,
      columnRepresentationBelow left right basis values) :
    ∃ values, solveColumn? left right basis shallowBound = some values := by
  have genericSolution :
      ∃ values : Variable → HomContext Hom,
        (matrixColumnSystem left right basis).IsSolution values := by
    rcases solution with ⟨values, solved⟩
    exact ⟨values,
      (matrixColumnSystem_isSolution_iff left right basis values).mpr solved⟩
  exact solveFiniteLanguage?_complete
    (matrixColumnSystem left right basis) shallowBound genericSolution

/-- One memoized basis column. -/
abbrev CachedColumn (Variable Basis Hom : Type u) :=
  Basis × (Variable → HomContext Hom)

/-- Look up an already solved column. -/
def lookupColumn? [DecidableEq Basis]
    (entries : List (CachedColumn Variable Basis Hom))
    (basis : Basis) : Option (Variable → HomContext Hom) :=
  match entries with
  | [] => none
  | (storedBasis, column) :: rest =>
      if storedBasis = basis then some column else lookupColumn? rest basis

/-- Solve a list of columns exactly once, threading the successful results
into an immutable memo table. -/
def solveColumnEntries?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (shallowBound : Nat) :
    List Basis → Option (List (CachedColumn Variable Basis Hom))
  | [] => some []
  | basis :: rest => do
      let column ← solveColumn? (representations basis).1
        (representations basis).2 basis shallowBound
      let entries ← solveColumnEntries? representations shallowBound rest
      some ((basis, column) :: entries)

theorem solveColumnEntries?_lookup_sound
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable]
    [FinEnum Hom] [Encodable Hom] [DecidableEq Basis]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (shallowBound : Nat) (candidates : List Basis)
    {entries : List (CachedColumn Variable Basis Hom)}
    (solved : solveColumnEntries? representations shallowBound candidates =
      some entries)
    {basis : Basis} {column : Variable → HomContext Hom}
    (cached : lookupColumn? entries basis = some column) :
    solveColumn? (representations basis).1
      (representations basis).2 basis shallowBound = some column := by
  induction candidates generalizing entries basis column with
  | nil => simp [solveColumnEntries?] at solved; simp [solved, lookupColumn?] at cached
  | cons head tail inductionHypothesis =>
      simp only [solveColumnEntries?] at solved
      cases headResult : solveColumn? (representations head).1
          (representations head).2 head shallowBound with
      | none => simp [headResult] at solved
      | some headColumn =>
          cases tailResult : solveColumnEntries? representations shallowBound tail with
          | none => simp [headResult, tailResult] at solved
          | some tailEntries =>
              simp [headResult, tailResult] at solved
              subst entries
              by_cases equality : head = basis
              · subst head
                simp [lookupColumn?] at cached
                subst column
                exact headResult
              · simp [lookupColumn?, equality] at cached
                exact inductionHypothesis tailResult cached

theorem solveColumnEntries?_lookup_complete
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable]
    [FinEnum Hom] [Encodable Hom] [DecidableEq Basis]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (shallowBound : Nat) (candidates : List Basis)
    {entries : List (CachedColumn Variable Basis Hom)}
    (solved : solveColumnEntries? representations shallowBound candidates =
      some entries)
    {basis : Basis} (membership : basis ∈ candidates) :
    (lookupColumn? entries basis).isSome := by
  induction candidates generalizing entries with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [solveColumnEntries?] at solved
      cases headResult : solveColumn? (representations head).1
          (representations head).2 head shallowBound with
      | none => simp [headResult] at solved
      | some headColumn =>
          cases tailResult : solveColumnEntries? representations shallowBound tail with
          | none => simp [headResult, tailResult] at solved
          | some tailEntries =>
              simp [headResult, tailResult] at solved
              subst entries
              rcases List.mem_cons.mp membership with equality | inTail
              · subst head
                simp [lookupColumn?]
              · by_cases equality : head = basis
                · subst head
                  simp [lookupColumn?]
                · simp [lookupColumn?, equality,
                    inductionHypothesis tailResult inTail]

theorem solveColumnEntries?_complete
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (shallowBound : Nat) (candidates : List Basis)
    (solvable : ∀ basis ∈ candidates,
      ∃ column, solveColumn? (representations basis).1
        (representations basis).2 basis shallowBound = some column) :
    ∃ entries, solveColumnEntries? representations shallowBound candidates =
      some entries := by
  induction candidates with
  | nil => exact ⟨[], rfl⟩
  | cons head tail inductionHypothesis =>
      rcases solvable head (by simp) with ⟨headColumn, headFound⟩
      rcases inductionHypothesis (fun basis membership =>
          solvable basis (by simp [membership])) with ⟨tailEntries, tailFound⟩
      exact ⟨(head, headColumn) :: tailEntries,
        by simp [solveColumnEntries?, headFound, tailFound]⟩

/-- Interpret the memo table as a matrix.  The zero branch is unreachable for
tables produced from `FinEnum.toList Basis`; keeping it explicit avoids
embedding proof terms in the runtime representation. -/
def cachedColumnMatrix [DecidableEq Basis]
    (entries : List (CachedColumn Variable Basis Hom)) :
    Matrix Variable Basis (HomContext Hom) :=
  fun index basis =>
    match lookupColumn? entries basis with
    | some column => column index
    | none => 0

/-- Solve each independently decomposed basis column once and retain all
results in a configuration-local memo table. -/
def solveColumnFamily?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (shallowBound : Nat := 8) :
    Option (Matrix Variable Basis (HomContext Hom)) := do
  let entries ← solveColumnEntries? representations shallowBound
    (FinEnum.toList Basis)
  some (cachedColumnMatrix entries)

theorem solveColumnFamily?_sound
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (shallowBound : Nat := 8)
    {values : Matrix Variable Basis (HomContext Hom)}
    (found : solveColumnFamily? representations shallowBound = some values) :
    ∀ row basis,
      evaluateMatrixRepresentation (representations basis).1 values row basis ≤
        evaluateMatrixRepresentation (representations basis).2 values row basis := by
  unfold solveColumnFamily? at found
  cases entriesResult : solveColumnEntries? representations shallowBound
      (FinEnum.toList Basis) with
  | none => simp [entriesResult] at found
  | some entries =>
      simp [entriesResult] at found
      subst values
      intro row basis
      have cachedSome : (lookupColumn? entries basis).isSome :=
        solveColumnEntries?_lookup_complete representations shallowBound
          (FinEnum.toList Basis) entriesResult (FinEnum.mem_toList basis)
      cases lookupResult : lookupColumn? entries basis with
      | none => simp [lookupResult] at cachedSome
      | some column =>
          have columnFound := solveColumnEntries?_lookup_sound
            representations shallowBound (FinEnum.toList Basis)
            entriesResult lookupResult
          simpa [cachedColumnMatrix, lookupResult] using
            solveColumn?_sound (representations basis).1
              (representations basis).2 basis shallowBound columnFound row

theorem solveColumnFamily?_complete
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (shallowBound : Nat := 8)
    (solution : ∃ values : Matrix Variable Basis (HomContext Hom),
      ∀ row basis,
        evaluateMatrixRepresentation (representations basis).1 values row basis ≤
          evaluateMatrixRepresentation (representations basis).2 values row basis) :
    ∃ values, solveColumnFamily? representations shallowBound = some values := by
  rcases solution with ⟨values, solved⟩
  have columnSolvable : ∀ basis ∈ FinEnum.toList Basis,
      ∃ column, solveColumn? (representations basis).1
        (representations basis).2 basis shallowBound = some column := by
    intro basis _
    rcases solveColumn?_complete (representations basis).1
        (representations basis).2 basis shallowBound
        ⟨fun index => values index basis, fun row => solved row basis⟩ with
      ⟨column, found⟩
    exact ⟨column, found⟩
  rcases solveColumnEntries?_complete representations shallowBound
      (FinEnum.toList Basis) columnSolvable with ⟨entries, entriesFound⟩
  exact ⟨cachedColumnMatrix entries,
    by simp [solveColumnFamily?, entriesFound]⟩

end ACUIHE.Optimized.Optimized
