import ACUIHE.Solver.Search.Optimized.Shortcut.FiniteLanguageSystem
import ACUIHE.Solver.Search.ColumnAutomaton

/-! Shortcut saturation exposed through the ACUIh column decomposition. -/

namespace ACUIHE.Solver.Search.Optimized.Shortcut

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

/-- Exact shortcut search for one ACUIh matrix column. -/
def solveColumn?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) : Option (Variable → HomContext Hom) :=
  solveFiniteLanguage? (matrixColumnSystem left right basis)

theorem solveColumn?_sound
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) {values : Variable → HomContext Hom}
    (found : solveColumn? left right basis = some values) :
    columnRepresentationBelow left right basis values := by
  apply (matrixColumnSystem_isSolution_iff left right basis values).mp
  exact solveFiniteLanguage?_sound
    (matrixColumnSystem left right basis) found

theorem solveColumn?_complete
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis)
    (solution : ∃ values : Variable → HomContext Hom,
      columnRepresentationBelow left right basis values) :
    ∃ values, solveColumn? left right basis = some values := by
  have genericSolution :
      ∃ values : Variable → HomContext Hom,
        (matrixColumnSystem left right basis).IsSolution values := by
    rcases solution with ⟨values, solved⟩
    exact ⟨values,
      (matrixColumnSystem_isSolution_iff left right basis values).mpr solved⟩
  exact solveFiniteLanguage?_complete
    (matrixColumnSystem left right basis) genericSolution

/-- One memoized basis-column result. -/
abbrev CachedColumn (Variable Basis Hom : Type u) :=
  Basis × (Variable → HomContext Hom)

def lookupColumn? [DecidableEq Basis]
    (entries : List (CachedColumn Variable Basis Hom))
    (basis : Basis) : Option (Variable → HomContext Hom) :=
  match entries with
  | [] => none
  | (storedBasis, column) :: rest =>
      if storedBasis = basis then some column else lookupColumn? rest basis

/-- Solve each requested column once and retain its witness. -/
def solveColumnEntries?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))) :
    List Basis → Option (List (CachedColumn Variable Basis Hom))
  | [] => some []
  | basis :: rest => do
      let column ← solveColumn? (representations basis).1
        (representations basis).2 basis
      let entries ← solveColumnEntries? representations rest
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
    (candidates : List Basis)
    {entries : List (CachedColumn Variable Basis Hom)}
    (solved : solveColumnEntries? representations candidates = some entries)
    {basis : Basis} {column : Variable → HomContext Hom}
    (cached : lookupColumn? entries basis = some column) :
    solveColumn? (representations basis).1
      (representations basis).2 basis = some column := by
  induction candidates generalizing entries basis column with
  | nil =>
      simp [solveColumnEntries?] at solved
      simp [solved, lookupColumn?] at cached
  | cons head tail inductionHypothesis =>
      simp only [solveColumnEntries?] at solved
      cases headResult : solveColumn? (representations head).1
          (representations head).2 head with
      | none => simp [headResult] at solved
      | some headColumn =>
          cases tailResult : solveColumnEntries? representations tail with
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
    (candidates : List Basis)
    {entries : List (CachedColumn Variable Basis Hom)}
    (solved : solveColumnEntries? representations candidates = some entries)
    {basis : Basis} (membership : basis ∈ candidates) :
    (lookupColumn? entries basis).isSome := by
  induction candidates generalizing entries with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [solveColumnEntries?] at solved
      cases headResult : solveColumn? (representations head).1
          (representations head).2 head with
      | none => simp [headResult] at solved
      | some headColumn =>
          cases tailResult : solveColumnEntries? representations tail with
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
    (candidates : List Basis)
    (solvable : ∀ basis ∈ candidates,
      ∃ column, solveColumn? (representations basis).1
        (representations basis).2 basis = some column) :
    ∃ entries, solveColumnEntries? representations candidates =
      some entries := by
  induction candidates with
  | nil => exact ⟨[], rfl⟩
  | cons head tail inductionHypothesis =>
      rcases solvable head (by simp) with ⟨headColumn, headFound⟩
      rcases inductionHypothesis (fun basis membership =>
          solvable basis (by simp [membership])) with
        ⟨tailEntries, tailFound⟩
      exact ⟨(head, headColumn) :: tailEntries,
        by simp [solveColumnEntries?, headFound, tailFound]⟩

def cachedColumnMatrix [DecidableEq Basis]
    (entries : List (CachedColumn Variable Basis Hom)) :
    Matrix Variable Basis (HomContext Hom) :=
  fun index basis =>
    match lookupColumn? entries basis with
    | some column => column index
    | none => 0

/-- Solve the independent decomposition columns once each. -/
def solveColumnFamily?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))) :
    Option (Matrix Variable Basis (HomContext Hom)) := do
  let entries ← solveColumnEntries? representations (FinEnum.toList Basis)
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
    {values : Matrix Variable Basis (HomContext Hom)}
    (found : solveColumnFamily? representations = some values) :
    ∀ row basis,
      evaluateMatrixRepresentation (representations basis).1 values row basis ≤
        evaluateMatrixRepresentation (representations basis).2 values row basis := by
  unfold solveColumnFamily? at found
  cases entriesResult : solveColumnEntries? representations
      (FinEnum.toList Basis) with
  | none => simp [entriesResult] at found
  | some entries =>
      simp [entriesResult] at found
      subst values
      intro row basis
      have cachedSome : (lookupColumn? entries basis).isSome :=
        solveColumnEntries?_lookup_complete representations
          (FinEnum.toList Basis) entriesResult (FinEnum.mem_toList basis)
      cases lookupResult : lookupColumn? entries basis with
      | none => simp [lookupResult] at cachedSome
      | some column =>
          have columnFound := solveColumnEntries?_lookup_sound
            representations (FinEnum.toList Basis)
            entriesResult lookupResult
          simpa [cachedColumnMatrix, lookupResult] using
            solveColumn?_sound (representations basis).1
              (representations basis).2 basis columnFound row

theorem solveColumnFamily?_complete
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (solution : ∃ values : Matrix Variable Basis (HomContext Hom),
      ∀ row basis,
        evaluateMatrixRepresentation (representations basis).1 values row basis ≤
          evaluateMatrixRepresentation (representations basis).2 values row basis) :
    ∃ values, solveColumnFamily? representations = some values := by
  rcases solution with ⟨values, solved⟩
  have columnSolvable : ∀ basis ∈ FinEnum.toList Basis,
      ∃ column, solveColumn? (representations basis).1
        (representations basis).2 basis = some column := by
    intro basis _
    rcases solveColumn?_complete (representations basis).1
        (representations basis).2 basis
        ⟨fun index => values index basis, fun row => solved row basis⟩ with
      ⟨column, found⟩
    exact ⟨column, found⟩
  rcases solveColumnEntries?_complete representations
      (FinEnum.toList Basis) columnSolvable with ⟨entries, entriesFound⟩
  exact ⟨cachedColumnMatrix entries,
    by simp [solveColumnFamily?, entriesFound]⟩

end ACUIHE.Solver.Search.Optimized.Shortcut
