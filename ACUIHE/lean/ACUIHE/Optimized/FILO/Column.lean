import ACUIHE.Optimized.FILO.FiniteLanguageSystem
import ACUIHE.Solver.Search.ColumnAutomaton

/-! The proved FILO finite-language kernel exposed through ACUIh columns. -/

namespace ACUIHE.Optimized.FILO

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

local instance filoColumnBoolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

/-- Executable extensional comparison of two finite-language systems over the
same finite row and variable types. -/
def sameFiniteLanguageSystem
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (first second : FiniteLanguageSystem Row Variable Hom) : Bool :=
  (FinEnum.toList Bool).all fun side =>
    (FinEnum.toList Row).all fun row =>
      ((FinEnum.toList Variable).all fun index =>
        decide (first.coefficient side row index =
          second.coefficient side row index)) &&
      decide (first.constant side row = second.constant side row)

theorem sameFiniteLanguageSystem_eq_true_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (first second : FiniteLanguageSystem Row Variable Hom) :
    sameFiniteLanguageSystem first second = true ↔
      (∀ side row index,
        first.coefficient side row index =
          second.coefficient side row index) ∧
      (∀ side row, first.constant side row = second.constant side row) := by
  simp [sameFiniteLanguageSystem]
  aesop

theorem finiteLanguageSystem_eq_of_same_eq_true
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    {first second : FiniteLanguageSystem Row Variable Hom}
    (same : sameFiniteLanguageSystem first second = true) :
    first = second := by
  rcases (sameFiniteLanguageSystem_eq_true_iff first second).mp same with
    ⟨coefficients, constants⟩
  cases first with
  | mk firstCoefficients firstConstants =>
      cases second with
      | mk secondCoefficients secondConstants =>
          congr
          · funext side row index
            exact coefficients side row index
          · funext side row
            exact constants side row

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

theorem solveColumn?_eq_none_iff
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) :
    solveColumn? left right basis = none ↔
      ¬ ∃ values : Variable → HomContext Hom,
        columnRepresentationBelow left right basis values := by
  constructor
  · intro failed solution
    rcases solveColumn?_complete left right basis solution with ⟨values, found⟩
    rw [failed] at found
    contradiction
  · intro rejected
    cases found : solveColumn? left right basis with
    | none => rfl
    | some values =>
        exact False.elim (rejected ⟨values,
          solveColumn?_sound left right basis found⟩)

/-!
## Extensional system cache

E configurations frequently induce identical ACUIh column systems.  Cache
both positive and negative exact results by finite extensional comparison.
-/

structure SystemCacheEntry (Row Variable Hom : Type u) where
  system : FiniteLanguageSystem Row Variable Hom
  result : Option (Variable → HomContext Hom)

abbrev SystemCache (Row Variable Hom : Type u) :=
  List (SystemCacheEntry Row Variable Hom)

def SystemCacheValid
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (entries : SystemCache Row Variable Hom) : Prop :=
  ∀ entry ∈ entries, solveFiniteLanguage? entry.system = entry.result

/-- A nested option distinguishes a cached negative result from a cache miss. -/
def lookupSystemResult?
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (target : FiniteLanguageSystem Row Variable Hom) :
    SystemCache Row Variable Hom →
      Option (Option (Variable → HomContext Hom))
  | [] => none
  | entry :: rest =>
      if sameFiniteLanguageSystem target entry.system then
        some entry.result
      else
        lookupSystemResult? target rest

theorem lookupSystemResult?_sound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (target : FiniteLanguageSystem Row Variable Hom)
    {entries : SystemCache Row Variable Hom}
    (valid : SystemCacheValid entries)
    {result : Option (Variable → HomContext Hom)}
    (found : lookupSystemResult? target entries = some result) :
    solveFiniteLanguage? target = result := by
  induction entries with
  | nil => simp [lookupSystemResult?] at found
  | cons entry rest inductionHypothesis =>
      by_cases same : sameFiniteLanguageSystem target entry.system = true
      · simp [lookupSystemResult?, same] at found
        have equality := finiteLanguageSystem_eq_of_same_eq_true same
        subst target
        simpa [found] using valid entry (by simp)
      · simp [lookupSystemResult?, same] at found
        exact inductionHypothesis
          (fun cached membership => valid cached (by simp [membership])) found

/-- Solve once on a miss and otherwise reuse the exact cached result. -/
def solveFiniteLanguageCached
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (system : FiniteLanguageSystem Row Variable Hom)
    (entries : SystemCache Row Variable Hom) :
    Option (Variable → HomContext Hom) × SystemCache Row Variable Hom :=
  match lookupSystemResult? system entries with
  | some result => (result, entries)
  | none =>
      let result := solveFiniteLanguage? system
      (result, { system := system, result := result } :: entries)

theorem solveFiniteLanguageCached_result
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (system : FiniteLanguageSystem Row Variable Hom)
    {entries : SystemCache Row Variable Hom}
    (valid : SystemCacheValid entries) :
    (solveFiniteLanguageCached system entries).1 =
      solveFiniteLanguage? system := by
  unfold solveFiniteLanguageCached
  cases found : lookupSystemResult? system entries with
  | none => rfl
  | some result =>
      simpa using (lookupSystemResult?_sound system valid found).symm

theorem solveFiniteLanguageCached_cacheValid
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (system : FiniteLanguageSystem Row Variable Hom)
    {entries : SystemCache Row Variable Hom}
    (valid : SystemCacheValid entries) :
    SystemCacheValid (solveFiniteLanguageCached system entries).2 := by
  unfold solveFiniteLanguageCached
  cases found : lookupSystemResult? system entries with
  | some result => exact valid
  | none =>
      intro entry membership
      rcases List.mem_cons.mp membership with equality | old
      · subst entry
        rfl
      · exact valid entry old

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

/-- Stateful column-family search sharing exact finite-language results with
other families over the same row/variable types. -/
def solveColumnEntriesCached?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))) :
    List Basis → SystemCache Row Variable Hom →
      Option (List (CachedColumn Variable Basis Hom)) ×
        SystemCache Row Variable Hom
  | [], cache => (some [], cache)
  | basis :: rest, cache =>
      let representation := representations basis
      let system := matrixColumnSystem representation.1 representation.2 basis
      let solved := solveFiniteLanguageCached system cache
      match solved.1 with
      | none => (none, solved.2)
      | some column =>
          let tail := solveColumnEntriesCached? representations rest solved.2
          match tail.1 with
          | none => (none, tail.2)
          | some entries => (some ((basis, column) :: entries), tail.2)

theorem solveColumnEntriesCached?_correct
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))) :
    ∀ candidates (cache : SystemCache Row Variable Hom),
      SystemCacheValid cache →
      (solveColumnEntriesCached? representations candidates cache).1 =
          solveColumnEntries? representations candidates ∧
        SystemCacheValid
          (solveColumnEntriesCached? representations candidates cache).2 := by
  intro candidates
  induction candidates with
  | nil =>
      intro cache valid
      exact ⟨rfl, valid⟩
  | cons basis rest inductionHypothesis =>
      intro cache valid
      let representation := representations basis
      let system :=
        matrixColumnSystem representation.1 representation.2 basis
      cases cachedEquality : solveFiniteLanguageCached system cache with
      | mk columnResult nextCache =>
          have resultEquality : columnResult = solveFiniteLanguage? system := by
            simpa [cachedEquality] using
              solveFiniteLanguageCached_result system valid
          have nextValid : SystemCacheValid nextCache := by
            simpa [cachedEquality] using
              solveFiniteLanguageCached_cacheValid system valid
          cases solved : solveFiniteLanguage? system with
          | none =>
              have columnNone : columnResult = none := by
                rw [resultEquality, solved]
              subst columnResult
              have cachedNone :
                  solveFiniteLanguageCached system cache =
                    (none, nextCache) := by
                rw [cachedEquality, solved]
              have cachedResult :
                  (solveColumnEntriesCached? representations
                    (basis :: rest) cache).1 = none := by
                simp [solveColumnEntriesCached?, representation, system,
                  cachedNone]
              have ordinaryResult :
                  solveColumnEntries? representations
                    (basis :: rest) = none := by
                simp [solveColumnEntries?, solveColumn?, representation,
                  system, solved]
              have cachedCache :
                  (solveColumnEntriesCached? representations
                    (basis :: rest) cache).2 = nextCache := by
                simp [solveColumnEntriesCached?, representation, system,
                  cachedNone]
              constructor
              · rw [cachedResult, ordinaryResult]
              · rw [cachedCache]
                exact nextValid
          | some column =>
              have columnSome : columnResult = some column := by
                rw [resultEquality, solved]
              subst columnResult
              have cachedSome :
                  solveFiniteLanguageCached system cache =
                    (some column, nextCache) := by
                rw [cachedEquality, solved]
              have tailCorrect := inductionHypothesis nextCache nextValid
              have cachedResult :
                  (solveColumnEntriesCached? representations
                    (basis :: rest) cache).1 =
                    Option.map (fun entries =>
                      (basis, column) :: entries)
                      (solveColumnEntriesCached?
                        representations rest nextCache).1 := by
                simp [solveColumnEntriesCached?, representation, system,
                  cachedSome]
                cases (solveColumnEntriesCached?
                  representations rest nextCache).1 <;> rfl
              have ordinaryResult :
                  solveColumnEntries? representations (basis :: rest) =
                    Option.map (fun entries =>
                      (basis, column) :: entries)
                      (solveColumnEntries? representations rest) := by
                simp [solveColumnEntries?, solveColumn?, representation,
                  system, solved]
                cases solveColumnEntries? representations rest <;> rfl
              have cachedCache :
                  (solveColumnEntriesCached? representations
                    (basis :: rest) cache).2 =
                    (solveColumnEntriesCached?
                      representations rest nextCache).2 := by
                simp [solveColumnEntriesCached?, representation, system,
                  cachedSome]
                cases (solveColumnEntriesCached?
                  representations rest nextCache).1 <;> rfl
              constructor
              · rw [cachedResult, ordinaryResult, tailCorrect.1]
              · rw [cachedCache]
                exact tailCorrect.2

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

/-- Column-family search that shares exact finite-language results through an
external cache. -/
def solveColumnFamilyCached?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (cache : SystemCache Row Variable Hom) :
    Option (Matrix Variable Basis (HomContext Hom)) ×
      SystemCache Row Variable Hom :=
  let solved := solveColumnEntriesCached? representations
    (FinEnum.toList Basis) cache
  (solved.1.map cachedColumnMatrix, solved.2)

theorem solveColumnFamilyCached?_correct
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)))
    (cache : SystemCache Row Variable Hom)
    (valid : SystemCacheValid cache) :
    (solveColumnFamilyCached? representations cache).1 =
        solveColumnFamily? representations ∧
      SystemCacheValid
        (solveColumnFamilyCached? representations cache).2 := by
  have entriesCorrect := solveColumnEntriesCached?_correct representations
    (FinEnum.toList Basis) cache valid
  constructor
  · simp only [solveColumnFamilyCached?, solveColumnFamily?]
    rw [entriesCorrect.1]
    cases solveColumnEntries? representations (FinEnum.toList Basis) <;> rfl
  · simpa [solveColumnFamilyCached?] using entriesCorrect.2

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

end ACUIHE.Optimized.FILO
