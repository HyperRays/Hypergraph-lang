import ACUIHE.Optimized.FILO.Column
import ACUIHE.Solver.Search.E.Reconstruction

/-!
ACUIhE entry point backed by the proved FILO finite-language solver.
The original and reachable-state optimized solvers remain unchanged.
-/

namespace ACUIHE.Optimized.FILO

open ACUIHE.Solver
open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

local instance shortcutEBoolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

/-- Solve one valid E-combination certificate with the shortcut column
solver. -/
def solveEConfiguration?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) :
    Option (Matrix Var (ECombinationBasis left right) (HomContext Hom)) :=
  if configuration.valid = true then
    solveColumnFamily?
      (eCombinationColumnRepresentations left right configuration)
  else
    none

theorem solveEConfiguration?_sound
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    {values : Matrix Var (ECombinationBasis left right) (HomContext Hom)}
    (found : solveEConfiguration? left right configuration = some values) :
    configuration.valid = true ∧
      eCombinationMatrixBelow left right configuration values := by
  unfold solveEConfiguration? at found
  split at found
  next valid =>
    exact ⟨valid, solveColumnFamily?_sound
      (eCombinationColumnRepresentations left right configuration) found⟩
  next invalid => simp at found

theorem solveEConfiguration?_complete
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (valid : configuration.valid = true)
    (solution : ∃ values :
        Matrix Var (ECombinationBasis left right) (HomContext Hom),
      eCombinationMatrixBelow left right configuration values) :
    ∃ values, solveEConfiguration? left right configuration = some values := by
  rcases solveColumnFamily?_complete
      (eCombinationColumnRepresentations left right configuration)
      solution with ⟨values, found⟩
  exact ⟨values, by simp [solveEConfiguration?, valid, found]⟩

/-- Reconstruct and independently validate the assignment for a successful
configuration. -/
def solveEConfigurationChecked?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) :
    Option (Var → NormalForm Const (Fin 0) Hom) := do
  let values ← solveEConfiguration? left right configuration
  let assignment :=
    decodeECombinationAssignment left right configuration values
  if checkGroundInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right) then
    some assignment
  else
    none

/-- Cached form of one checked E configuration.  The cache is shared across
configurations, so extensionally identical ACUIh columns are solved once. -/
def solveEConfigurationCheckedCached?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (cache : SystemCache (ECombinationRow left right) Var Hom) :
    Option (Var → NormalForm Const (Fin 0) Hom) ×
      SystemCache (ECombinationRow left right) Var Hom :=
  if configuration.valid = true then
    let solved := solveColumnFamilyCached?
      (eCombinationColumnRepresentations left right configuration) cache
    match solved.1 with
    | none => (none, solved.2)
    | some values =>
        let assignment :=
          decodeECombinationAssignment left right configuration values
        if checkGroundInequality
            (applyGroundAssignment assignment left)
            (applyGroundAssignment assignment right) then
          (some assignment, solved.2)
        else
          (none, solved.2)
  else
    (none, cache)

theorem solveEConfigurationCheckedCached?_correct
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (cache : SystemCache (ECombinationRow left right) Var Hom)
    (validCache : SystemCacheValid cache) :
    (solveEConfigurationCheckedCached?
        left right configuration cache).1 =
        solveEConfigurationChecked? left right configuration ∧
      SystemCacheValid
        (solveEConfigurationCheckedCached?
          left right configuration cache).2 := by
  by_cases valid : configuration.valid = true
  · let representations :=
      eCombinationColumnRepresentations left right configuration
    cases cachedEquality : solveColumnFamilyCached? representations cache with
    | mk familyResult nextCache =>
        have familyCorrect := solveColumnFamilyCached?_correct
          representations cache validCache
        have resultEquality :
            familyResult = solveColumnFamily? representations := by
          simpa [cachedEquality] using familyCorrect.1
        have nextValid : SystemCacheValid nextCache := by
          simpa [cachedEquality] using familyCorrect.2
        cases solved : solveColumnFamily? representations with
        | none =>
            have familyNone : familyResult = none := by
              rw [resultEquality, solved]
            subst familyResult
            have cachedNone :
                solveColumnFamilyCached? representations cache =
                  (none, nextCache) := by
              rw [cachedEquality, solved]
            constructor
            · simp [solveEConfigurationCheckedCached?,
                solveEConfigurationChecked?, solveEConfiguration?, valid,
                representations, cachedNone, solved]
            · simpa [solveEConfigurationCheckedCached?, valid,
                representations, cachedNone] using nextValid
        | some values =>
            have familySome : familyResult = some values := by
              rw [resultEquality, solved]
            subst familyResult
            have cachedSome :
                solveColumnFamilyCached? representations cache =
                  (some values, nextCache) := by
              rw [cachedEquality, solved]
            by_cases checked : checkGroundInequality
                (applyGroundAssignment
                  (decodeECombinationAssignment left right configuration values)
                  left)
                (applyGroundAssignment
                  (decodeECombinationAssignment left right configuration values)
                  right) = true
            · constructor
              · simp [solveEConfigurationCheckedCached?,
                  solveEConfigurationChecked?, solveEConfiguration?, valid,
                  representations, cachedSome, solved, checked]
              · simpa [solveEConfigurationCheckedCached?, valid,
                  representations, cachedSome, checked] using nextValid
            · constructor
              · simp [solveEConfigurationCheckedCached?,
                  solveEConfigurationChecked?, solveEConfiguration?, valid,
                  representations, cachedSome, solved, checked]
              · simpa [solveEConfigurationCheckedCached?, valid,
                  representations, cachedSome, checked] using nextValid
  · constructor
    · simp [solveEConfigurationCheckedCached?,
        solveEConfigurationChecked?, solveEConfiguration?, valid]
    · simpa [solveEConfigurationCheckedCached?, valid] using validCache

/-- Stateful first-success search through E configurations. -/
def solveEConfigurationListCached?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    List (EConfiguration left right) →
      SystemCache (ECombinationRow left right) Var Hom →
      Option (Var → NormalForm Const (Fin 0) Hom) ×
        SystemCache (ECombinationRow left right) Var Hom
  | [], cache => (none, cache)
  | configuration :: rest, cache =>
      let attempted :=
        solveEConfigurationCheckedCached? left right configuration cache
      match attempted.1 with
      | some assignment => (some assignment, attempted.2)
      | none => solveEConfigurationListCached? left right rest attempted.2

theorem solveEConfigurationListCached?_correct
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    ∀ configurations
      (cache : SystemCache (ECombinationRow left right) Var Hom),
      SystemCacheValid cache →
      (solveEConfigurationListCached?
          left right configurations cache).1 =
          firstSome?
            (solveEConfigurationChecked? left right) configurations ∧
        SystemCacheValid
          (solveEConfigurationListCached?
            left right configurations cache).2 := by
  intro configurations
  induction configurations with
  | nil =>
      intro cache valid
      exact ⟨rfl, valid⟩
  | cons configuration rest inductionHypothesis =>
      intro cache valid
      cases cachedEquality : solveEConfigurationCheckedCached?
          left right configuration cache with
      | mk attemptedResult nextCache =>
          have attemptedCorrect :=
            solveEConfigurationCheckedCached?_correct
              left right configuration cache valid
          have resultEquality : attemptedResult =
              solveEConfigurationChecked? left right configuration := by
            simpa [cachedEquality] using attemptedCorrect.1
          have nextValid : SystemCacheValid nextCache := by
            simpa [cachedEquality] using attemptedCorrect.2
          cases attempted :
              solveEConfigurationChecked? left right configuration with
          | none =>
              have attemptedNone : attemptedResult = none := by
                rw [resultEquality, attempted]
              subst attemptedResult
              have cachedNone : solveEConfigurationCheckedCached?
                  left right configuration cache = (none, nextCache) := by
                rw [cachedEquality, attempted]
              have tailCorrect := inductionHypothesis nextCache nextValid
              constructor
              · simpa [solveEConfigurationListCached?, firstSome?,
                  cachedNone, attempted] using tailCorrect.1
              · simpa [solveEConfigurationListCached?, cachedNone] using
                  tailCorrect.2
          | some assignment =>
              have attemptedSome : attemptedResult = some assignment := by
                rw [resultEquality, attempted]
              subst attemptedResult
              have cachedSome : solveEConfigurationCheckedCached?
                  left right configuration cache =
                    (some assignment, nextCache) := by
                rw [cachedEquality, attempted]
              constructor
              · simp [solveEConfigurationListCached?, firstSome?,
                  cachedSome, attempted]
              · simpa [solveEConfigurationListCached?, cachedSome] using
                  nextValid

/-- Uncached specification search retained as the simple extensional model
for the production solver. -/
def solveACUIhEUncached?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Option (Var → NormalForm Const (Fin 0) Hom) :=
  firstSome?
    (fun configuration =>
      solveEConfigurationChecked? left right configuration)
    (FinEnum.toList (EConfiguration left right))

/-- Sound and complete ACUIhE solver using FILO with exact cross-configuration
memoization.  There is no user-supplied depth or fuel. -/
def solveACUIhE?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Option (Var → NormalForm Const (Fin 0) Hom) :=
  (solveEConfigurationListCached? left right
    (FinEnum.toList (EConfiguration left right)) []).1

theorem solveACUIhE?_eq_uncached
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    solveACUIhE? left right = solveACUIhEUncached? left right := by
  have emptyValid :
      SystemCacheValid
        ([] : SystemCache (ECombinationRow left right) Var Hom) := by
    intro entry membership
    simp at membership
  exact (solveEConfigurationListCached?_correct left right
    (FinEnum.toList (EConfiguration left right)) [] emptyValid).1

theorem solveACUIhE?_sound
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    {assignment : Var → NormalForm Const (Fin 0) Hom}
    (found : solveACUIhE? left right = some assignment) :
    IsSolvedInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right) := by
  rw [solveACUIhE?_eq_uncached] at found
  unfold solveACUIhEUncached? at found
  rcases firstSome?_sound _ _ found with
    ⟨configuration, _, configurationFound⟩
  unfold solveEConfigurationChecked? at configurationFound
  cases valuesResult : solveEConfiguration? left right configuration with
  | none => simp [valuesResult] at configurationFound
  | some values =>
      let candidate :=
        decodeECombinationAssignment left right configuration values
      by_cases checked : checkGroundInequality
          (applyGroundAssignment candidate left)
          (applyGroundAssignment candidate right) = true
      · have resultEquality : candidate = assignment := by
          simpa [valuesResult, candidate, checked] using configurationFound
        subst assignment
        exact (checkGroundInequality_eq_true_iff _ _).mp checked
      · simp [valuesResult, candidate, checked] at configurationFound

theorem solveACUIhE?_complete_of_productive_configuration
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (certificate : ∃ configuration : EConfiguration left right,
      ProductiveEConfiguration left right configuration) :
    ∃ assignment, solveACUIhE? left right = some assignment := by
  rw [solveACUIhE?_eq_uncached]
  unfold solveACUIhEUncached?
  rcases certificate with
    ⟨configuration, valid, matrixSolution, reconstruction⟩
  rcases solveEConfiguration?_complete left right configuration
      valid matrixSolution with ⟨values, valuesFound⟩
  have valuesBelow :=
    (solveEConfiguration?_sound left right configuration valuesFound).2
  let assignment :=
    decodeECombinationAssignment left right configuration values
  have checked : checkGroundInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right) = true :=
    reconstruction values valuesBelow
  have configurationFound :
      solveEConfigurationChecked? left right configuration =
        some assignment := by
    simp [solveEConfigurationChecked?, valuesFound, assignment, checked]
  apply firstSome?_complete
    (fun candidate => solveEConfigurationChecked? left right candidate)
    (FinEnum.toList (EConfiguration left right))
    (candidate := configuration) (result := assignment)
  · exact FinEnum.mem_toList configuration
  · exact configurationFound

theorem solveACUIhE?_complete
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (solution : ∃ assignment : Var → NormalForm Const (Fin 0) Hom,
      IsSolvedInequality
        (applyGroundAssignment assignment left)
        (applyGroundAssignment assignment right)) :
    ∃ assignment, solveACUIhE? left right = some assignment := by
  rcases solution with ⟨assignment, solved⟩
  apply solveACUIhE?_complete_of_productive_configuration
  exact exists_productive_configuration_of_solution
    left right assignment solved

private theorem option_eq_none_iff_not_exists_some
    {Alpha : Type*} (value : Option Alpha) :
    value = none ↔ ¬ ∃ result, value = some result := by
  cases value <;> simp

theorem solveACUIhE?_eq_none_iff
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    solveACUIhE? left right = none ↔
      ¬ ∃ assignment : Var → NormalForm Const (Fin 0) Hom,
        IsSolvedInequality
          (applyGroundAssignment assignment left)
          (applyGroundAssignment assignment right) := by
  rw [option_eq_none_iff_not_exists_some]
  apply not_congr
  constructor
  · rintro ⟨assignment, found⟩
    exact ⟨assignment, solveACUIhE?_sound left right found⟩
  · exact solveACUIhE?_complete left right

end ACUIHE.Optimized.FILO
