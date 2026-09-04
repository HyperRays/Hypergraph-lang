import ACUIHE.Optimized.Optimized.Column
import ACUIHE.Solver.Search.E.Reconstruction

set_option linter.dupNamespace false

/-!
Separate ACUIhE entry point backed by the optimized reachable-state automaton
solver.  The original `ACUIHE.Solver.Search.solveACUIhE?` is unchanged.
-/

namespace ACUIHE.Optimized.Optimized

open ACUIHE.Solver
open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

local instance optimizedEBoolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

/-- Solve one valid combination certificate through the optimized column
solver. -/
def solveEConfiguration?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (shallowBound : Nat := 8) :
    Option (Matrix Var (ECombinationBasis left right) (HomContext Hom)) :=
  if configuration.valid = true then
    solveColumnFamily?
      (eCombinationColumnRepresentations left right configuration)
      shallowBound
  else
    none

theorem solveEConfiguration?_sound
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (shallowBound : Nat := 8)
    {values : Matrix Var (ECombinationBasis left right) (HomContext Hom)}
    (found : solveEConfiguration? left right configuration shallowBound =
      some values) :
    configuration.valid = true ∧
      eCombinationMatrixBelow left right configuration values := by
  unfold solveEConfiguration? at found
  split at found
  next valid =>
    exact ⟨valid, solveColumnFamily?_sound
      (eCombinationColumnRepresentations left right configuration)
      shallowBound found⟩
  next invalid => simp at found

theorem solveEConfiguration?_complete
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (shallowBound : Nat := 8)
    (valid : configuration.valid = true)
    (solution : ∃ values :
        Matrix Var (ECombinationBasis left right) (HomContext Hom),
      eCombinationMatrixBelow left right configuration values) :
    ∃ values, solveEConfiguration? left right configuration shallowBound =
      some values := by
  rcases solveColumnFamily?_complete
      (eCombinationColumnRepresentations left right configuration)
      shallowBound solution with ⟨values, found⟩
  exact ⟨values, by simp [solveEConfiguration?, valid, found]⟩

/-- Reconstruct and independently check the candidate produced for one
configuration. -/
def solveEConfigurationChecked?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (shallowBound : Nat := 8) :
    Option (Var → NormalForm Const (Fin 0) Hom) := do
  let values ← solveEConfiguration? left right configuration shallowBound
  let assignment :=
    decodeECombinationAssignment left right configuration values
  if checkGroundInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right) then
    some assignment
  else
    none

/-- Separate, sound and complete ACUIhE solver using the optimized automaton
kernel.  `shallowBound` controls only the fast shallow phase; exact saturation
and the completeness fallback do not depend on it. -/
def solveACUIhE?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (shallowBound : Nat := 8) :
    Option (Var → NormalForm Const (Fin 0) Hom) :=
  firstSome?
    (fun configuration =>
      solveEConfigurationChecked? left right configuration shallowBound)
    (FinEnum.toList (EConfiguration left right))

theorem solveACUIhE?_sound
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (shallowBound : Nat := 8)
    {assignment : Var → NormalForm Const (Fin 0) Hom}
    (found : solveACUIhE? left right shallowBound = some assignment) :
    IsSolvedInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right) := by
  rcases firstSome?_sound _ _ found with
    ⟨configuration, _, configurationFound⟩
  unfold solveEConfigurationChecked? at configurationFound
  cases valuesResult : solveEConfiguration? left right configuration shallowBound with
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
    (shallowBound : Nat := 8)
    (certificate : ∃ configuration : EConfiguration left right,
      ProductiveEConfiguration left right configuration) :
    ∃ assignment, solveACUIhE? left right shallowBound = some assignment := by
  rcases certificate with
    ⟨configuration, valid, matrixSolution, reconstruction⟩
  rcases solveEConfiguration?_complete left right configuration shallowBound
      valid matrixSolution with ⟨values, valuesFound⟩
  have valuesBelow :=
    (solveEConfiguration?_sound left right configuration shallowBound
      valuesFound).2
  let assignment :=
    decodeECombinationAssignment left right configuration values
  have checked : checkGroundInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right) = true :=
    reconstruction values valuesBelow
  have configurationFound :
      solveEConfigurationChecked? left right configuration shallowBound =
        some assignment := by
    simp [solveEConfigurationChecked?, valuesFound, assignment, checked]
  apply firstSome?_complete
    (fun candidate =>
      solveEConfigurationChecked? left right candidate shallowBound)
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
    (shallowBound : Nat := 8)
    (solution : ∃ assignment : Var → NormalForm Const (Fin 0) Hom,
      IsSolvedInequality
        (applyGroundAssignment assignment left)
        (applyGroundAssignment assignment right)) :
    ∃ assignment, solveACUIhE? left right shallowBound = some assignment := by
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
    (left right : NormalForm Const Var Hom)
    (shallowBound : Nat := 8) :
    solveACUIhE? left right shallowBound = none ↔
      ¬ ∃ assignment : Var → NormalForm Const (Fin 0) Hom,
        IsSolvedInequality
          (applyGroundAssignment assignment left)
          (applyGroundAssignment assignment right) := by
  rw [option_eq_none_iff_not_exists_some]
  apply not_congr
  constructor
  · rintro ⟨assignment, found⟩
    exact ⟨assignment, solveACUIhE?_sound left right shallowBound found⟩
  · exact solveACUIhE?_complete left right shallowBound

end ACUIHE.Optimized.Optimized
