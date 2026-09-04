import ACUIHE.Solver.Search.Optimized.Shortcut.Column
import ACUIHE.Solver.Search.E.Reconstruction

/-!
Separate ACUIhE entry point backed by witness-carrying shortcut saturation.
The original and reachable-state optimized solvers remain unchanged.
-/

namespace ACUIHE.Solver.Search.Optimized.Shortcut

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

/-- Sound and complete ACUIhE solver using the new shortcut backend.  There
is deliberately no user-supplied depth or fuel: all iteration limits are
cardinality bounds for proved finite fixed points. -/
def solveACUIhE?
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

end ACUIHE.Solver.Search.Optimized.Shortcut
