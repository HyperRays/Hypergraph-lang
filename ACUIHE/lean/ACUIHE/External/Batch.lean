import ACUIHE.External
import ACUIHE.Solver.Search.Optimized.Column

/-!
# Optimized batched external API

This module solves a finite family of externally rewritten inequalities with
one shared assignment. The union of all input terms supplies one global finite
`E`-occurrence basis, while every input inequality remains a distinct matrix
row. All rows consequently constrain one shared variable-assignment matrix.

The resulting column family is solved by the reachable-state optimized search
backend. The original exhaustive backend remains confined to
`ACUIHE.External.solveACUIhE?`.
-/

namespace ACUIHE.External

open ACUIHE.Solver

universe u v w

instance batchBoolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

/-- One inequality supplied to the simultaneous external API. -/
structure TypeInequality
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  left : NormalForm Const Var Hom
  right : NormalForm Const Var Hom

namespace TypeInequality

/-- Apply the ordered external rewrite pass to both sides. -/
def rewrite
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (inequality : TypeInequality Const Var Hom) :
    TypeInequality Const Var Hom where
  left := rewriteAll rules inequality.left
  right := rewriteAll rules inequality.right

/-- Satisfaction of one rewritten inequality by a ground assignment. -/
def IsSolved
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (inequality : TypeInequality Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Prop :=
  IsSolvedInequality
    (ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules inequality.left))
    (ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules inequality.right))

/-- Executable exact check for one rewritten inequality. -/
def check
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (inequality : TypeInequality Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Bool :=
  ACUIHE.Solver.Search.checkGroundInequality
    (ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules inequality.left))
    (ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules inequality.right))

theorem check_eq_true_iff
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (inequality : TypeInequality Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) :
    inequality.check rules assignment = true ↔
      inequality.IsSolved rules assignment := by
  exact ACUIHE.Solver.Search.checkGroundInequality_eq_true_iff _ _

end TypeInequality

/-- A finite family of inequalities is solved by one shared assignment. -/
def IsSystemSolution
    {Row : Type u} {Const : Type u} {Var : Type u} {Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Prop :=
  ∀ row, (system row).IsSolved rules assignment

/-- Executable exact check of every row in a finite inequality system. -/
def checkInequalitySystem
    {Row : Type u} {Const : Type u} {Var : Type u} {Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Bool :=
  (FinEnum.toList Row).all fun row =>
    (system row).check rules assignment

theorem checkInequalitySystem_eq_true_iff
    {Row : Type u} {Const : Type u} {Var : Type u} {Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) :
    checkInequalitySystem rules system assignment = true ↔
      IsSystemSolution rules system assignment := by
  simp [checkInequalitySystem, IsSystemSolution,
    TypeInequality.check_eq_true_iff]

/--
Union of all rewritten terms in the system. This is not a conjunction
encoding: it is used only to enumerate every `E` body that purification may
need to name.
-/
def systemSupport
    {Row : Type u} {Const : Type u} {Var : Type u} {Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom) :
    NormalForm Const Var Hom :=
  (FinEnum.toList Row).foldr
    (fun row support =>
      let inequality := (system row).rewrite rules
      inequality.left ∪ inequality.right ∪ support)
    ∅

/-- One global `E` certificate for every occurrence in a finite system. -/
abbrev SystemEConfiguration
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom) :=
  ACUIHE.Solver.Search.EConfiguration
    (systemSupport rules system) (systemSupport rules system)

/-- Constants of the system-wide purified affine problem. -/
abbrev SystemCombinationBasis
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom) :=
  ACUIHE.Solver.Search.ECombinationBasis
    (systemSupport rules system) (systemSupport rules system)

/--
Rows consist of caller inequalities plus the ordinary `E` equality, dependency,
and support rows generated for the global occurrence basis.
-/
abbrev SystemCombinationRow
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom) :=
  Row ⊕ ACUIHE.Solver.Search.ECombinationRow
    (systemSupport rules system) (systemSupport rules system)

/-- Right-hand term of one row in the system-wide affine problem. -/
def systemCombinationRightTerm
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (configuration : SystemEConfiguration rules system) :
    SystemCombinationRow rules system →
      Term (SystemCombinationBasis rules system) Var Hom
  | .inl row =>
      reify (ACUIHE.Solver.Search.purifyNormalForm
        (systemSupport rules system) (systemSupport rules system)
        configuration (rewriteAll rules (system row).right))
  | .inr generatedRow =>
      ACUIHE.Solver.Search.eCombinationRightTerm
        (systemSupport rules system) (systemSupport rules system)
        configuration generatedRow

/--
Left-hand row specialized to the basis column currently being solved. Caller
rows are ordinary affine rows; generated dependency restrictions remain
column-local as required by the shared ACUIhE combination construction.
-/
def systemCombinationColumnLeftTerm
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (configuration : SystemEConfiguration rules system)
    (selectedBasis : SystemCombinationBasis rules system) :
    SystemCombinationRow rules system →
      Term (SystemCombinationBasis rules system) Var Hom
  | .inl row =>
      reify (ACUIHE.Solver.Search.purifyNormalForm
        (systemSupport rules system) (systemSupport rules system)
        configuration (rewriteAll rules (system row).left))
  | .inr generatedRow =>
      ACUIHE.Solver.Search.eCombinationColumnLeftTerm
        (systemSupport rules system) (systemSupport rules system)
        configuration selectedBasis generatedRow

/-- Column-specialized matrices for all caller and generated rows. -/
def systemCombinationColumnRepresentations
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (configuration : SystemEConfiguration rules system)
    (selectedBasis : SystemCombinationBasis rules system) :=
  (ACUIHE.Solver.Search.fullMatrixRepresentation
      (fun row => normalize
        (systemCombinationColumnLeftTerm rules system configuration
          selectedBasis row)),
    ACUIHE.Solver.Search.fullMatrixRepresentation
      (fun row => normalize
        (systemCombinationRightTerm rules system configuration row)))

/-- Every row holds in its selected basis column. -/
def systemCombinationMatrixBelow
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [Encodable Const] [FinEnum Var] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (configuration : SystemEConfiguration rules system)
    (values : Matrix Var (SystemCombinationBasis rules system)
      (ACUIHE.Solver.Linear.HomContext Hom)) : Prop :=
  ∀ row basis,
    ACUIHE.Solver.Linear.evaluateMatrixRepresentation
        (systemCombinationColumnRepresentations rules system configuration
          basis).1 values row basis ≤
      ACUIHE.Solver.Linear.evaluateMatrixRepresentation
        (systemCombinationColumnRepresentations rules system configuration
          basis).2 values row basis

/--
Solve one valid global `E` certificate with the reachable-state optimized
affine column solver. `shallowBound` controls only its fast shallow phase.
-/
def solveSystemEConfiguration?
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (configuration : SystemEConfiguration rules system)
    (shallowBound : Nat := 8) :
    Option (Matrix Var (SystemCombinationBasis rules system)
      (ACUIHE.Solver.Linear.HomContext Hom)) :=
  if configuration.valid = true then
    ACUIHE.Solver.Search.Optimized.solveColumnFamily?
      (systemCombinationColumnRepresentations rules system configuration)
      shallowBound
  else
    none

/-- Decode and independently validate the candidate for one certificate. -/
def solveSystemEConfigurationChecked?
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (configuration : SystemEConfiguration rules system)
    (shallowBound : Nat := 8) :
    Option (Var → GroundNormalForm Const Hom) := do
  let values ← solveSystemEConfiguration?
    rules system configuration shallowBound
  let support := systemSupport rules system
  let assignment := ACUIHE.Solver.Search.decodeECombinationAssignment
    support support configuration values
  if checkInequalitySystem rules system assignment then
    some assignment
  else
    none

/--
Solve all rows simultaneously with the optimized backend. Unlike repeated
calls to the single-row API, this searches for one assignment matrix satisfying
the complete family.
-/
def solveInequalitySystem?
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (shallowBound : Nat := 8) :
    Option (Var → GroundNormalForm Const Hom) :=
  ACUIHE.Solver.Search.firstSome?
    (fun configuration =>
      solveSystemEConfigurationChecked?
        rules system configuration shallowBound)
    (FinEnum.toList (SystemEConfiguration rules system))

/-- Every returned assignment satisfies every externally rewritten row. -/
theorem solveInequalitySystem?_sound
    {Row Const Var Hom : Type u}
    [FinEnum Row]
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (system : Row → TypeInequality Const Var Hom)
    (shallowBound : Nat := 8)
    {assignment : Var → GroundNormalForm Const Hom}
    (found : solveInequalitySystem? rules system shallowBound =
      some assignment) :
    IsSystemSolution rules system assignment := by
  rcases ACUIHE.Solver.Search.firstSome?_sound _ _ found with
    ⟨configuration, _, configurationFound⟩
  unfold solveSystemEConfigurationChecked? at configurationFound
  cases valuesResult : solveSystemEConfiguration?
      rules system configuration shallowBound with
  | none => simp [valuesResult] at configurationFound
  | some values =>
      let support := systemSupport rules system
      let candidate := ACUIHE.Solver.Search.decodeECombinationAssignment
        support support configuration values
      by_cases checked : checkInequalitySystem rules system candidate = true
      · have assignmentEquality : candidate = assignment := by
          simpa [valuesResult, support, candidate, checked]
            using configurationFound
        subst assignment
        exact (checkInequalitySystem_eq_true_iff
          rules system candidate).mp checked
      · simp [valuesResult, support, candidate, checked] at configurationFound

/-!
## Type-equation interface

An equation contributes two rows to the affine system, one in each direction.
The structures and functions below retain both rows through the simultaneous
solver, so every equation in a batch is checked against the same assignment.
-/

/-- One type equation over solver normal forms. -/
structure TypeEquation
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  left : NormalForm Const Var Hom
  right : NormalForm Const Var Hom

namespace TypeEquation

/-- Both sides of an externally rewritten equation under one ground assignment. -/
def IsSolved
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equation : TypeEquation Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Prop :=
  ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules equation.left) =
    ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules equation.right)

/-- Executable exact check for one externally rewritten equation. -/
def check
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equation : TypeEquation Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Bool :=
  decide
    (ACUIHE.Solver.Search.applyGroundAssignment assignment
        (rewriteAll rules equation.left) =
      ACUIHE.Solver.Search.applyGroundAssignment assignment
        (rewriteAll rules equation.right))

theorem check_eq_true_iff
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equation : TypeEquation Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) :
    equation.check rules assignment = true ↔
      equation.IsSolved rules assignment := by
  simp [check, IsSolved]

end TypeEquation

/-- The conjunction represented by a finite, indexed family of equations. -/
def AreSolved
    {Index : Type u} {Const : Type u} {Var : Type u} {Hom : Type u}
    [FinEnum Index] [Encodable Index]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equations : Index → TypeEquation Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Prop :=
  ∀ index, (equations index).IsSolved rules assignment

/-- Executable exact check of a complete finite equation batch. -/
def checkEquationBatch
    {Index : Type u} {Const : Type u} {Var : Type u} {Hom : Type u}
    [FinEnum Index] [Encodable Index]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equations : Index → TypeEquation Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Bool :=
  (FinEnum.toList Index).all fun index =>
    (equations index).check rules assignment

theorem checkEquationBatch_eq_true_iff
    {Index : Type u} {Const : Type u} {Var : Type u} {Hom : Type u}
    [FinEnum Index] [Encodable Index]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equations : Index → TypeEquation Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) :
    checkEquationBatch rules equations assignment = true ↔
      AreSolved rules equations assignment := by
  simp [checkEquationBatch, AreSolved, TypeEquation.check_eq_true_iff]

/-- One equation contributes a forward and a reverse inequality row. -/
def TypeEquation.asInequality
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (equation : TypeEquation Const Var Hom) (reverse : Bool) :
    TypeInequality Const Var Hom :=
  if reverse then
    { left := equation.right, right := equation.left }
  else
    { left := equation.left, right := equation.right }

/-- Row identifiers for the two directions of every indexed equation. -/
abbrev EquationRow (Index : Type u) := Index × Bool

/-- Expand an indexed equation family into affine inequality rows. -/
def equationSystem
    {Index Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (equations : Index → TypeEquation Const Var Hom) :
    EquationRow Index → TypeInequality Const Var Hom
  | (index, reverse) => (equations index).asInequality reverse

/-- Solve a finite equation family through one optimized shared affine matrix. -/
def solveEquationBatch?
    {Index Const Var Hom : Type u}
    [FinEnum Index] [Encodable Index]
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equations : Index → TypeEquation Const Var Hom)
    (shallowBound : Nat := 8) :
    Option (Var → GroundNormalForm Const Hom) :=
  solveInequalitySystem? rules (equationSystem equations) shallowBound

/-- Every returned batch assignment makes every rewritten equation equal. -/
theorem solveEquationBatch?_sound
    {Index Const Var Hom : Type u}
    [FinEnum Index] [Encodable Index]
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (equations : Index → TypeEquation Const Var Hom)
    (shallowBound : Nat := 8)
    {assignment : Var → GroundNormalForm Const Hom}
    (found : solveEquationBatch? rules equations shallowBound =
      some assignment) :
    AreSolved rules equations assignment := by
  have solvedRows := solveInequalitySystem?_sound
    rules (equationSystem equations) shallowBound found
  intro index
  have forward := solvedRows (index, false)
  have reverse := solvedRows (index, true)
  unfold equationSystem TypeEquation.asInequality at forward reverse
  simp only [if_true, TypeInequality.IsSolved] at forward reverse
  unfold TypeEquation.IsSolved
  exact calc
    ACUIHE.Solver.Search.applyGroundAssignment assignment
        (rewriteAll rules (equations index).left) =
      ACUIHE.Solver.Search.applyGroundAssignment assignment
        (rewriteAll rules (equations index).right) +
      ACUIHE.Solver.Search.applyGroundAssignment assignment
        (rewriteAll rules (equations index).left) := reverse.2.2.symm
    _ = ACUIHE.Solver.Search.applyGroundAssignment assignment
          (rewriteAll rules (equations index).left) +
        ACUIHE.Solver.Search.applyGroundAssignment assignment
          (rewriteAll rules (equations index).right) := by
            apply NormalForm.ext_raw
            exact ACUIHE.Solver.NormalForm.Internal.rawUnion_comm _ _
    _ = ACUIHE.Solver.Search.applyGroundAssignment assignment
          (rewriteAll rules (equations index).right) := forward.2.2

/-- Solve one equation; this is the two-row specialization of the batch API. -/
def solveEquation?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom)
    (shallowBound : Nat := 8) :
    Option (Var → GroundNormalForm Const Hom) :=
  solveEquationBatch? (Index := ULift.{u} Unit) rules
    (fun _ => { left := left, right := right }) shallowBound

/-- Every assignment returned for one equation makes its rewritten sides equal. -/
theorem solveEquation?_sound
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom)
    (shallowBound : Nat := 8)
    {assignment : Var → GroundNormalForm Const Hom}
    (found : solveEquation? rules left right shallowBound = some assignment) :
    (TypeEquation.mk left right).IsSolved rules assignment := by
  have solved := solveEquationBatch?_sound
    (Index := ULift.{u} Unit) rules
    (fun _ => { left := left, right := right }) shallowBound found
  exact solved ⟨()⟩

end ACUIHE.External
