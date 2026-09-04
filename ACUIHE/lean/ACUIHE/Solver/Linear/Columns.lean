import ACUIHE.Solver.Linear.Representation

/-! Decomposition and composition of matrix solutions by constant columns. -/

namespace ACUIHE.Solver.Linear

universe u v w x

/-- A represented inequality holds exactly when its path sets are included basis-wise. -/
theorem matrixRepresentationBelow_iff_paths_subset
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (values : Matrix Variable Basis (HomContext Hom)) :
    matrixRepresentationBelow left right values ↔
      ∀ row basis,
        (evaluateMatrixRepresentation left values row basis).paths ⊆
          (evaluateMatrixRepresentation right values row basis).paths := by
  unfold matrixRepresentationBelow
  simp only [HomContext.le_iff_paths_subset]

/--
For one row, the matrix inequality is exactly the solved inequality between
the ground normal forms obtained by applying the represented assignment.
-/
theorem isSolvedInequality_applyMatrixAssignment_iff
    {Row : Type x} {Variable : Type v}
    {Const : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row (↥basis) (HomContext Hom))
    (values : Matrix Variable (↥basis) (HomContext Hom))
    (row : Row) :
    IsSolvedInequality
        (applyMatrixAssignment basis left values row)
        (applyMatrixAssignment basis right values row) ↔
      ∀ constant : ↥basis,
        evaluateMatrixRepresentation left values row constant ≤
          evaluateMatrixRepresentation right values row constant := by
  rw [isSolvedInequality_iff_constantCoefficient_le
    (applyMatrixAssignment basis left values row)
    (applyMatrixAssignment basis right values row)
    basis
    (isACUIh_decodeConstantMatrix basis
      (evaluateMatrixRepresentation left values) row)
    (constantSupport_decodeConstantMatrix_subset basis
      (evaluateMatrixRepresentation left values) row)]
  simp [applyMatrixAssignment]

/--
`matrixRepresentationBelow` agrees with `Solution.IsSolvedInequality` on
every decoded row of `A * V + C`.
-/
theorem matrixRepresentationBelow_iff_solvedInequalities
    {Row : Type x} {Variable : Type v}
    {Const : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row (↥basis) (HomContext Hom))
    (values : Matrix Variable (↥basis) (HomContext Hom)) :
    matrixRepresentationBelow left right values ↔
      ∀ row,
        IsSolvedInequality
          (applyMatrixAssignment basis left values row)
          (applyMatrixAssignment basis right values row) := by
  constructor
  · intro solution row
    exact (isSolvedInequality_applyMatrixAssignment_iff
      basis left right values row).mpr (solution row)
  · intro solved row
    exact (isSolvedInequality_applyMatrixAssignment_iff
      basis left right values row).mp (solved row)

/--
The single-constant problem obtained by selecting one column of a represented
matrix inequality.  A column assignment gives one homomorphism context for
each variable and must satisfy every row at the selected constant.
-/
def columnRepresentationBelow
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis)
    (values : Variable → HomContext Hom) : Prop :=
  ∀ row,
    (∑ index, left.1 row index * values index) +
        left.2 row basis ≤
      (∑ index, right.1 row index * values index) +
        right.2 row basis

/-- A full matrix solution restricts to a solution of every column. -/
theorem decomposeMatrixSolution
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (values : Matrix Variable Basis (HomContext Hom))
    (solution : matrixRepresentationBelow left right values)
    (basis : Basis) :
    columnRepresentationBelow left right basis
      (fun index => values index basis) := by
  intro row
  exact solution row basis

/-- Independently chosen column solutions assemble into a matrix solution. -/
theorem composeMatrixSolution
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (solutions :
      ∀ basis, ∃ values : Variable → HomContext Hom,
        columnRepresentationBelow left right basis values) :
    ∃ values : Matrix Variable Basis (HomContext Hom),
      matrixRepresentationBelow left right values := by
  classical
  choose columns columnSolutions using solutions
  refine ⟨fun index basis => columns basis index, ?_⟩
  intro row basis
  exact columnSolutions basis row

/-- A full solution exists exactly when every constant column is solvable. -/
theorem matrixSolution_iff_columnSolutions
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) :
    (∃ values : Matrix Variable Basis (HomContext Hom),
        matrixRepresentationBelow left right values) ↔
      ∀ basis, ∃ values : Variable → HomContext Hom,
        columnRepresentationBelow left right basis values := by
  constructor
  · rintro ⟨values, solution⟩ basis
    exact ⟨fun index => values index basis,
      decomposeMatrixSolution left right values solution basis⟩
  · exact composeMatrixSolution left right

end ACUIHE.Solver.Linear
