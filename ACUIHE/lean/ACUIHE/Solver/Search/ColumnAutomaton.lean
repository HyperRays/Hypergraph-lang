import ACUIHE.Solver.Search.FiniteLanguageSystem.Solver

/-!
ACUIh matrix adapter for the generic finite-language column solver.

The generic automaton knows only coefficient languages, rows, and variables.
This module selects one basis coordinate from the ACUIh matrix representation
and preserves the original public `solveColumn?` API.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u

attribute [local instance]
  finiteLanguageDecidableEq finiteLanguageBoolFinEnum

/-- Select one basis coordinate of an ACUIh matrix inequality as a generic
finite-language column problem. -/
def matrixColumnSystem
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) : FiniteLanguageSystem Row Variable Hom where
  coefficient side row index :=
    if side then right.1 row index else left.1 row index
  constant side row :=
    if side then right.2 row basis else left.2 row basis

/-- The generic problem semantics is definitionally the selected ACUIh matrix
column inequality. -/
theorem matrixColumnSystem_isSolution_iff
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (values : Variable → HomContext Hom) :
    (matrixColumnSystem left right basis).IsSolution values ↔
      columnRepresentationBelow left right basis values := by
  rfl

/-- Exact, total search for one ACUIh matrix column. -/
def solveColumn?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) : Option (Variable → HomContext Hom) :=
  (matrixColumnSystem left right basis).solve?

/-- Any column assignment returned by search satisfies every input row. -/
theorem solveColumn?_sound
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) {values : Variable → HomContext Hom}
    (result : solveColumn? left right basis = some values) :
    columnRepresentationBelow left right basis values := by
  apply (matrixColumnSystem_isSolution_iff left right basis values).mp
  exact (matrixColumnSystem left right basis).solve?_sound result

/-- Every finite column solution is found. -/
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
  exact (matrixColumnSystem left right basis).solve?_complete genericSolution

/-- Failure of column search is equivalent to genuine unsatisfiability. -/
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
  rw [show solveColumn? left right basis =
      (matrixColumnSystem left right basis).solve? by rfl,
    (matrixColumnSystem left right basis).solve?_eq_none_iff]
  apply not_congr
  constructor
  · rintro ⟨values, solved⟩
    exact ⟨values,
      (matrixColumnSystem_isSolution_iff left right basis values).mp solved⟩
  · rintro ⟨values, solved⟩
    exact ⟨values,
      (matrixColumnSystem_isSolution_iff left right basis values).mpr solved⟩

end ACUIHE.Solver.Search
