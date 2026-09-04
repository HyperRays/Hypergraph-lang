import ACUIHE.Solver.Search.ColumnAutomaton

/-! Exact composition of independently solved ACUIh matrix columns. -/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u

/-- Solve every constant column and assemble the resulting assignments into
one matrix.  The finite universal test is executable because `Basis` is
explicitly enumerable. -/
def solveMatrix?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) :
    Option (Matrix Variable Basis (HomContext Hom)) :=
  if complete : ∀ basis, (solveColumn? left right basis).isSome then
    some fun index basis =>
      (solveColumn? left right basis).get (complete basis) index
  else
    none

/-- A matrix returned by exact column composition satisfies the represented
inequality in every row and basis coordinate. -/
theorem solveMatrix?_sound
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    {values : Matrix Variable Basis (HomContext Hom)}
    (result : solveMatrix? left right = some values) :
    matrixRepresentationBelow left right values := by
  unfold solveMatrix? at result
  split at result
  next complete =>
    cases result
    intro row basis
    have found : solveColumn? left right basis = some
        ((solveColumn? left right basis).get (complete basis)) :=
      (Option.some_get (complete basis)).symm
    exact solveColumn?_sound left right basis found row
  next incomplete =>
    simp at result

/-- If any matrix solution exists, exact column composition returns one. -/
theorem solveMatrix?_complete
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (solution : ∃ values : Matrix Variable Basis (HomContext Hom),
      matrixRepresentationBelow left right values) :
    ∃ values, solveMatrix? left right = some values := by
  rcases solution with ⟨values, solved⟩
  have complete : ∀ basis, (solveColumn? left right basis).isSome := by
    intro basis
    rcases solveColumn?_complete left right basis
        ⟨fun index => values index basis,
          decomposeMatrixSolution left right values solved basis⟩ with
      ⟨column, found⟩
    rw [found]
    trivial
  refine ⟨(fun index basis =>
    (solveColumn? left right basis).get (complete basis) index), ?_⟩
  simp [solveMatrix?, complete]

/-- Matrix-search failure is equivalent to genuine unsatisfiability. -/
theorem solveMatrix?_eq_none_iff
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) :
    solveMatrix? left right = none ↔
      ¬ ∃ values : Matrix Variable Basis (HomContext Hom),
        matrixRepresentationBelow left right values := by
  constructor
  · intro failed solution
    rcases solveMatrix?_complete left right solution with ⟨values, found⟩
    rw [failed] at found
    contradiction
  · intro unsatisfiable
    cases found : solveMatrix? left right with
    | none => rfl
    | some values =>
        exact False.elim (unsatisfiable ⟨values,
          solveMatrix?_sound left right found⟩)

/-- Solve a finite family of columns whose row representations may depend on
the selected basis element.  This is the exact column product used by the
ACUIhE combination layer, where a dependency restriction is local to one
alien column. -/
def solveColumnFamily?
    {Row Variable Basis Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Basis]
    [FinEnum Hom] [Encodable Hom]
    (representations : Basis →
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom)) ×
      (Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))) :
    Option (Matrix Variable Basis (HomContext Hom)) :=
  if complete : ∀ basis,
      (solveColumn? (representations basis).1
        (representations basis).2 basis).isSome then
    some fun index basis =>
      (solveColumn? (representations basis).1
        (representations basis).2 basis).get (complete basis) index
  else
    none

/-- Every assembled member of an exact column family satisfies its own
selected representation. -/
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
    (result : solveColumnFamily? representations = some values) :
    ∀ row basis,
      evaluateMatrixRepresentation (representations basis).1 values row basis ≤
        evaluateMatrixRepresentation (representations basis).2 values row basis := by
  unfold solveColumnFamily? at result
  split at result
  next complete =>
    cases result
    intro row basis
    have found : solveColumn? (representations basis).1
        (representations basis).2 basis = some
          ((solveColumn? (representations basis).1
            (representations basis).2 basis).get (complete basis)) :=
      (Option.some_get (complete basis)).symm
    exact solveColumn?_sound (representations basis).1
      (representations basis).2 basis found row
  next incomplete =>
    simp at result

/-- If each selected representation has a column solution, their finite
product returns a matrix. -/
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
  have complete : ∀ basis,
      (solveColumn? (representations basis).1
        (representations basis).2 basis).isSome := by
    intro basis
    rcases solveColumn?_complete (representations basis).1
        (representations basis).2 basis
        ⟨fun index => values index basis, fun row => solved row basis⟩ with
      ⟨column, found⟩
    rw [found]
    trivial
  refine ⟨fun index basis =>
    (solveColumn? (representations basis).1
      (representations basis).2 basis).get (complete basis) index, ?_⟩
  simp [solveColumnFamily?, complete]

end ACUIHE.Solver.Search
