import ACUIHE.Solver.Search.Words

/-!
Finite-language linear inequality systems.

This is the source-independent problem solved by the pending-suffix
automaton.  A problem supplies variable coefficients and an inhomogeneous
coefficient on each side of every row.  It does not mention normal forms,
basis constants, or matrices.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u

/-- A finite family of two-sided linear inequalities over finite languages
of homomorphism words.  The Boolean side is false on the left and true on the
right. -/
structure FiniteLanguageSystem
    (Row Variable Hom : Type u) where
  coefficient : Bool → Row → Variable → HomContext Hom
  constant : Bool → Row → HomContext Hom

namespace FiniteLanguageSystem

/-- Evaluate one side of one row under a proposed finite-language
assignment. -/
def evaluate
    {Row Variable Hom : Type u}
    [FinEnum Variable] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (side : Bool) (values : Variable → HomContext Hom) (row : Row) :
    HomContext Hom :=
  (∑ index, problem.coefficient side row index * values index) +
    problem.constant side row

/-- A solution makes the left language a subset of the right language in
every row. -/
def IsSolution
    {Row Variable Hom : Type u}
    [FinEnum Variable] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) : Prop :=
  ∀ row, problem.evaluate false values row ≤ problem.evaluate true values row

/-- Maximum word length among all coefficients in a finite problem. -/
def pathBound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) : Nat :=
  max
    (Finset.univ.sup fun side : Bool =>
      Finset.univ.sup fun row =>
        Finset.univ.sup fun index =>
          contextPathBound (problem.coefficient side row index))
    (Finset.univ.sup fun side : Bool =>
      Finset.univ.sup fun row =>
        contextPathBound (problem.constant side row))

theorem coefficient_path_length_le_pathBound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (side : Bool) (row : Row) (index : Variable)
    {path : List Hom}
    (membership : path ∈ (problem.coefficient side row index).paths) :
    path.length ≤ problem.pathBound := by
  apply le_trans (path_length_le_contextPathBound _ membership)
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun index =>
      contextPathBound (problem.coefficient side row index))
    (Finset.mem_univ index))
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun row =>
      Finset.univ.sup fun index =>
        contextPathBound (problem.coefficient side row index))
    (Finset.mem_univ row))
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun side : Bool =>
      Finset.univ.sup fun row =>
        Finset.univ.sup fun index =>
          contextPathBound (problem.coefficient side row index))
    (Finset.mem_univ side))
  exact Nat.le_max_left _ _

theorem constant_path_length_le_pathBound
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom)
    (side : Bool) (row : Row) {path : List Hom}
    (membership : path ∈ (problem.constant side row).paths) :
    path.length ≤ problem.pathBound := by
  apply le_trans (path_length_le_contextPathBound _ membership)
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun row => contextPathBound (problem.constant side row))
    (Finset.mem_univ row))
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun side : Bool =>
      Finset.univ.sup fun row =>
        contextPathBound (problem.constant side row))
    (Finset.mem_univ side))
  exact Nat.le_max_right _ _

end FiniteLanguageSystem

end ACUIHE.Solver.Search
