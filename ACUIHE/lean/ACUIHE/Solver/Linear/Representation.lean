import ACUIHE.NormalForm.Canonical
import ACUIHE.ACUIh
import ACUIHE.Solver.Linear.Matrix
import ACUIHE.Solver.Solution

/-! Matrix representations of finite ACUIh expressions. -/

namespace ACUIHE.Solver.Linear

open ACUIHE.Solver.NormalForm.Internal

universe u v w x

local instance representationEncodableDecidableEq {α : Type*} [Encodable α] :
    DecidableEq α :=
  Encodable.decidableEqOfEncodable α

local instance homContextAddIdempotent {Hom : Type*} [Encodable Hom] :
    Std.IdempotentOp (fun left right : HomContext Hom => left + right) :=
  ⟨HomContext.add_self⟩

/--
The finite collection of homomorphism paths surrounding occurrences of one
variable in a normal form. Complete `E` blocks are deliberately ignored:
the matrix representation is used on E-free ACUIh forms.
-/
def variableCoefficient
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Var) :
    HomContext Hom :=
  normalForm.fold 0 (· + ·)
    (fun _ _ => 0)
    (fun path name => if name = selected then {path} else 0)
    (fun _ _ => 0)

/--
The finite collection of homomorphism paths surrounding occurrences of one
constant in a normal form.
-/
def constantCoefficient
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (constant : Const) :
    HomContext Hom :=
  normalForm.fold 0 (· + ·)
    (fun path name => if name = constant then {path} else 0)
    (fun _ _ => 0)
    (fun _ _ => 0)

@[simp]
theorem variableCoefficient_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (selected : Var) :
    variableCoefficient
        (∅ : NormalForm Const Var Hom) selected = 0 := by
  simp [variableCoefficient]

@[simp]
theorem constantCoefficient_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (selected : Const) :
    constantCoefficient
        (∅ : NormalForm Const Var Hom) selected = 0 := by
  simp [constantCoefficient]

@[simp]
theorem variableCoefficient_singleton_constant
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Const) (selected : Var) :
    variableCoefficient
        ({(path, .constant name)} : NormalForm Const Var Hom) selected = 0 := by
  simp [variableCoefficient]

@[simp]
theorem variableCoefficient_singleton_variable
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name selected : Var) :
    variableCoefficient
        ({(path, .variable name)} : NormalForm Const Var Hom) selected =
      if name = selected then {path} else 0 := by
  simp [variableCoefficient]

@[simp]
theorem constantCoefficient_singleton_constant
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name selected : Const) :
    constantCoefficient
        ({(path, .constant name)} : NormalForm Const Var Hom) selected =
      if name = selected then {path} else 0 := by
  simp [constantCoefficient]

@[simp]
theorem constantCoefficient_singleton_variable
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Var) (selected : Const) :
    constantCoefficient
        ({(path, .variable name)} : NormalForm Const Var Hom) selected = 0 := by
  simp [constantCoefficient]

theorem variableCoefficient_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) (selected : Var) :
    variableCoefficient (left ∪ right) selected =
      variableCoefficient left selected + variableCoefficient right selected := by
  unfold variableCoefficient
  rw [NormalForm.fold_union (zeroRight := fun value => add_zero value)]

theorem constantCoefficient_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) (selected : Const) :
    constantCoefficient (left ∪ right) selected =
      constantCoefficient left selected + constantCoefficient right selected := by
  unfold constantCoefficient
  rw [NormalForm.fold_union (zeroRight := fun value => add_zero value)]

theorem variableCoefficient_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) (selected : Var) :
    variableCoefficient (prefixHom name normalForm) selected =
      ({[name]} : HomContext Hom) * variableCoefficient normalForm selected := by
  unfold variableCoefficient
  apply NormalForm.fold_prefixHom
      (zeroRight := fun value : HomContext Hom => add_zero value)
      (mapResult := fun context => ({[name]} : HomContext Hom) * context)
  · simp
  · intro left right
    exact mul_add _ _ _
  · intro path constantName
    simp
  · intro path variableName
    by_cases equality : variableName = selected
    · simp only [equality, ↓reduceIte]
      apply HomContext.ext
      change
        ({name :: path} : Finset (List Hom)) =
          Finset.image₂ (fun left right => left ++ right)
            ({[name]} : Finset (List Hom)) ({path} : Finset (List Hom))
      simp
    · simp [equality]
  · intro path body
    simp

theorem constantCoefficient_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) (selected : Const) :
    constantCoefficient (prefixHom name normalForm) selected =
      ({[name]} : HomContext Hom) * constantCoefficient normalForm selected := by
  unfold constantCoefficient
  apply NormalForm.fold_prefixHom
      (zeroRight := fun value : HomContext Hom => add_zero value)
      (mapResult := fun context => ({[name]} : HomContext Hom) * context)
  · simp
  · intro left right
    exact mul_add _ _ _
  · intro path constantName
    by_cases equality : constantName = selected
    · simp only [equality, ↓reduceIte]
      apply HomContext.ext
      change
        ({name :: path} : Finset (List Hom)) =
          Finset.image₂ (fun left right => left ++ right)
            ({[name]} : Finset (List Hom)) ({path} : Finset (List Hom))
      simp
    · simp [equality]
  · intro path variableName
    simp
  · intro path body
    simp

private theorem constantCoefficient_normalize_reifyPath_const
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name selected : Const) :
    constantCoefficient
        (normalize (reifyPath path (.const name : Term Const Var Hom))) selected =
      if name = selected then {path} else 0 := by
  induction path with
  | nil =>
      simp [reifyPath, constantCoefficient, constantForm]
  | cons hom path inductionHypothesis =>
      change constantCoefficient
          (normalize (.hom hom (reifyPath path (.const name)))) selected = _
      rw [normalize_hom, constantCoefficient_prefixHom,
        inductionHypothesis]
      by_cases equality : name = selected
      · subst name
        simp only [if_pos]
        apply HomContext.ext
        change
          Finset.image₂ (fun leftPath rightPath => leftPath ++ rightPath)
              ({[hom]} : Finset (List Hom)) ({path} : Finset (List Hom)) =
            ({hom :: path} : Finset (List Hom))
        simp
      · simp [equality]

private theorem constantCoefficient_normalize_reifyPath_var
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Var) (selected : Const) :
    constantCoefficient
        (normalize (reifyPath path (.var name : Term Const Var Hom))) selected =
      0 := by
  induction path with
  | nil => simp [reifyPath, constantCoefficient, variableForm]
  | cons hom path inductionHypothesis =>
      change constantCoefficient
          (normalize (.hom hom (reifyPath path (.var name)))) selected = 0
      rw [normalize_hom, constantCoefficient_prefixHom,
        inductionHypothesis, mul_zero]

private theorem constantCoefficient_normalize_reifyPath_free
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (body : Term Const Var Hom) (selected : Const) :
    constantCoefficient
        (normalize (reifyPath path (.free body : Term Const Var Hom))) selected =
      0 := by
  induction path with
  | nil =>
      by_cases bodyZero : normalize body = ∅
      · rw [show normalize (reifyPath [] (.free body)) =
            wrapE (normalize body) by rfl,
          bodyZero, wrapE_empty, constantCoefficient_empty]
      · rw [show normalize (reifyPath [] (.free body)) =
            wrapE (normalize body) by rfl,
          wrapE_of_ne_empty bodyZero]
        simp [constantCoefficient]
  | cons hom path inductionHypothesis =>
      change constantCoefficient
          (normalize (.hom hom (reifyPath path (.free body)))) selected = 0
      rw [normalize_hom, constantCoefficient_prefixHom,
        inductionHypothesis, mul_zero]

/-- Canonicalizing a normal form never changes any outer constant
coefficient.  Canonicalization only recursively changes `E` bodies. -/
@[simp]
theorem constantCoefficient_canonicalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Const) :
    constantCoefficient (canonicalize normalForm) selected =
      constantCoefficient normalForm selected := by
  unfold canonicalize reify
  exact NormalForm.fold_hom
    (fun term : Term Const Var Hom =>
      constantCoefficient (normalize term) selected)
    (.zero : Term Const Var Hom) (.add)
    (fun path name => reifyPath path (.const name))
    (fun path name => reifyPath path (.var name))
    (fun path body => reifyPath path (.free body))
    (0 : HomContext Hom) (· + ·)
    (fun path name => if name = selected then {path} else 0)
    (fun _ _ => 0) (fun _ _ => 0)
    (by simp [constantCoefficient])
    (by intro left right; simp [constantCoefficient_union])
    (constantCoefficient_normalize_reifyPath_const · · selected)
    (constantCoefficient_normalize_reifyPath_var · · selected)
    (constantCoefficient_normalize_reifyPath_free · · selected)
    normalForm

/-- The variables occurring outside complete `E` blocks. -/
def variableSupport
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Finset Var :=
  normalForm.fold ∅ (· ∪ ·)
    (fun _ _ => ∅)
    (fun _ name => {name})
    (fun _ _ => ∅)

/-- The constants occurring outside complete `E` blocks. -/
def constantSupport
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Finset Const :=
  normalForm.fold ∅ (· ∪ ·)
    (fun _ name => {name})
    (fun _ _ => ∅)
    (fun _ _ => ∅)

@[simp]
theorem variableSupport_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    variableSupport (∅ : NormalForm Const Var Hom) = ∅ := by
  simp [variableSupport]

@[simp]
theorem constantSupport_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    constantSupport (∅ : NormalForm Const Var Hom) = ∅ := by
  simp [constantSupport]

@[simp]
theorem variableSupport_constantForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    variableSupport (constantForm (Var := Var) (Hom := Hom) name) = ∅ := by
  simp [variableSupport, constantForm]

@[simp]
theorem constantSupport_constantForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    constantSupport (constantForm (Var := Var) (Hom := Hom) name) = {name} := by
  simp [constantSupport, constantForm]

@[simp]
theorem variableSupport_variableForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    variableSupport (variableForm (Const := Const) (Hom := Hom) name) = {name} := by
  simp [variableSupport, variableForm]

@[simp]
theorem constantSupport_variableForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    constantSupport (variableForm (Const := Const) (Hom := Hom) name) = ∅ := by
  simp [constantSupport, variableForm]

theorem variableSupport_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    variableSupport (left ∪ right) =
      variableSupport left ∪ variableSupport right := by
  unfold variableSupport
  apply NormalForm.fold_union
  exact Finset.union_empty

theorem constantSupport_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    constantSupport (left ∪ right) =
      constantSupport left ∪ constantSupport right := by
  unfold constantSupport
  apply NormalForm.fold_union
  exact Finset.union_empty

@[simp]
theorem variableSupport_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) :
    variableSupport (prefixHom name normalForm) = variableSupport normalForm := by
  unfold variableSupport
  simpa only [id_eq] using NormalForm.fold_prefixHom
    (∅ : Finset Var) (· ∪ ·) Finset.union_empty
    (fun _ _ => ∅) (fun _ name => {name}) (fun _ _ => ∅)
    name id rfl (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) normalForm

@[simp]
theorem constantSupport_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) :
    constantSupport (prefixHom name normalForm) = constantSupport normalForm := by
  unfold constantSupport
  simpa only [id_eq] using NormalForm.fold_prefixHom
    (∅ : Finset Const) (· ∪ ·) Finset.union_empty
    (fun _ name => {name}) (fun _ _ => ∅) (fun _ _ => ∅)
    name id rfl (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) normalForm

/-- The variable-coefficient matrix `A` of a row-indexed family of expressions. -/
def variableMatrix
    {Row : Type x} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom) (variableSet : Finset Var) :
    Matrix Row (↥variableSet) (HomContext Hom) :=
  fun row index => variableCoefficient (expressions row) index.1

/-- The constant matrix `C` of a row-indexed family of expressions. -/
def constantMatrix
    {Row : Type x} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom) (basis : Finset Const) :
    Matrix Row (↥basis) (HomContext Hom) :=
  fun row constant => constantCoefficient (expressions row) constant.1

/--
The matrix representation `(A, C)` of a family of ACUIh expressions.

For a single expression take `Row := Unit`. The finite sets select the local
variable and constant coordinates; correctness requires them to contain the
corresponding supports.
-/
def matrixRepresentation
    {Row : Type x} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom)
    (variableSet : Finset Var) (basis : Finset Const) :
    Matrix Row (↥variableSet) (HomContext Hom) ×
      Matrix Row (↥basis) (HomContext Hom) :=
  (variableMatrix expressions variableSet, constantMatrix expressions basis)

/--
The representation of one expression on exactly its local variable and
constant supports.
-/
def localMatrixRepresentation
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    Matrix Unit (↥(variableSupport normalForm)) (HomContext Hom) ×
      Matrix Unit (↥(constantSupport normalForm)) (HomContext Hom) :=
  matrixRepresentation (fun _ => normalForm)
    (variableSupport normalForm) (constantSupport normalForm)

@[simp]
theorem matrixRepresentation_first
    {Row : Type x} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom)
    (variableSet : Finset Var) (basis : Finset Const) :
    (matrixRepresentation expressions variableSet basis).1 =
      variableMatrix expressions variableSet :=
  rfl

@[simp]
theorem matrixRepresentation_second
    {Row : Type x} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom)
    (variableSet : Finset Var) (basis : Finset Const) :
    (matrixRepresentation expressions variableSet basis).2 =
      constantMatrix expressions basis :=
  rfl

/-- Evaluate `(A, C)` at a variable matrix `V`, obtaining `A * V + C`. -/
def evaluateMatrixRepresentation
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (values : Matrix Variable Basis (HomContext Hom)) :
    Matrix Row Basis (HomContext Hom) :=
  representation.1 * values + representation.2

@[simp]
theorem evaluateMatrixRepresentation_apply
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (values : Matrix Variable Basis (HomContext Hom))
    (row : Row) (basis : Basis) :
    evaluateMatrixRepresentation representation values row basis =
      (∑ index, representation.1 row index * values index basis) +
        representation.2 row basis :=
  rfl

/-- Entry-wise form of `A * V + C` for a represented family of expressions. -/
theorem evaluate_matrixRepresentation_apply
    {Row : Type x} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom)
    (variableSet : Finset Var) (basis : Finset Const)
    (values : Matrix (↥variableSet) (↥basis) (HomContext Hom))
    (row : Row) (constant : ↥basis) :
    evaluateMatrixRepresentation
        (matrixRepresentation expressions variableSet basis) values row constant =
      (∑ index : ↥variableSet,
          variableCoefficient (expressions row) index.1 * values index constant) +
        constantCoefficient (expressions row) constant.1 :=
  rfl

private theorem finsetFoldAnd_eq_true_of_mem
    {α : Type*} [DecidableEq α] (function : α → Bool)
    (set : Finset α) {value : α} (membership : value ∈ set)
    (folded : set.fold (fun left right => left && right) true function = true) :
    function value = true := by
  induction set using Finset.induction_on with
  | empty => simp at membership
  | @insert head tail notMember inductionHypothesis =>
      rw [Finset.fold_insert notMember] at folded
      have both := Bool.and_eq_true_iff.mp folded
      rw [Finset.mem_insert] at membership
      rcases membership with equality | membership
      · subst value
        exact both.1
      · exact inductionHypothesis membership both.2

private theorem variableCoefficient_paths
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Var) :
    (variableCoefficient normalForm selected).paths =
      (RecursiveFinset.toFinset normalForm.raw).biUnion
        (fun summand =>
          match summand.2 with
          | .variable name => if name = selected then {summand.1} else ∅
          | _ => ∅) := by
  unfold variableCoefficient NormalForm.fold
  rw [rawFold_toFinset
    (zeroRight := fun value : HomContext Hom => add_zero value)
    (valid := normalForm.valid.outer)]
  generalize RecursiveFinset.toFinset normalForm.raw = summands
  induction summands using Finset.induction_on with
  | empty => rfl
  | @insert summand summands notMember inductionHypothesis =>
      rw [Finset.fold_insert_idem]
      rw [Finset.biUnion_insert]
      rw [HomContext.paths_add, inductionHypothesis]
      rcases summand with ⟨path, atom⟩
      cases atom
      · simp [rawFoldSummand]
      · rename_i name
        by_cases equality : name = selected
        · subst name
          simp only [rawFoldSummand, ↓reduceIte]
          congr 1
        · simp [rawFoldSummand, equality]
      · simp [rawFoldSummand]

private theorem constantCoefficient_paths
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Const) :
    (constantCoefficient normalForm selected).paths =
      (RecursiveFinset.toFinset normalForm.raw).biUnion
        (fun summand =>
          match summand.2 with
          | .constant name => if name = selected then {summand.1} else ∅
          | _ => ∅) := by
  unfold constantCoefficient NormalForm.fold
  rw [rawFold_toFinset
    (zeroRight := fun value : HomContext Hom => add_zero value)
    (valid := normalForm.valid.outer)]
  generalize RecursiveFinset.toFinset normalForm.raw = summands
  induction summands using Finset.induction_on with
  | empty => rfl
  | @insert summand summands notMember inductionHypothesis =>
      rw [Finset.fold_insert_idem]
      rw [Finset.biUnion_insert]
      rw [HomContext.paths_add, inductionHypothesis]
      rcases summand with ⟨path, atom⟩
      cases atom
      · rename_i name
        by_cases equality : name = selected
        · subst name
          simp only [rawFoldSummand, ↓reduceIte]
          congr 1
        · simp [rawFoldSummand, equality]
      · simp [rawFoldSummand]
      · simp [rawFoldSummand]

private theorem variableSupport_eq_biUnion
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    variableSupport normalForm =
      (RecursiveFinset.toFinset normalForm.raw).biUnion
        (fun summand =>
          match summand.2 with
          | .variable name => {name}
          | _ => ∅) := by
  unfold variableSupport NormalForm.fold
  rw [rawFold_toFinset
    (zeroRight := fun value : Finset Var => Finset.union_empty value)
    (valid := normalForm.valid.outer)]
  generalize RecursiveFinset.toFinset normalForm.raw = summands
  induction summands using Finset.induction_on with
  | empty => rfl
  | @insert summand summands notMember inductionHypothesis =>
      rw [Finset.fold_insert_idem]
      rw [Finset.biUnion_insert]
      rw [inductionHypothesis]
      rcases summand with ⟨path, atom⟩
      cases atom <;> rfl

private theorem constantSupport_eq_biUnion
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    constantSupport normalForm =
      (RecursiveFinset.toFinset normalForm.raw).biUnion
        (fun summand =>
          match summand.2 with
          | .constant name => {name}
          | _ => ∅) := by
  unfold constantSupport NormalForm.fold
  rw [rawFold_toFinset
    (zeroRight := fun value : Finset Const => Finset.union_empty value)
    (valid := normalForm.valid.outer)]
  generalize RecursiveFinset.toFinset normalForm.raw = summands
  induction summands using Finset.induction_on with
  | empty => rfl
  | @insert summand summands notMember inductionHypothesis =>
      rw [Finset.fold_insert_idem]
      rw [Finset.biUnion_insert]
      rw [inductionHypothesis]
      rcases summand with ⟨path, atom⟩
      cases atom <;> rfl

@[simp]
theorem mem_variableCoefficient
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Var)
    (path : List Hom) :
    path ∈ (variableCoefficient normalForm selected).paths ↔
      (path, RawNormalAtom.variable selected) ∈
        RecursiveFinset.toFinset normalForm.raw := by
  rw [variableCoefficient_paths]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨candidatePath, atom⟩, membership, selectedMembership⟩
    cases atom
    · simp at selectedMembership
    · rename_i name
      by_cases equality : name = selected
      · subst name
        simp only [↓reduceIte, Finset.mem_singleton] at selectedMembership
        subst candidatePath
        exact membership
      · simp [equality] at selectedMembership
    · simp at selectedMembership
  · intro membership
    exact ⟨(path, RawNormalAtom.variable selected), membership, by simp⟩

@[simp]
theorem mem_constantCoefficient
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Const)
    (path : List Hom) :
    path ∈ (constantCoefficient normalForm selected).paths ↔
      (path, RawNormalAtom.constant selected) ∈
        RecursiveFinset.toFinset normalForm.raw := by
  rw [constantCoefficient_paths]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨candidatePath, atom⟩, membership, selectedMembership⟩
    cases atom
    · rename_i name
      by_cases equality : name = selected
      · subst name
        simp only [↓reduceIte, Finset.mem_singleton] at selectedMembership
        subst candidatePath
        exact membership
      · simp [equality] at selectedMembership
    · simp at selectedMembership
    · simp at selectedMembership
  · intro membership
    exact ⟨(path, RawNormalAtom.constant selected), membership, by simp⟩

@[simp]
theorem mem_variableSupport
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Var) :
    selected ∈ variableSupport normalForm ↔
      ∃ path, (path, RawNormalAtom.variable selected) ∈
        RecursiveFinset.toFinset normalForm.raw := by
  rw [variableSupport_eq_biUnion]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨path, atom⟩, membership, selectedMembership⟩
    cases atom
    · simp at selectedMembership
    · rename_i name
      simp only [Finset.mem_singleton] at selectedMembership
      subst name
      exact ⟨path, membership⟩
    · simp at selectedMembership
  · rintro ⟨path, membership⟩
    exact ⟨(path, RawNormalAtom.variable selected), membership, by simp⟩

@[simp]
theorem mem_constantSupport
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Const) :
    selected ∈ constantSupport normalForm ↔
      ∃ path, (path, RawNormalAtom.constant selected) ∈
        RecursiveFinset.toFinset normalForm.raw := by
  rw [constantSupport_eq_biUnion]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨path, atom⟩, membership, selectedMembership⟩
    cases atom
    · rename_i name
      simp only [Finset.mem_singleton] at selectedMembership
      subst name
      exact ⟨path, membership⟩
    · simp at selectedMembership
    · simp at selectedMembership
  · rintro ⟨path, membership⟩
    exact ⟨(path, RawNormalAtom.constant selected), membership, by simp⟩

private theorem no_eOperator_of_isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {normalForm : NormalForm Const Var Hom}
    (acuih : isACUIh normalForm = true)
    (path : List Hom) (body : RawNormalForm Const Var Hom) :
    (path, RawNormalAtom.eOperator body) ∉
      RecursiveFinset.toFinset normalForm.raw := by
  intro membership
  unfold isACUIh NormalForm.fold at acuih
  rw [rawFold_toFinset
    (zeroRight := fun value : Bool => Bool.and_true value)
    (valid := normalForm.valid.outer)] at acuih
  have selectedTrue := finsetFoldAnd_eq_true_of_mem
    (rawFoldSummand true (fun left right => left && right)
      (fun _ _ => true) (fun _ _ => true) (fun _ _ => false))
    (RecursiveFinset.toFinset normalForm.raw) membership acuih
  simp [rawFoldSummand] at selectedTrue

private theorem no_variable_of_isGround
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {normalForm : NormalForm Const Var Hom}
    (ground : normalForm.IsGround)
    (path : List Hom) (name : Var) :
    (path, RawNormalAtom.variable name) ∉
      RecursiveFinset.toFinset normalForm.raw := by
  intro membership
  unfold NormalForm.IsGround NormalForm.isGround NormalForm.fold at ground
  rw [rawFold_toFinset
    (zeroRight := fun value : Bool => Bool.and_true value)
    (valid := normalForm.valid.outer)] at ground
  have selectedTrue := finsetFoldAnd_eq_true_of_mem
    (rawFoldSummand true (fun left right => left && right)
      (fun _ _ => true) (fun _ _ => false) (fun _ bodyGround => bodyGround))
    (RecursiveFinset.toFinset normalForm.raw) membership ground
  simp [rawFoldSummand] at selectedTrue

/-- An E-free normal form over the empty variable type is ground. -/
theorem isGround_of_isACUIh_fin_zero
    {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (normalForm : NormalForm Const (Fin 0) Hom)
    (acuih : isACUIh normalForm = true) :
    normalForm.IsGround := by
  unfold NormalForm.IsGround NormalForm.isGround NormalForm.fold
  rw [rawFold_toFinset
    (zeroRight := fun value : Bool => Bool.and_true value)
    (valid := normalForm.valid.outer)]
  calc
    _ = Finset.fold (fun left right => left && right) true
        (fun _ => true) (RecursiveFinset.toFinset normalForm.raw) := by
      apply Finset.fold_congr
      intro summand membership
      rcases summand with ⟨path, atom⟩
      cases atom
      · simp [rawFoldSummand]
      · rename_i impossible
        exact impossible.elim0
      · rename_i body
        exact False.elim
          (no_eOperator_of_isACUIh acuih path body membership)
    _ = true := by
      rw [Finset.fold_const true (by decide)]
      simp

/--
When the ground left-hand side is ACUIh and supported on the selected basis,
`IsSolvedInequality` is exactly coefficient-wise inclusion on that basis.
The right-hand side may contain additional ground summands.
-/
theorem isSolvedInequality_iff_constantCoefficient_le
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) (basis : Finset Const)
    (leftACUIh : isACUIh left = true)
    (leftBasisComplete : constantSupport left ⊆ basis) :
    IsSolvedInequality left right ↔
      left.IsGround ∧ right.IsGround ∧
        ∀ constant : ↥basis,
          constantCoefficient left constant.1 ≤
            constantCoefficient right constant.1 := by
  constructor
  · rintro ⟨leftGround, rightGround, below⟩
    refine ⟨leftGround, rightGround, ?_⟩
    intro constant
    apply add_eq_right_iff_le.mp
    have coefficientEquality :=
      congrArg (fun normalForm => constantCoefficient normalForm constant.1) below
    change
      constantCoefficient (left ∪ right) constant.1 =
        constantCoefficient right constant.1 at coefficientEquality
    rw [constantCoefficient_union] at coefficientEquality
    exact coefficientEquality
  · rintro ⟨leftGround, rightGround, coefficientBelow⟩
    refine ⟨leftGround, rightGround, ?_⟩
    unfold Below
    apply NormalForm.ext_raw
    change left.raw ∪ right.raw = right.raw
    rw [← left.valid.outer, ← right.valid.outer,
      ← RecursiveFinset.ofFinset_union]
    apply congrArg RecursiveFinset.ofFinset
    apply Finset.union_eq_right.mpr
    intro summand membership
    rcases summand with ⟨path, atom⟩
    cases atom
    · rename_i name
      have nameInBasis : name ∈ basis :=
        leftBasisComplete
          ((mem_constantSupport left name).mpr ⟨path, membership⟩)
      have pathInLeft : path ∈ (constantCoefficient left name).paths :=
        (mem_constantCoefficient left name path).mpr membership
      have pathInRight : path ∈ (constantCoefficient right name).paths :=
        (HomContext.le_iff_paths_subset _ _).mp
          (coefficientBelow ⟨name, nameInBasis⟩) pathInLeft
      exact (mem_constantCoefficient right name path).mp pathInRight
    · rename_i name
      exact False.elim
        (no_variable_of_isGround leftGround path name membership)
    · rename_i body
      exact False.elim
        (no_eOperator_of_isACUIh leftACUIh path body membership)

private def matrixRepresentationSummands
    {Row : Type*} {Variable : Type*} {Basis : Type*}
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Fintype Variable] [Fintype Basis]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (variableName : Variable → Var) (constantName : Basis → Const)
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (row : Row) : Finset (RawNormalSummand Const Var Hom) :=
  (Finset.univ.biUnion fun index =>
    (representation.1 row index).paths.image fun path =>
      (path, RawNormalAtom.variable (variableName index))) ∪
  (Finset.univ.biUnion fun index =>
    (representation.2 row index).paths.image fun path =>
      (path, RawNormalAtom.constant (constantName index)))

/-- Decode one row of `(A, C)` into the ACUIh normal form it represents. -/
def decodeMatrixRepresentation
    {Row : Type*} {Variable : Type*} {Basis : Type*}
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Fintype Variable] [Fintype Basis]
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (variableName : Variable → Var) (constantName : Basis → Const)
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (row : Row) : NormalForm Const Var Hom :=
  ⟨RecursiveFinset.ofFinset
      (matrixRepresentationSummands
        variableName constantName representation row),
    by
      apply ValidNode.normalForm
      · simp [RecursiveFinset.Valid]
      · intro summand membership
        rw [RecursiveFinset.toFinset_ofFinset] at membership
        rcases Finset.mem_union.mp membership with variableMembership |
          constantMembership
        · rcases Finset.mem_biUnion.mp variableMembership with
            ⟨index, _, membership⟩
          rcases Finset.mem_image.mp membership with ⟨path, _, equality⟩
          subst summand
          exact ValidNode.variable _
        · rcases Finset.mem_biUnion.mp constantMembership with
            ⟨index, _, membership⟩
          rcases Finset.mem_image.mp membership with ⟨path, _, equality⟩
          subst summand
          exact ValidNode.constant _⟩

/--
`matrixRepresentation` fully encodes every ACUIh normal form when the chosen
coordinate sets contain all of its variables and constants.
-/
theorem decode_matrixRepresentation
    {Row : Type*} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom)
    (variableSet : Finset Var) (basis : Finset Const)
    (row : Row)
    (variablesComplete : variableSupport (expressions row) ⊆ variableSet)
    (basisComplete : constantSupport (expressions row) ⊆ basis)
    (acuih : isACUIh (expressions row) = true) :
    decodeMatrixRepresentation
        (fun index : ↥variableSet => index.1)
        (fun index : ↥basis => index.1)
        (matrixRepresentation expressions variableSet basis) row =
      expressions row := by
  apply NormalForm.ext_raw
  change RecursiveFinset.ofFinset _ = (expressions row).raw
  rw [← (expressions row).valid.outer]
  apply congrArg RecursiveFinset.ofFinset
  ext summand
  rcases summand with ⟨path, atom⟩
  cases atom
  · rename_i name
    simp [matrixRepresentationSummands, matrixRepresentation, variableMatrix,
      constantMatrix]
    intro membership
    exact basisComplete
      (mem_constantSupport (expressions row) name |>.mpr
        ⟨path, membership⟩)
  · rename_i name
    simp [matrixRepresentationSummands, matrixRepresentation, variableMatrix,
      constantMatrix]
    intro membership
    exact variablesComplete
      (mem_variableSupport (expressions row) name |>.mpr
        ⟨path, membership⟩)
  · rename_i body
    constructor
    · simp [matrixRepresentationSummands]
    · intro membership
      exact False.elim
        (no_eOperator_of_isACUIh acuih path body membership)

/-- The exact local-support representation decodes to its source normal form. -/
theorem decode_localMatrixRepresentation
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom)
    (acuih : isACUIh normalForm = true) :
    decodeMatrixRepresentation
        (fun index : ↥(variableSupport normalForm) => index.1)
        (fun index : ↥(constantSupport normalForm) => index.1)
        (localMatrixRepresentation normalForm) () = normalForm := by
  exact decode_matrixRepresentation
    (fun _ : Unit => normalForm)
    (variableSupport normalForm) (constantSupport normalForm)
    () Finset.Subset.rfl Finset.Subset.rfl acuih

/-- Decode a full (rather than `Finset`-subtype indexed) matrix row as a
ground ACUIh normal form. -/
def decodeGroundMatrix
    {Row : Type x} {Basis : Type u} {Hom : Type w}
    [Fintype Basis] [Encodable Basis] [Encodable Hom]
    (matrix : Matrix Row Basis (HomContext Hom))
    (row : Row) : NormalForm Basis (Fin 0) Hom :=
  decodeMatrixRepresentation
    (fun index : Fin 0 => index.elim0) id
    ((0 : Matrix Row (Fin 0) (HomContext Hom)), matrix) row

/-- Full-coordinate ground decoding preserves every coefficient exactly. -/
@[simp]
theorem constantCoefficient_decodeGroundMatrix
    {Row : Type x} {Basis : Type u} {Hom : Type w}
    [Fintype Basis] [Encodable Basis] [Encodable Hom]
    (matrix : Matrix Row Basis (HomContext Hom))
    (row : Row) (basis : Basis) :
    constantCoefficient (decodeGroundMatrix matrix row) basis =
      matrix row basis := by
  apply HomContext.ext
  ext path
  simp [decodeGroundMatrix, decodeMatrixRepresentation,
    matrixRepresentationSummands]

/-- Full-coordinate ground decoding is E-free. -/
@[simp]
theorem isACUIh_decodeGroundMatrix
    {Row : Type x} {Basis : Type u} {Hom : Type w}
    [Fintype Basis] [Encodable Basis] [Encodable Hom]
    (matrix : Matrix Row Basis (HomContext Hom)) (row : Row) :
    isACUIh (decodeGroundMatrix matrix row) = true := by
  unfold isACUIh NormalForm.fold decodeGroundMatrix
  change rawFold true (fun left right => left && right) _ _ _
    (RecursiveFinset.ofFinset _) = true
  rw [rawFold_ofFinset
    (zeroRight := fun value : Bool => Bool.and_true value)]
  calc
    _ = Finset.fold (fun left right => left && right) true
        (fun _ => true) _ := by
      apply Finset.fold_congr
      intro summand membership
      rcases summand with ⟨path, atom⟩
      cases atom <;>
        simp [matrixRepresentationSummands, rawFoldSummand] at membership ⊢
    _ = true := by
      rw [Finset.fold_const true (by decide)]
      simp

/-- Decode a row of constant coefficients as a ground ACUIh normal form. -/
def decodeConstantMatrix
    {Row : Type x} {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (matrix : Matrix Row (↥basis) (HomContext Hom))
    (row : Row) : NormalForm Const (Fin 0) Hom :=
  decodeMatrixRepresentation
    (fun index : Fin 0 => index.elim0)
    (fun constant : ↥basis => constant.1)
    ((0 : Matrix Row (Fin 0) (HomContext Hom)), matrix)
    row

/-- Decoding a constant matrix preserves every coefficient exactly. -/
@[simp]
theorem constantCoefficient_decodeConstantMatrix
    {Row : Type x} {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (matrix : Matrix Row (↥basis) (HomContext Hom))
    (row : Row) (constant : ↥basis) :
    constantCoefficient (decodeConstantMatrix basis matrix row) constant.1 =
      matrix row constant := by
  apply HomContext.ext
  ext path
  simp [decodeConstantMatrix, decodeMatrixRepresentation,
    matrixRepresentationSummands]

/-- A decoded constant matrix contains no variables. -/
@[simp]
theorem variableSupport_decodeConstantMatrix
    {Row : Type x} {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (matrix : Matrix Row (↥basis) (HomContext Hom))
    (row : Row) :
    variableSupport (decodeConstantMatrix basis matrix row) = ∅ := by
  let _ : DecidableEq (Fin 0) := representationEncodableDecidableEq
  let _ : Std.Commutative (fun left right : Finset (Fin 0) => left ∪ right) :=
    ⟨Finset.union_comm⟩
  let _ : Std.Associative (fun left right : Finset (Fin 0) => left ∪ right) :=
    ⟨Finset.union_assoc⟩
  let _ : Std.IdempotentOp (fun left right : Finset (Fin 0) => left ∪ right) :=
    ⟨Finset.union_self⟩
  unfold variableSupport NormalForm.fold
  unfold decodeConstantMatrix decodeMatrixRepresentation
  dsimp only [NormalFormImpl.raw]
  rw [rawFold_ofFinset
    (zero := (∅ : Finset (Fin 0)))
    (combine := fun left right : Finset (Fin 0) => left ∪ right)
    (onConstant := fun _ _ => (∅ : Finset (Fin 0)))
    (onVariable := fun _ name => ({name} : Finset (Fin 0)))
    (onEOperator := fun _ _ => (∅ : Finset (Fin 0)))
    (zeroRight := fun value : Finset (Fin 0) => Finset.union_empty value)]
  calc
    _ = Finset.fold (· ∪ ·) ∅ (fun _ => (∅ : Finset (Fin 0))) _ := by
      apply Finset.fold_congr
      intro summand membership
      rcases summand with ⟨path, atom⟩
      cases atom <;>
        simp [matrixRepresentationSummands, rawFoldSummand] at membership ⊢
    _ = ∅ := by
      rw [Finset.fold_const (∅ : Finset (Fin 0))
        (by simp only [Finset.empty_union])]
      simp

/-- Every constant in a decoded row belongs to the selected basis. -/
theorem constantSupport_decodeConstantMatrix_subset
    {Row : Type x} {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (matrix : Matrix Row (↥basis) (HomContext Hom))
    (row : Row) :
    constantSupport (decodeConstantMatrix basis matrix row) ⊆ basis := by
  intro constant membership
  rw [mem_constantSupport] at membership
  rcases membership with ⟨path, membership⟩
  simp [decodeConstantMatrix, decodeMatrixRepresentation,
    matrixRepresentationSummands] at membership
  exact membership.1

/-- Decoding constant coefficients always produces an E-free normal form. -/
@[simp]
theorem isACUIh_decodeConstantMatrix
    {Row : Type x} {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (matrix : Matrix Row (↥basis) (HomContext Hom))
    (row : Row) :
    isACUIh (decodeConstantMatrix basis matrix row) = true := by
  unfold isACUIh NormalForm.fold
  change rawFold true (fun left right => left && right) _ _ _
    (RecursiveFinset.ofFinset _) = true
  rw [rawFold_ofFinset
    (zeroRight := fun value : Bool => Bool.and_true value)]
  calc
    _ = Finset.fold (fun left right => left && right) true
        (fun _ => true) _ := by
      apply Finset.fold_congr
      intro summand membership
      rcases summand with ⟨path, atom⟩
      cases atom <;>
        simp [matrixRepresentationSummands, rawFoldSummand] at membership ⊢
    _ = true := by
      rw [Finset.fold_const true (by decide)]
      simp

/-- Decoding constant coefficients always produces a ground normal form. -/
@[simp]
theorem isGround_decodeConstantMatrix
    {Row : Type x} {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (matrix : Matrix Row (↥basis) (HomContext Hom))
    (row : Row) :
    (decodeConstantMatrix basis matrix row).IsGround := by
  unfold NormalForm.IsGround NormalForm.isGround NormalForm.fold
  change rawFold true (fun left right => left && right) _ _ _
    (RecursiveFinset.ofFinset _) = true
  rw [rawFold_ofFinset
    (zeroRight := fun value : Bool => Bool.and_true value)]
  calc
    _ = Finset.fold (fun left right => left && right) true
        (fun _ => true) _ := by
      apply Finset.fold_congr
      intro summand membership
      rcases summand with ⟨path, atom⟩
      cases atom <;>
        simp [matrixRepresentationSummands, rawFoldSummand] at membership ⊢
    _ = true := by
      rw [Finset.fold_const true (by decide)]
      simp

/-- Encoding a decoded constant matrix recovers the original coefficients. -/
theorem matrixRepresentation_decodeConstantMatrix
    {Row : Type x} {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (matrix : Matrix Row (↥basis) (HomContext Hom)) :
    matrixRepresentation
        (fun row => decodeConstantMatrix basis matrix row)
        (∅ : Finset (Fin 0)) basis =
      ((0 : Matrix Row (↥(∅ : Finset (Fin 0))) (HomContext Hom)), matrix) := by
  apply Prod.ext
  · funext row index
    exact index.1.elim0
  · funext row constant
    exact constantCoefficient_decodeConstantMatrix basis matrix row constant

/--
Decode the result `A * V + C` as the ground normal form obtained by applying
the represented variable assignment.
-/
def applyMatrixAssignment
    {Row : Type x} {Variable : Type v}
    {Const : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row (↥basis) (HomContext Hom))
    (values : Matrix Variable (↥basis) (HomContext Hom))
    (row : Row) : NormalForm Const (Fin 0) Hom :=
  decodeConstantMatrix basis
    (evaluateMatrixRepresentation representation values) row

/-- The normal-form representation of assignment application is `A * V + C`. -/
theorem matrixRepresentation_applyMatrixAssignment
    {Row : Type x} {Variable : Type v}
    {Const : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Const] [Encodable Hom]
    (basis : Finset Const)
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row (↥basis) (HomContext Hom))
    (values : Matrix Variable (↥basis) (HomContext Hom)) :
    matrixRepresentation
        (fun row => applyMatrixAssignment basis representation values row)
        (∅ : Finset (Fin 0)) basis =
      ((0 : Matrix Row (↥(∅ : Finset (Fin 0))) (HomContext Hom)),
        evaluateMatrixRepresentation representation values) := by
  exact matrixRepresentation_decodeConstantMatrix basis _

/-- A basis-wise inequality between two represented expressions. -/
def matrixRepresentationBelow
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [Fintype Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (values : Matrix Variable Basis (HomContext Hom)) : Prop :=
  ∀ row basis,
    evaluateMatrixRepresentation left values row basis ≤
      evaluateMatrixRepresentation right values row basis

end ACUIHE.Solver.Linear
