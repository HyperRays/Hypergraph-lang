import ACUIHE.Solver.ESubstitution
import ACUIHE.Solver.Search.Matrix
import ACUIHE.Solver.Search.E.Body

/-!
Finite alien-term certificates for ACUIh combined with the free unary
constructor `E`.

Every distinct canonical `E` body is purified to an alien constant.  Equal
bodies share one key, so the certificate does not duplicate syntax positions.
A certificate chooses whether that key denotes zero or an equality-class
representative, and assigns representatives a strict dependency rank.  The
equalities between `E` bodies and all rank restrictions are compiled into the
same ACUIh matrix problem as the outer inequality.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver
open ACUIHE.Solver.Linear
open ACUIHE.Solver.NormalForm.Internal

universe u v w x

local instance eCombinationDecidableEq {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

local instance eCombinationBoolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

local instance eCombinationHomContextAddIdempotent
    {Hom : Type*} [Encodable Hom] :
    Std.IdempotentOp (fun left right : HomContext Hom => left + right) :=
  ⟨HomContext.add_self⟩

/-- A finite combination certificate: an occurrence is either zero or is
identified with a representative; representatives carry a dependency rank. -/
abbrev EConfiguration
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :=
  (EOccurrence left right → Option (EOccurrence left right)) ×
    (EOccurrence left right → Fin (FinEnum.card (EOccurrence left right) + 1))

instance eConfigurationFinEnum
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    FinEnum (EConfiguration left right) :=
  inferInstance

/-- Constants of the purified ACUIh problem. -/
abbrev ECombinationBasis
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :=
  Const ⊕ EOccurrence left right

/-- Keep the enumeration-derived `Fintype` for the alien basis stable across
definitions.  Without this local priority, Lean can choose the extensionally
equal direct `Sum` instance in one theorem and the `FinEnum` instance in
another, making decoded normal forms definitionally different. -/
local instance (priority := 2000) eCombinationBasisFintype
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Fintype (ECombinationBasis left right) :=
  FinEnum.instFintype

/-- Look up the certificate class of a canonical `E` body. -/
def classOfBody?
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (body : NormalForm Const Var Hom) : Option (EOccurrence left right) :=
  (findEOccurrence? left right body).bind configuration.1

/-- Purify a normal form directly.  An `E(body)` is kept opaque and becomes
one representative constant (or zero); the recursively scanned body is used
only to recover its canonical normal form. -/
def purifyNormalFormScan
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (target : NormalForm Const Var Hom) :
    EPurificationScan Const Var Hom (ECombinationBasis left right) :=
  substituteEBlocksScan (classOfBody? left right configuration) target

/-- The normal-form-native purified image. -/
def purifyNormalForm
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (target : NormalForm Const Var Hom) :
    NormalForm (ECombinationBasis left right) Var Hom :=
  (purifyNormalFormScan left right configuration target).purified

@[simp]
theorem purifyNormalForm_isACUIh
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (target : NormalForm Const Var Hom) :
    isACUIh (purifyNormalForm left right configuration target) = true :=
  (purifyNormalFormScan left right configuration target).acuih

/-- Executable structural ACUIh test on raw terms. -/
def checkTermIsACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w} :
    Term Const Var Hom → Bool
  | .zero => true
  | .const _ => true
  | .var _ => true
  | .add first second => checkTermIsACUIh first && checkTermIsACUIh second
  | .hom _ body => checkTermIsACUIh body
  | .free _ => false

@[simp]
theorem checkTermIsACUIh_eq_true_iff
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (term : Term Const Var Hom) :
    checkTermIsACUIh term = true ↔ term.IsACUIh := by
  induction term <;> simp_all [checkTermIsACUIh, Term.IsACUIh]

private theorem checkTermIsACUIh_reifyPath_const
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (path : List Hom) (name : Const) :
    checkTermIsACUIh (reifyPath path (.const name : Term Const Var Hom)) = true := by
  induction path <;> simp_all [reifyPath, checkTermIsACUIh]

private theorem checkTermIsACUIh_reifyPath_var
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (path : List Hom) (name : Var) :
    checkTermIsACUIh (reifyPath path (.var name : Term Const Var Hom)) = true := by
  induction path <;> simp_all [reifyPath, checkTermIsACUIh]

private theorem checkTermIsACUIh_reifyPath_free
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (path : List Hom) (body : Term Const Var Hom) :
    checkTermIsACUIh (reifyPath path (.free body : Term Const Var Hom)) = false := by
  induction path <;> simp_all [reifyPath, checkTermIsACUIh]

/-- Reification and the public normal-form ACUIh checker agree exactly. -/
theorem checkTermIsACUIh_reify
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    checkTermIsACUIh (reify normalForm) = isACUIh normalForm := by
  unfold reify isACUIh
  exact NormalForm.fold_hom
    checkTermIsACUIh
    (.zero : Term Const Var Hom) (.add)
    (fun path name => reifyPath path (.const name))
    (fun path name => reifyPath path (.var name))
    (fun path body => reifyPath path (.free body))
    true (fun left right => left && right)
    (fun _ _ => true) (fun _ _ => true) (fun _ _ => false)
    rfl (by intro first second; rfl)
    checkTermIsACUIh_reifyPath_const
    checkTermIsACUIh_reifyPath_var
    (by intro path body; exact checkTermIsACUIh_reifyPath_free path body)
    normalForm

/-- Reifying an E-free normal form gives an E-free term. -/
theorem reify_isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom)
    (acuih : isACUIh normalForm = true) :
    (reify normalForm).IsACUIh := by
  rw [← checkTermIsACUIh_eq_true_iff,
    checkTermIsACUIh_reify, acuih]

/-- Reification of the purified form is an E-free raw term. -/
theorem reify_purifyNormalForm_isACUIh
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (target : NormalForm Const Var Hom) :
    (reify (purifyNormalForm left right configuration target)).IsACUIh :=
  reify_isACUIh _ (purifyNormalForm_isACUIh left right configuration target)

/-- Substitution preserves the ACUIh fragment when all substituted values
are themselves E-free. -/
theorem isACUIh_substitute
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    (substitution : SourceVar → Term Const TargetVar Hom)
    (valuesACUIh : ∀ name, (substitution name).IsACUIh)
    {term : Term Const SourceVar Hom} (acuih : term.IsACUIh) :
    (Term.substitute substitution term).IsACUIh := by
  induction term with
  | zero => trivial
  | const name => trivial
  | var name => exact valuesACUIh name
  | add first second firstHypothesis secondHypothesis =>
      exact ⟨firstHypothesis acuih.1, secondHypothesis acuih.2⟩
  | hom name body inductionHypothesis => exact inductionHypothesis acuih
  | free body inductionHypothesis => exact False.elim acuih

/-- Purified form of one whole side. -/
def purifiedSide
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) (side : Bool) :
    NormalForm (ECombinationBasis left right) Var Hom :=
  purifyNormalForm left right configuration (if side then right else left)

/-- Purified body of a selected occurrence. -/
def purifiedOccurrenceBody
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (occurrence : EOccurrence left right) :
    NormalForm (ECombinationBasis left right) Var Hom :=
  purifyNormalForm left right configuration occurrence.body

/-- Fixed row type for all equations and restrictions of a certificate. -/
abbrev ECombinationRow
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :=
  Unit ⊕
    ((EOccurrence left right × Bool) ⊕
      (EOccurrence left right × Var × EOccurrence left right))

/-- Whether an occurrence is a fixed representative. -/
def isRepresentative
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (configuration : EConfiguration left right)
    (occurrence : EOccurrence left right) : Prop :=
  configuration.1 occurrence = some occurrence

/-- An assignment column is forbidden when it names a non-representative, or
when a variable used in a representative body would introduce a dependency
at least as large as the representative's rank. -/
def forbiddenOccurrenceColumn
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (name : Var) (basisOccurrence : EOccurrence left right) : Bool :=
  decide (configuration.1 basisOccurrence ≠ some basisOccurrence) ||
    (FinEnum.toList (EOccurrence left right)).any fun representative =>
      decide
        (configuration.1 representative = some representative ∧
          name ∈ variableSupport
            (purifiedOccurrenceBody left right configuration representative) ∧
          ¬ configuration.2 basisOccurrence < configuration.2 representative)

theorem forbiddenOccurrenceColumn_eq_true_iff
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (name : Var) (basisOccurrence : EOccurrence left right) :
    forbiddenOccurrenceColumn left right configuration name basisOccurrence = true ↔
      configuration.1 basisOccurrence ≠ some basisOccurrence ∨
        ∃ representative : EOccurrence left right,
          configuration.1 representative = some representative ∧
          name ∈ variableSupport
            (purifiedOccurrenceBody left right configuration representative) ∧
          ¬ configuration.2 basisOccurrence <
            configuration.2 representative := by
  simp [forbiddenOccurrenceColumn]

/-- Left term represented by a certificate row. -/
def eCombinationLeftTerm
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) :
    ECombinationRow left right →
      Term (ECombinationBasis left right) Var Hom
  | .inl () =>
      reify (purifiedSide left right configuration false)
  | .inr (.inl (occurrence, false)) =>
      reify (purifiedOccurrenceBody left right configuration occurrence)
  | .inr (.inl (occurrence, true)) =>
      match configuration.1 occurrence with
      | none => .zero
      | some representative =>
          reify (purifiedOccurrenceBody left right configuration representative)
  | .inr (.inr (_, name, basisOccurrence)) =>
      if forbiddenOccurrenceColumn left right configuration name
          basisOccurrence = true then
        .var name
      else
        .zero

/-- Right term represented by a certificate row. -/
def eCombinationRightTerm
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) :
    ECombinationRow left right →
      Term (ECombinationBasis left right) Var Hom
  | .inl () =>
      reify (purifiedSide left right configuration true)
  | .inr (.inl (occurrence, false)) =>
      match configuration.1 occurrence with
      | none => .zero
      | some representative =>
          reify (purifiedOccurrenceBody left right configuration representative)
  | .inr (.inl (occurrence, true)) =>
      reify (purifiedOccurrenceBody left right configuration occurrence)
  | .inr (.inr _) => .zero

/-- Left expression represented by a certificate row. -/
def eCombinationLeftExpression
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (row : ECombinationRow left right) :
    NormalForm (ECombinationBasis left right) Var Hom :=
  normalize (eCombinationLeftTerm left right configuration row)

/-- Right expression represented by a certificate row. -/
def eCombinationRightExpression
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (row : ECombinationRow left right) :
    NormalForm (ECombinationBasis left right) Var Hom :=
  normalize (eCombinationRightTerm left right configuration row)

theorem eCombinationLeftTerm_isACUIh
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (row : ECombinationRow left right) :
    (eCombinationLeftTerm left right configuration row).IsACUIh := by
  rcases row with ⟨⟩ | row
  · exact reify_purifyNormalForm_isACUIh _ _ _ _
  · rcases row with ⟨occurrence, side⟩ | ⟨representative, name, occurrence⟩
    · cases side with
      | false => exact reify_purifyNormalForm_isACUIh _ _ _ _
      | true =>
          simp only [eCombinationLeftTerm]
          split
          · trivial
          · apply reify_purifyNormalForm_isACUIh
    · simp only [eCombinationLeftTerm]
      split <;> trivial

theorem eCombinationRightTerm_isACUIh
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (row : ECombinationRow left right) :
    (eCombinationRightTerm left right configuration row).IsACUIh := by
  rcases row with ⟨⟩ | row
  · exact reify_purifyNormalForm_isACUIh _ _ _ _
  · rcases row with ⟨occurrence, side⟩ | ⟨representative, name, occurrence⟩
    · cases side with
      | false =>
          simp only [eCombinationRightTerm]
          split
          · trivial
          · apply reify_purifyNormalForm_isACUIh
      | true => exact reify_purifyNormalForm_isACUIh _ _ _ _
    · trivial

/-- Direct full-coordinate matrix representation, avoiding irrelevant
subtype coordinates around `Finset.univ`. -/
def fullMatrixRepresentation
    {Row : Type*} {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (expressions : Row → NormalForm Const Var Hom) :
    Matrix Row Var (HomContext Hom) × Matrix Row Const (HomContext Hom) :=
  (fun row name => variableCoefficient (expressions row) name,
    fun row constant => constantCoefficient (expressions row) constant)

/-- Substitution in an E-free term is exactly multiplication by its variable
coefficient row plus its constant row. -/
theorem constantCoefficient_normalize_substitute_acuih
    {Const SourceVar Hom : Type u}
    [Encodable Const] [FinEnum SourceVar] [Encodable SourceVar] [Encodable Hom]
    (substitution : SourceVar → Term Const (Fin 0) Hom)
    (term : Term Const SourceVar Hom) (acuih : term.IsACUIh)
    (constant : Const) :
    constantCoefficient (normalize (Term.substitute substitution term)) constant =
      (∑ name : SourceVar,
          variableCoefficient (normalize term) name *
            constantCoefficient (normalize (substitution name)) constant) +
        constantCoefficient (normalize term) constant := by
  induction term with
  | zero => simp
  | const name =>
      by_cases equality : name = constant <;>
        simp [variableCoefficient, constantCoefficient, constantForm, equality]
  | var name =>
      simp only [Term.substitute_var, normalize_var,
        variableCoefficient, constantCoefficient, variableForm,
        NormalForm.fold_singleton, add_zero]
      rw [Finset.sum_eq_single name]
      · simp only [if_pos]
        change _ = (1 : HomContext Hom) * _
        rw [one_mul]
      · intro selected _ different
        simp [different.symm]
      · simp
  | add first second firstHypothesis secondHypothesis =>
      simp only [Term.substitute_add, normalize_add,
        constantCoefficient_union, variableCoefficient_union]
      rw [firstHypothesis acuih.1, secondHypothesis acuih.2]
      simp only [add_mul, Finset.sum_add_distrib]
      ac_rfl
  | hom name body inductionHypothesis =>
      simp only [Term.substitute_hom, normalize_hom,
        constantCoefficient_prefixHom, variableCoefficient_prefixHom]
      rw [inductionHypothesis acuih]
      simp only [mul_add]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro selected _
      exact (mul_assoc _ _ _).symm
  | free body inductionHypothesis =>
      exact False.elim acuih

/-- The left row term specialized to the matrix column currently being
solved.  Restriction rows constrain exactly one alien column; all ordinary
inequality/equality rows are independent of the selected column. -/
def eCombinationColumnLeftTerm
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (selectedBasis : ECombinationBasis left right) :
    ECombinationRow left right →
      Term (ECombinationBasis left right) Var Hom
  | .inr (.inr (_, name, basisOccurrence)) =>
      if selectedBasis = Sum.inr basisOccurrence ∧
          forbiddenOccurrenceColumn left right configuration name
            basisOccurrence = true then
        .var name
      else
        .zero
  | row => eCombinationLeftTerm left right configuration row

theorem eCombinationColumnLeftTerm_isACUIh
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (selectedBasis : ECombinationBasis left right)
    (row : ECombinationRow left right) :
    (eCombinationColumnLeftTerm left right configuration selectedBasis row).IsACUIh := by
  rcases row with ⟨⟩ | row
  · exact eCombinationLeftTerm_isACUIh left right configuration (.inl ())
  · rcases row with ⟨occurrence, direction⟩ |
        ⟨representative, name, basisOccurrence⟩
    · exact eCombinationLeftTerm_isACUIh left right configuration
        (.inr (.inl (occurrence, direction)))
    · simp only [eCombinationColumnLeftTerm]
      split <;> trivial

/-- The two matrices used while solving one selected basis column. -/
def eCombinationColumnRepresentations
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (selectedBasis : ECombinationBasis left right) :=
  (fullMatrixRepresentation
      (fun row => normalize
        (eCombinationColumnLeftTerm left right configuration selectedBasis row)),
    fullMatrixRepresentation
      (eCombinationRightExpression left right configuration))

/-- Every row holds in the representation specialized to its selected basis
column. -/
def eCombinationMatrixBelow
    {Const Var Hom : Type u}
    [Encodable Const] [FinEnum Var] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom)) : Prop :=
  ∀ row basis,
    evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right configuration basis).1
        values row basis ≤
      evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right configuration basis).2
        values row basis

/-- Fixed occurrence constants in representative bodies must also respect
the guessed strict dependency order. -/
def EConfiguration.valid
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (configuration : EConfiguration left right) : Bool :=
  (FinEnum.toList (EOccurrence left right)).all fun occurrence =>
    match configuration.1 occurrence with
    | none => true
    | some representative =>
        decide (configuration.1 representative = some representative) &&
          (FinEnum.toList (EOccurrence left right)).all fun basisOccurrence =>
            decide
              (Sum.inr basisOccurrence ∈ constantSupport
                  (purifiedOccurrenceBody left right configuration representative) →
                configuration.2 basisOccurrence < configuration.2 representative)

/-- Solve the complete ACUIh constraint system for one valid certificate. -/
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

/-- Decode one abstract ACUIh variable value from a matrix. -/
def decodeAbstractEValue
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (name : Var) :
    NormalForm (ECombinationBasis left right) (Fin 0) Hom :=
  decodeGroundMatrix values name

@[simp]
theorem constantCoefficient_decodeAbstractEValue
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (name : Var) (basis : ECombinationBasis left right) :
    constantCoefficient (decodeAbstractEValue left right values name) basis =
      values name basis := by
  exact constantCoefficient_decodeGroundMatrix values name basis

@[simp]
theorem constantCoefficient_normalize_reify_decodeAbstractEValue
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (name : Var) (basis : ECombinationBasis left right) :
    constantCoefficient
        (normalize (reify (decodeAbstractEValue left right values name))) basis =
      values name basis := by
  change constantCoefficient
      (canonicalize (decodeAbstractEValue left right values name)) basis = _
  rw [constantCoefficient_canonicalize,
    constantCoefficient_decodeAbstractEValue]

/-- Matrix evaluation agrees with actual substitution into an E-free term. -/
theorem evaluate_fullMatrixRepresentation_normalize
    {Basis SourceVar Hom : Type u}
    [FinEnum Basis] [Encodable Basis]
    [FinEnum SourceVar] [Encodable SourceVar]
    [FinEnum Hom] [Encodable Hom]
    (term : Term Basis SourceVar Hom) (acuih : term.IsACUIh)
    (values : Matrix SourceVar Basis (HomContext Hom)) (basis : Basis) :
    evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun _ : Unit => normalize term))
        values () basis =
      constantCoefficient
        (normalize
          (Term.substitute
            (fun name => reify (decodeGroundMatrix values name)) term)) basis := by
  rw [constantCoefficient_normalize_substitute_acuih _ term acuih basis]
  change
    (∑ name : SourceVar,
        variableCoefficient (normalize term) name * values name basis) +
        constantCoefficient (normalize term) basis =
      (∑ name : SourceVar,
        variableCoefficient (normalize term) name *
          constantCoefficient
            (normalize (reify (decodeGroundMatrix values name))) basis) +
        constantCoefficient (normalize term) basis
  congr 1
  apply Finset.sum_congr rfl
  intro name _
  rw [show normalize (reify (decodeGroundMatrix values name)) =
      canonicalize (decodeGroundMatrix values name) by rfl,
    constantCoefficient_canonicalize,
    constantCoefficient_decodeGroundMatrix]

/-- Row-indexed version of the matrix/substitution agreement theorem. -/
theorem evaluate_fullMatrixRepresentation_normalize_apply
    {Row Basis SourceVar Hom : Type u}
    [FinEnum Basis] [Encodable Basis]
    [FinEnum SourceVar] [Encodable SourceVar]
    [FinEnum Hom] [Encodable Hom]
    (terms : Row → Term Basis SourceVar Hom)
    (acuih : ∀ row, (terms row).IsACUIh)
    (values : Matrix SourceVar Basis (HomContext Hom))
    (row : Row) (basis : Basis) :
    evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun row => normalize (terms row)))
        values row basis =
      constantCoefficient
        (normalize
          (Term.substitute
            (fun name => reify (decodeGroundMatrix values name))
            (terms row))) basis := by
  change
    evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun _ : Unit => normalize (terms row)))
        values () basis = _
  exact evaluate_fullMatrixRepresentation_normalize
    (terms row) (acuih row) values basis

/-- Actual abstract substitution represented by a matrix row. -/
def applyAbstractMatrixAssignment
    {Basis SourceVar Hom : Type u}
    [FinEnum Basis] [Encodable Basis]
    [FinEnum SourceVar] [Encodable SourceVar]
    [FinEnum Hom] [Encodable Hom]
    (values : Matrix SourceVar Basis (HomContext Hom))
    (term : Term Basis SourceVar Hom) : NormalForm Basis (Fin 0) Hom :=
  normalize
    (Term.substitute
      (fun name => reify (decodeGroundMatrix values name)) term)

/-- Coefficient-wise matrix inclusion is a genuine solved ACUIh inequality
after applying the decoded abstract assignment. -/
theorem fullMatrixRepresentation_below_gives_solved
    {Row Basis SourceVar Hom : Type u}
    [FinEnum Row]
    [FinEnum Basis] [Encodable Basis]
    [FinEnum SourceVar] [Encodable SourceVar]
    [FinEnum Hom] [Encodable Hom]
    (leftTerms rightTerms : Row → Term Basis SourceVar Hom)
    (leftACUIh : ∀ row, (leftTerms row).IsACUIh)
    (rightACUIh : ∀ row, (rightTerms row).IsACUIh)
    (values : Matrix SourceVar Basis (HomContext Hom))
    (below : matrixRepresentationBelow
      (fullMatrixRepresentation (fun row => normalize (leftTerms row)))
      (fullMatrixRepresentation (fun row => normalize (rightTerms row)))
      values) (row : Row) :
    IsSolvedInequality
      (applyAbstractMatrixAssignment values (leftTerms row))
      (applyAbstractMatrixAssignment values (rightTerms row)) := by
  let leftValue := applyAbstractMatrixAssignment values (leftTerms row)
  let rightValue := applyAbstractMatrixAssignment values (rightTerms row)
  have decodedACUIh : ∀ name,
      (reify (decodeGroundMatrix values name)).IsACUIh := by
    intro name
    apply reify_isACUIh
    exact isACUIh_decodeGroundMatrix values name
  have leftValueACUIh : isACUIh leftValue = true := by
    apply isACUIh_normalize
    exact isACUIh_substitute _ decodedACUIh (leftACUIh row)
  have rightValueACUIh : isACUIh rightValue = true := by
    apply isACUIh_normalize
    exact isACUIh_substitute _ decodedACUIh (rightACUIh row)
  apply (isSolvedInequality_iff_constantCoefficient_le
    leftValue rightValue Finset.univ leftValueACUIh (by simp)).mpr
  refine ⟨isGround_of_isACUIh_fin_zero leftValue leftValueACUIh,
    isGround_of_isACUIh_fin_zero rightValue rightValueACUIh, ?_⟩
  intro basis
  dsimp only [leftValue, rightValue, applyAbstractMatrixAssignment]
  rw [← evaluate_fullMatrixRepresentation_normalize_apply
      leftTerms leftACUIh values row basis.1,
    ← evaluate_fullMatrixRepresentation_normalize_apply
      rightTerms rightACUIh values row basis.1]
  exact below row basis.1

/-- Whether a row is an inequality/body row rather than a column-local zero
restriction. -/
def isMainECombinationRow
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : NormalForm Const Var Hom} :
    ECombinationRow left right → Prop
  | .inr (.inr _) => False
  | _ => True

/-- Every inequality/body row has its intended ordinary ACUIh semantics
under a solution of all column-specialized representations. -/
theorem eCombination_matrix_solution_solved_row
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (below : eCombinationMatrixBelow left right configuration values)
    (row : ECombinationRow left right)
    (mainRow : isMainECombinationRow row) :
    IsSolvedInequality
      (applyAbstractMatrixAssignment values
        (eCombinationLeftTerm left right configuration row))
      (applyAbstractMatrixAssignment values
        (eCombinationRightTerm left right configuration row)) := by
  let leftValue := applyAbstractMatrixAssignment values
    (eCombinationLeftTerm left right configuration row)
  let rightValue := applyAbstractMatrixAssignment values
    (eCombinationRightTerm left right configuration row)
  have decodedACUIh : ∀ name,
      (reify (decodeGroundMatrix values name)).IsACUIh := by
    intro name
    apply reify_isACUIh
    exact isACUIh_decodeGroundMatrix values name
  have leftValueACUIh : isACUIh leftValue = true := by
    apply isACUIh_normalize
    exact isACUIh_substitute _ decodedACUIh
      (eCombinationLeftTerm_isACUIh left right configuration row)
  have rightValueACUIh : isACUIh rightValue = true := by
    apply isACUIh_normalize
    exact isACUIh_substitute _ decodedACUIh
      (eCombinationRightTerm_isACUIh left right configuration row)
  apply (isSolvedInequality_iff_constantCoefficient_le
    leftValue rightValue Finset.univ leftValueACUIh (by simp)).mpr
  refine ⟨isGround_of_isACUIh_fin_zero leftValue leftValueACUIh,
    isGround_of_isACUIh_fin_zero rightValue rightValueACUIh, ?_⟩
  intro basis
  have selected := below row basis.1
  have rowEquality : eCombinationColumnLeftTerm left right configuration
      basis.1 row = eCombinationLeftTerm left right configuration row := by
    rcases row with ⟨⟩ | row
    · rfl
    · rcases row with ⟨occurrence, direction⟩ |
          ⟨representative, name, basisOccurrence⟩
      · rfl
      · exact False.elim mainRow
  change evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationColumnLeftTerm left right configuration basis.1 row)))
      values row basis.1 ≤
    evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationRightTerm left right configuration row)))
      values row basis.1 at selected
  dsimp only [leftValue, rightValue, applyAbstractMatrixAssignment]
  have leftAgreement := evaluate_fullMatrixRepresentation_normalize_apply
    (fun row => eCombinationColumnLeftTerm left right configuration basis.1 row)
    (eCombinationColumnLeftTerm_isACUIh left right configuration basis.1)
    values row basis.1
  have rightAgreement := evaluate_fullMatrixRepresentation_normalize_apply
    (fun row => eCombinationRightTerm left right configuration row)
    (eCombinationRightTerm_isACUIh left right configuration)
    values row basis.1
  rw [leftAgreement, rightAgreement] at selected
  rw [rowEquality] at selected
  exact selected

/-- Interpret one representative by well-founded recursion on the strict rank
stored in the certificate.  A non-smaller occurrence is interpreted as zero;
validity and the zero rows prove that such a branch is unreachable in every
body that matters. -/
def resolveERepresentative
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (representative : EOccurrence left right) : Term Const (Fin 0) Hom :=
  .free
    (replaceBasisConstants
      (fun basis =>
        match basis with
        | .inl constant => .const constant
        | .inr dependency =>
            if _smaller : configuration.2 dependency <
                configuration.2 representative then
              resolveERepresentative left right configuration values dependency
            else
              .zero)
      (reify
        (normalize
          (Term.substitute
            (fun name => reify (decodeAbstractEValue left right values name))
            (reify
              (purifiedOccurrenceBody left right configuration
                representative))))))
termination_by (configuration.2 representative).1
decreasing_by exact _smaller

/-- Interpret an abstract basis atom using the certificate's well-founded
representative definitions. -/
def resolveECombinationBasis
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom)) :
    ECombinationBasis left right → Term Const (Fin 0) Hom
  | .inl name => .const name
  | .inr representative =>
      resolveERepresentative left right configuration values representative

/-- The ground substitution reconstructed from a certificate matrix. -/
def decodeECombinationAssignment
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom)) :
    Var → NormalForm Const (Fin 0) Hom :=
  fun name =>
    normalize
      (replaceBasisConstants
        (resolveECombinationBasis left right configuration values)
        (reify (decodeAbstractEValue left right values name)))

/-- Apply a decoded ground-normal-form assignment. -/
def applyGroundAssignment
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) : NormalForm Const (Fin 0) Hom :=
  substituteNormalForm (fun name => reify (assignment name)) target

/-- Executable exact check of the public solved-inequality specification. -/
def checkGroundInequality
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) : Bool :=
  left.isGround && right.isGround && decide (left + right = right)

theorem checkGroundInequality_eq_true_iff
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    checkGroundInequality left right = true ↔
      IsSolvedInequality left right := by
  constructor
  · intro checked
    have parts := Bool.and_eq_true_iff.mp checked
    have groundParts := Bool.and_eq_true_iff.mp parts.1
    refine ⟨groundParts.1, groundParts.2, ?_⟩
    change left + right = right
    exact of_decide_eq_true parts.2
  · rintro ⟨leftGround, rightGround, below⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨leftGround, rightGround⟩, ?_⟩
    change left + right = right at below
    exact decide_eq_true below

/-- A configuration contributes a candidate only after exact ACUIhE
validation of the reconstructed assignment. -/
def solveEConfigurationChecked?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) :
    Option (Var → NormalForm Const (Fin 0) Hom) := do
  let values ← solveEConfiguration? left right configuration
  let assignment := decodeECombinationAssignment left right configuration values
  if checkGroundInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right) then
    some assignment
  else
    none

/-- First successful result of a finite backtracking list. -/
def firstSome? {Alpha Beta : Type*} (attempt : Alpha → Option Beta) :
    List Alpha → Option Beta
  | [] => none
  | value :: rest =>
      match attempt value with
      | some result => some result
      | none => firstSome? attempt rest

theorem firstSome?_sound
    {Alpha Beta : Type*} (attempt : Alpha → Option Beta)
    (candidates : List Alpha) {result : Beta}
    (found : firstSome? attempt candidates = some result) :
    ∃ candidate ∈ candidates, attempt candidate = some result := by
  induction candidates with
  | nil => simp [firstSome?] at found
  | cons candidate candidates inductionHypothesis =>
      simp only [firstSome?] at found
      cases attemptResult : attempt candidate with
      | none =>
          rw [attemptResult] at found
          rcases inductionHypothesis found with ⟨witness, membership, result⟩
          exact ⟨witness, by simp [membership], result⟩
      | some value =>
          rw [attemptResult] at found
          cases found
          exact ⟨candidate, by simp, attemptResult⟩

theorem firstSome?_complete
    {Alpha Beta : Type*} (attempt : Alpha → Option Beta)
    (candidates : List Alpha) {candidate : Alpha} {result : Beta}
    (membership : candidate ∈ candidates)
    (found : attempt candidate = some result) :
    ∃ returned, firstSome? attempt candidates = some returned := by
  induction candidates with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at membership
      rcases membership with equality | membership
      · subst head
        simp [firstSome?, found]
      · cases headResult : attempt head with
        | none =>
            simpa [firstSome?, headResult] using
              inductionHypothesis membership
        | some value => exact ⟨value, by simp [firstSome?, headResult]⟩

/-- Total finite search for a ground solution of one ACUIhE inequality. -/
def solveACUIhE?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Option (Var → NormalForm Const (Fin 0) Hom) :=
  firstSome? (solveEConfigurationChecked? left right)
    (FinEnum.toList (EConfiguration left right))

/-- Every returned assignment is a genuine ground ACUIhE solution. -/
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

/-!
## Projection of arbitrary solutions

The following definitions implement the small-solution projection used by
the completeness proof.  Unanchored `E` atoms in a ground assignment are
discarded; an atom equal to the value of an input occurrence is renamed to
the first such occurrence.  Ranks count strictly smaller representative-body
measures, so a genuine nested dependency always has a smaller rank.
-/

/-- The ground value of one input occurrence body under an assignment. -/
def occurrenceBodyValue
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right) : NormalForm Const (Fin 0) Hom :=
  applyGroundAssignment assignment occurrence.body

/-- First input occurrence whose evaluated body is the selected ground body. -/
def representativeForBody?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (body : NormalForm Const (Fin 0) Hom) :
    Option (EOccurrence left right) :=
  (FinEnum.toList (EOccurrence left right)).find? fun occurrence =>
    occurrenceBodyValue left right assignment occurrence = body

/-- Equality/zero class induced by an arbitrary ground assignment. -/
def projectedOccurrenceClass
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right) : Option (EOccurrence left right) :=
  let body := occurrenceBodyValue left right assignment occurrence
  if body = ∅ then none
  else representativeForBody? left right assignment body

/-- Rank induced by strict raw measures of evaluated occurrence bodies. -/
def projectedOccurrenceRank
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right) :
    Fin (FinEnum.card (EOccurrence left right) + 1) :=
  let occurrences := FinEnum.toList (EOccurrence left right)
  let smaller := occurrences.filter fun candidate =>
    rawNormalFormMeasure
        (occurrenceBodyValue left right assignment candidate).raw <
      rawNormalFormMeasure
        (occurrenceBodyValue left right assignment occurrence).raw
  ⟨smaller.length, by
    apply Nat.lt_succ_of_le
    apply le_trans (List.length_filter_le _ _)
    simp [occurrences, FinEnum.toList]⟩

/-- The finite configuration canonically projected from a ground assignment. -/
def projectedEConfiguration
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom) :
    EConfiguration left right :=
  (projectedOccurrenceClass left right assignment,
    projectedOccurrenceRank left right assignment)

/-- Rebuild a ground form while simultaneously replacing each `E` atom that
is anchored by an input occurrence with its representative constant. -/
def projectGroundNormalFormPair
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const (Fin 0) Hom) :
    NormalForm Const (Fin 0) Hom ×
      NormalForm (ECombinationBasis left right) (Fin 0) Hom :=
  projectEBlocksPair (representativeForBody? left right assignment) target

/-- Shallow alien-term projection of a ground normal form. -/
def projectGroundNormalForm
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const (Fin 0) Hom) :
    NormalForm (ECombinationBasis left right) (Fin 0) Hom :=
  (projectGroundNormalFormPair left right assignment target).2

/-- Project every value of an arbitrary assignment to the finite alien basis. -/
def projectedAssignment
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom) :
    Var → NormalForm (ECombinationBasis left right) (Fin 0) Hom :=
  fun name =>
    projectGroundNormalForm left right assignment (canonicalize (assignment name))

/-- Matrix of the projected finite-basis assignment. -/
def projectedAssignmentMatrix
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom) :
    Matrix Var (ECombinationBasis left right) (HomContext Hom) :=
  fun name basis =>
    constantCoefficient (projectedAssignment left right assignment name) basis

/-- A productive combination configuration has an ACUIh matrix solution and
its rank/equality restrictions make every such solution reconstruct to a
valid solution of the original ACUIhE inequality. -/
def ProductiveEConfiguration
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) : Prop :=
  configuration.valid = true ∧
    (∃ values : Matrix Var (ECombinationBasis left right) (HomContext Hom),
      eCombinationMatrixBelow left right configuration values) ∧
    ∀ values : Matrix Var (ECombinationBasis left right) (HomContext Hom),
      eCombinationMatrixBelow left right configuration values →
        checkGroundInequality
          (applyGroundAssignment
            (decodeECombinationAssignment left right configuration values) left)
          (applyGroundAssignment
            (decodeECombinationAssignment left right configuration values) right) =
          true

/-- Completeness of finite backtracking once the theory-combination
certificate is supplied.  No arbitrary search cutoff occurs in this
statement. -/
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
      solveEConfigurationChecked? left right configuration = some assignment := by
    simp [solveEConfigurationChecked?, valuesFound, assignment, checked]
  apply firstSome?_complete
    (solveEConfigurationChecked? left right)
    (FinEnum.toList (EConfiguration left right))
    (candidate := configuration) (result := assignment)
  · exact FinEnum.mem_toList configuration
  · exact configurationFound

end ACUIHE.Solver.Search
