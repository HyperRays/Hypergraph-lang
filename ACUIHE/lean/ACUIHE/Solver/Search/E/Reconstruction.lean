import ACUIHE.Solver.Search.E.Projection

/-!
The reverse half of ACUIhE completeness.

For a valid finite certificate and an ACUIh matrix solution, representatives
are expanded by well-founded recursion on their certificate rank.
`ReconstructionProofScan` then traverses the intrinsic normal form once and
proves that expanding its purified image recovers the original semantics.
This yields a genuine solution of the unpurified inequality and completes the
soundness/completeness equivalence for search failure.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver
open ACUIHE.Solver.Linear
open ACUIHE.Solver.NormalForm.Internal

universe u v w x

local instance reconstructionEncodableDecidableEq
    {Alpha : Type*} [Encodable Alpha] : DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

local instance (priority := 2000) reconstructionBasisFintype
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Fintype (ECombinationBasis left right) :=
  FinEnum.instFintype

local instance reconstructionNormalUnionCommutative
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Commutative
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun left right => by
    apply NormalForm.ext_raw
    exact rawUnion_comm left.raw right.raw⟩

local instance reconstructionNormalUnionAssociative
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Associative
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun left middle right => by
    apply NormalForm.ext_raw
    exact rawUnion_assoc left.raw middle.raw right.raw⟩

local instance reconstructionNormalUnionIdempotent
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.IdempotentOp
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun value => by
    apply NormalForm.ext_raw
    exact rawUnion_self value.raw⟩

local instance reconstructionPairCommutative
    {Const₁ Var₁ Const₂ Var₂ Hom : Type*}
    [Encodable Const₁] [Encodable Var₁]
    [Encodable Const₂] [Encodable Var₂] [Encodable Hom] :
    Std.Commutative (fun first second :
        NormalForm Const₁ Var₁ Hom × NormalForm Const₂ Var₂ Hom =>
      (first.1 ∪ second.1, first.2 ∪ second.2)) :=
  ⟨by intro first second; apply Prod.ext <;>
    apply reconstructionNormalUnionCommutative.comm⟩

local instance reconstructionPairAssociative
    {Const₁ Var₁ Const₂ Var₂ Hom : Type*}
    [Encodable Const₁] [Encodable Var₁]
    [Encodable Const₂] [Encodable Var₂] [Encodable Hom] :
    Std.Associative (fun first second :
        NormalForm Const₁ Var₁ Hom × NormalForm Const₂ Var₂ Hom =>
      (first.1 ∪ second.1, first.2 ∪ second.2)) :=
  ⟨by intro first middle last; apply Prod.ext <;>
    apply reconstructionNormalUnionAssociative.assoc⟩

local instance reconstructionPairIdempotent
    {Const₁ Var₁ Const₂ Var₂ Hom : Type*}
    [Encodable Const₁] [Encodable Var₁]
    [Encodable Const₂] [Encodable Var₂] [Encodable Hom] :
    Std.IdempotentOp (fun first second :
        NormalForm Const₁ Var₁ Hom × NormalForm Const₂ Var₂ Hom =>
      (first.1 ∪ second.1, first.2 ∪ second.2)) :=
  ⟨by intro value; apply Prod.ext <;>
    apply reconstructionNormalUnionIdempotent.idempotent⟩

/-- A dependency row really zeros exactly its selected forbidden matrix
coefficient. -/
theorem eCombinationMatrixBelow_forbidden_zero
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (below : eCombinationMatrixBelow left right configuration values)
    (name : Var) (basisOccurrence : EOccurrence left right)
    (forbidden : forbiddenOccurrenceColumn left right configuration name
      basisOccurrence = true) :
    values name (Sum.inr basisOccurrence) = 0 := by
  have selected := below
    (.inr (.inr (basisOccurrence, name, basisOccurrence)))
    (Sum.inr basisOccurrence)
  change evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationColumnLeftTerm left right configuration
          (Sum.inr basisOccurrence) row))) values
      (.inr (.inr (basisOccurrence, name, basisOccurrence)))
      (Sum.inr basisOccurrence) ≤
    evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationRightTerm left right configuration row))) values
      (.inr (.inr (basisOccurrence, name, basisOccurrence)))
      (Sum.inr basisOccurrence) at selected
  have simplified : ({[]} : HomContext Hom) *
      values name (Sum.inr basisOccurrence) = 0 := by
    simpa [evaluateMatrixRepresentation_apply, fullMatrixRepresentation,
      eCombinationColumnLeftTerm, forbidden, eCombinationRightTerm,
      variableCoefficient, constantCoefficient, variableForm] using selected
  change (1 : HomContext Hom) *
      values name (Sum.inr basisOccurrence) = 0 at simplified
  simpa using simplified

/-- Validity makes every chosen class representative a fixed point. -/
theorem EConfiguration.valid_representative
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (configuration : EConfiguration left right)
    (valid : configuration.valid = true)
    {occurrence representative : EOccurrence left right}
    (classResult : configuration.1 occurrence = some representative) :
    configuration.1 representative = some representative := by
  have selected := (List.all_eq_true.mp valid) occurrence
    (FinEnum.mem_toList occurrence)
  rw [classResult] at selected
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp selected).1

/-- Every alien constant occurring in a valid representative body has a
strictly smaller rank. -/
theorem EConfiguration.valid_constant_rank
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (configuration : EConfiguration left right)
    (valid : configuration.valid = true)
    (representative dependency : EOccurrence left right)
    (fixed : configuration.1 representative = some representative)
    (membership : Sum.inr dependency ∈ constantSupport
      (purifiedOccurrenceBody left right configuration representative)) :
    configuration.2 dependency < configuration.2 representative := by
  have selected := (List.all_eq_true.mp valid) representative
    (FinEnum.mem_toList representative)
  rw [fixed] at selected
  have ranks := (List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp selected).2) dependency
      (FinEnum.mem_toList dependency)
  exact (of_decide_eq_true ranks) membership

/-- Non-representative alien columns vanish in every certified matrix. -/
theorem eCombinationMatrixBelow_nonrepresentative_zero
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (below : eCombinationMatrixBelow left right configuration values)
    (name : Var) (occurrence : EOccurrence left right)
    (notFixed : configuration.1 occurrence ≠ some occurrence) :
    values name (Sum.inr occurrence) = 0 := by
  apply eCombinationMatrixBelow_forbidden_zero
    left right configuration values below
  apply (forbiddenOccurrenceColumn_eq_true_iff
    left right configuration name occurrence).mpr
  exact Or.inl notFixed

/-- A variable used in a representative body has no alien coefficient whose
rank is not smaller than that representative. -/
theorem eCombinationMatrixBelow_nonsmaller_zero
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (below : eCombinationMatrixBelow left right configuration values)
    (representative dependency : EOccurrence left right) (name : Var)
    (fixed : configuration.1 representative = some representative)
    (variableMembership : name ∈ variableSupport
      (purifiedOccurrenceBody left right configuration representative))
    (notSmaller : ¬ configuration.2 dependency <
      configuration.2 representative) :
    values name (Sum.inr dependency) = 0 := by
  apply eCombinationMatrixBelow_forbidden_zero
    left right configuration values below
  apply (forbiddenOccurrenceColumn_eq_true_iff
    left right configuration name dependency).mpr
  exact Or.inr
    ⟨representative, fixed, variableMembership, notSmaller⟩

/-- The two body rows make every occurrence body exactly equal to its chosen
representative body (or to zero) under the abstract matrix assignment. -/
theorem eCombination_abstract_body_class
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (below : eCombinationMatrixBelow left right configuration values)
    (occurrence : EOccurrence left right) :
    applyAbstractMatrixAssignment values
        (reify
          (purifiedOccurrenceBody left right configuration occurrence)) =
      match configuration.1 occurrence with
      | none => ∅
      | some representative =>
          applyAbstractMatrixAssignment values
            (reify
              (purifiedOccurrenceBody left right configuration representative)) := by
  have forward := eCombination_matrix_solution_solved_row
    left right configuration values below
      (.inr (.inl (occurrence, false))) True.intro
  have reverse := eCombination_matrix_solution_solved_row
    left right configuration values below
      (.inr (.inl (occurrence, true))) True.intro
  cases classResult : configuration.1 occurrence with
  | none =>
      simp only [eCombinationLeftTerm, eCombinationRightTerm,
        classResult] at forward reverse ⊢
      have forwardBelow := forward.2.2
      change applyAbstractMatrixAssignment values
          (reify
            (purifiedOccurrenceBody left right configuration occurrence)) +
            ∅ = ∅ at forwardBelow
      calc
        applyAbstractMatrixAssignment values
            (reify
              (purifiedOccurrenceBody left right configuration occurrence)) =
              applyAbstractMatrixAssignment values
                (reify
                  (purifiedOccurrenceBody left right configuration occurrence)) +
              (0 : NormalForm (ECombinationBasis left right) (Fin 0) Hom) :=
          by
            apply NormalForm.ext_raw
            exact (rawUnion_empty _).symm
        _ = ∅ := forwardBelow
  | some representative =>
      simp only [eCombinationLeftTerm, eCombinationRightTerm,
        classResult] at forward reverse ⊢
      have forwardBelow := forward.2.2
      have reverseBelow := reverse.2.2
      calc
        applyAbstractMatrixAssignment values
            (reify
              (purifiedOccurrenceBody left right configuration occurrence)) =
            applyAbstractMatrixAssignment values
                (reify
                  (purifiedOccurrenceBody left right configuration representative)) +
              applyAbstractMatrixAssignment values
                (reify
                  (purifiedOccurrenceBody left right configuration occurrence)) :=
          reverseBelow.symm
        _ = applyAbstractMatrixAssignment values
                (reify
                  (purifiedOccurrenceBody left right configuration occurrence)) +
              applyAbstractMatrixAssignment values
                (reify
                  (purifiedOccurrenceBody left right configuration representative)) := by
          apply NormalForm.ext_raw
          exact rawUnion_comm _ _
        _ = applyAbstractMatrixAssignment values
              (reify
                (purifiedOccurrenceBody left right configuration representative)) :=
          forwardBelow

/-- A nonzero variable coefficient witnesses membership in variable support. -/
theorem mem_variableSupport_of_variableCoefficient_ne_zero
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) (name : Var)
    (nonzero : variableCoefficient target name ≠ 0) :
    name ∈ variableSupport target := by
  have pathsNonempty : (variableCoefficient target name).paths ≠ ∅ := by
    intro pathsEmpty
    apply nonzero
    apply HomContext.ext
    simpa using pathsEmpty
  rcases Finset.nonempty_iff_ne_empty.mpr pathsNonempty with
    ⟨path, pathMembership⟩
  exact (mem_variableSupport target name).mpr
    ⟨path, (mem_variableCoefficient target name path).mp pathMembership⟩

/-- A nonzero constant coefficient witnesses membership in constant support. -/
theorem mem_constantSupport_of_constantCoefficient_ne_zero
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) (name : Const)
    (nonzero : constantCoefficient target name ≠ 0) :
    name ∈ constantSupport target := by
  have pathsNonempty : (constantCoefficient target name).paths ≠ ∅ := by
    intro pathsEmpty
    apply nonzero
    apply HomContext.ext
    simpa using pathsEmpty
  rcases Finset.nonempty_iff_ne_empty.mpr pathsNonempty with
    ⟨path, pathMembership⟩
  exact (mem_constantSupport target name).mpr
    ⟨path, (mem_constantCoefficient target name path).mp pathMembership⟩

private theorem variableCoefficient_normalize_reifyPath_constant
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Const) (selected : Var) :
    variableCoefficient
        (normalize (reifyPath path (.const name : Term Const Var Hom))) selected =
      0 := by
  induction path with
  | nil => simp [reifyPath, variableCoefficient, constantForm]
  | cons hom path inductionHypothesis =>
      change variableCoefficient
          (normalize (.hom hom (reifyPath path (.const name)))) selected = 0
      rw [normalize_hom, variableCoefficient_prefixHom,
        inductionHypothesis, mul_zero]

private theorem variableCoefficient_normalize_reifyPath_variable
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name selected : Var) :
    variableCoefficient
        (normalize (reifyPath path (.var name : Term Const Var Hom))) selected =
      if name = selected then {path} else 0 := by
  induction path with
  | nil => simp [reifyPath, variableCoefficient, variableForm]
  | cons hom path inductionHypothesis =>
      change variableCoefficient
          (normalize (.hom hom (reifyPath path (.var name)))) selected = _
      rw [normalize_hom, variableCoefficient_prefixHom, inductionHypothesis]
      by_cases equality : name = selected
      · subst name
        simp only [if_pos]
        apply HomContext.ext
        change Finset.image₂ (fun leftPath rightPath => leftPath ++ rightPath)
            ({[hom]} : Finset (List Hom)) ({path} : Finset (List Hom)) =
          ({hom :: path} : Finset (List Hom))
        simp
      · simp [equality]

private theorem variableCoefficient_normalize_reifyPath_free
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (body : Term Const Var Hom) (selected : Var) :
    variableCoefficient
        (normalize (reifyPath path (.free body : Term Const Var Hom))) selected =
      0 := by
  induction path with
  | nil =>
      by_cases bodyZero : normalize body = ∅
      · rw [show normalize (reifyPath [] (.free body)) =
            wrapE (normalize body) by rfl,
          bodyZero, wrapE_empty, variableCoefficient_empty]
      · rw [show normalize (reifyPath [] (.free body)) =
            wrapE (normalize body) by rfl,
          wrapE_of_ne_empty bodyZero]
        simp [variableCoefficient]
  | cons hom path inductionHypothesis =>
      change variableCoefficient
          (normalize (.hom hom (reifyPath path (.free body)))) selected = 0
      rw [normalize_hom, variableCoefficient_prefixHom,
        inductionHypothesis, mul_zero]

/-- Canonicalization can recursively alter `E` bodies, but never changes an
outer variable coefficient. -/
@[simp]
theorem variableCoefficient_canonicalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) (selected : Var) :
    variableCoefficient (canonicalize normalForm) selected =
      variableCoefficient normalForm selected := by
  unfold canonicalize reify
  exact NormalForm.fold_hom
    (fun term : Term Const Var Hom =>
      variableCoefficient (normalize term) selected)
    (.zero : Term Const Var Hom) (.add)
    (fun path name => reifyPath path (.const name))
    (fun path name => reifyPath path (.var name))
    (fun path body => reifyPath path (.free body))
    (0 : HomContext Hom) (· + ·)
    (fun _ _ => 0)
    (fun path name => if name = selected then {path} else 0)
    (fun _ _ => 0)
    (by simp [variableCoefficient])
    (by intro first second; simp [variableCoefficient_union])
    (fun path name =>
      variableCoefficient_normalize_reifyPath_constant path name selected)
    (fun path name =>
      variableCoefficient_normalize_reifyPath_variable path name selected)
    (fun path body =>
      variableCoefficient_normalize_reifyPath_free path body selected)
    normalForm

/-- The solved abstract body of a fixed representative contains no alien
constant at a non-smaller rank. -/
theorem abstract_representative_body_nonsmaller_coefficient_zero
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (representative dependency : EOccurrence left right)
    (fixed : configuration.1 representative = some representative)
    (notSmaller : ¬ configuration.2 dependency <
      configuration.2 representative) :
    constantCoefficient
        (applyAbstractMatrixAssignment values
          (reify
            (purifiedOccurrenceBody left right configuration representative)))
        (Sum.inr dependency) = 0 := by
  unfold applyAbstractMatrixAssignment
  rw [constantCoefficient_normalize_substitute_acuih
    (fun name => reify (decodeGroundMatrix values name))
    (reify
      (purifiedOccurrenceBody left right configuration representative))
    (reify_purifyNormalForm_isACUIh left right configuration
      representative.body)
    (Sum.inr dependency)]
  have decodedCoefficient : ∀ name : Var,
      constantCoefficient
          (normalize (reify (decodeGroundMatrix values name)))
          (Sum.inr dependency) =
        values name (Sum.inr dependency) := by
    intro name
    change constantCoefficient
        (canonicalize (decodeGroundMatrix values name))
        (Sum.inr dependency) = _
    rw [constantCoefficient_canonicalize,
      constantCoefficient_decodeGroundMatrix]
  simp_rw [decodedCoefficient]
  have variableProductsZero : ∀ name : Var,
      variableCoefficient
          (purifiedOccurrenceBody left right configuration representative) name *
        values name (Sum.inr dependency) = 0 := by
    intro name
    by_cases coefficientZero : variableCoefficient
        (purifiedOccurrenceBody left right configuration representative) name = 0
    · rw [coefficientZero, zero_mul]
    · have variableMembership :=
        mem_variableSupport_of_variableCoefficient_ne_zero
          (purifiedOccurrenceBody left right configuration representative)
          name coefficientZero
      rw [eCombinationMatrixBelow_nonsmaller_zero
        left right configuration values below representative dependency name
        fixed variableMembership notSmaller, mul_zero]
  have constantZero : constantCoefficient
      (purifiedOccurrenceBody left right configuration representative)
      (Sum.inr dependency) = 0 := by
    by_contra coefficientNonzero
    have membership := mem_constantSupport_of_constantCoefficient_ne_zero
      (purifiedOccurrenceBody left right configuration representative)
      (Sum.inr dependency) coefficientNonzero
    exact notSmaller (EConfiguration.valid_constant_rank
      configuration valid representative dependency fixed membership)
  change
    (∑ name : Var,
      variableCoefficient
          (canonicalize
            (purifiedOccurrenceBody left right configuration representative)) name *
        values name (Sum.inr dependency)) +
      constantCoefficient
        (canonicalize
          (purifiedOccurrenceBody left right configuration representative))
        (Sum.inr dependency) = 0
  simp only [variableCoefficient_canonicalize,
    constantCoefficient_canonicalize]
  rw [Finset.sum_eq_zero (fun name _ => variableProductsZero name),
    constantZero, add_zero]

/-- Replacing constants in an E-free term only depends on replacement values
for constants actually in its normalized support. -/
theorem replaceBasisConstants_congr_acuih
    {Basis : Type u} {Const : Type v} {Hom : Type w}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (first second : Basis → Term Const (Fin 0) Hom)
    (term : Term Basis (Fin 0) Hom) (acuih : term.IsACUIh)
    (agree : ∀ basis ∈ constantSupport (normalize term),
      first basis = second basis) :
    replaceBasisConstants first term = replaceBasisConstants second term := by
  induction term with
  | zero => rfl
  | const basis =>
      simp only [replaceBasisConstants]
      apply agree basis
      simp [constantSupport, constantForm]
  | var name => rfl
  | add leftTerm rightTerm leftHypothesis rightHypothesis =>
      simp only [replaceBasisConstants]
      congr 1
      · apply leftHypothesis acuih.1
        intro basis membership
        apply agree basis
        simpa [constantSupport_union] using
          Finset.mem_union_left
            (constantSupport (normalize rightTerm)) membership
      · apply rightHypothesis acuih.2
        intro basis membership
        apply agree basis
        simpa [constantSupport_union] using
          Finset.mem_union_right
            (constantSupport (normalize leftTerm)) membership
  | hom name body inductionHypothesis =>
      simp only [replaceBasisConstants]
      congr 1
      apply inductionHypothesis acuih
      intro basis membership
      apply agree basis
      simpa using membership
  | free body inductionHypothesis => exact False.elim acuih

/-- For a valid solved certificate, the local rank-bounded replacement used
by `resolveERepresentative` agrees with the global replacement on the whole
solved representative body. -/
theorem resolveERepresentative_normalize
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (representative : EOccurrence left right)
    (fixed : configuration.1 representative = some representative) :
    normalize (resolveERepresentative left right configuration values
        representative) =
      wrapE
        (normalize
          (replaceBasisConstants
            (resolveECombinationBasis left right configuration values)
            (reify
              (applyAbstractMatrixAssignment values
                (reify
                  (purifiedOccurrenceBody left right configuration
                    representative)))))) := by
  let abstractBody := applyAbstractMatrixAssignment values
    (reify (purifiedOccurrenceBody left right configuration representative))
  let localReplacement : ECombinationBasis left right →
      Term Const (Fin 0) Hom := fun basis =>
    match basis with
    | .inl constant => .const constant
    | .inr dependency =>
        if smaller : configuration.2 dependency <
            configuration.2 representative then
          resolveERepresentative left right configuration values dependency
        else
          .zero
  have replacementsAgree : replaceBasisConstants localReplacement
      (reify abstractBody) =
    replaceBasisConstants
      (resolveECombinationBasis left right configuration values)
      (reify abstractBody) := by
    apply replaceBasisConstants_congr_acuih
    · apply reify_isACUIh
      dsimp only [abstractBody, applyAbstractMatrixAssignment]
      apply isACUIh_normalize
      apply isACUIh_substitute
      · intro name
        apply reify_isACUIh
        exact isACUIh_decodeGroundMatrix values name
      · exact reify_purifyNormalForm_isACUIh left right configuration
          representative.body
    · intro basis membership
      rcases basis with constant | dependency
      · rfl
      · by_cases smaller : configuration.2 dependency <
            configuration.2 representative
        · simp [localReplacement, resolveECombinationBasis, smaller]
        · have coefficientZero :=
            abstract_representative_body_nonsmaller_coefficient_zero
              left right configuration values valid below representative
              dependency fixed smaller
          have coefficientNonzero : constantCoefficient abstractBody
              (Sum.inr dependency) ≠ 0 := by
            intro targetZero
            have canonicalMembership : Sum.inr dependency ∈
                constantSupport (canonicalize abstractBody) := by
              change Sum.inr dependency ∈
                constantSupport (normalize (reify abstractBody))
              exact membership
            have paths := (mem_constantSupport
              (canonicalize abstractBody) (Sum.inr dependency)).mp
                canonicalMembership
            rcases paths with ⟨path, pathMembership⟩
            have pathInCoefficient := (mem_constantCoefficient
              (canonicalize abstractBody) (Sum.inr dependency) path).mpr
                pathMembership
            have canonicalCoefficientNonzero : constantCoefficient
                (canonicalize abstractBody) (Sum.inr dependency) ≠ 0 := by
              intro zeroEquality
              rw [zeroEquality] at pathInCoefficient
              simp at pathInCoefficient
            rw [constantCoefficient_canonicalize, targetZero] at canonicalCoefficientNonzero
            exact canonicalCoefficientNonzero rfl
          exact False.elim (coefficientNonzero coefficientZero)
  rw [resolveERepresentative]
  rw [normalize_free]
  change wrapE
      (normalize (replaceBasisConstants localReplacement
        (reify abstractBody))) = _
  rw [replacementsAgree]

/-! ## Address-free reconstruction -/

private def expandedAbstractValue
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (target : NormalForm (ECombinationBasis left right) Var Hom) :
    NormalForm Const (Fin 0) Hom :=
  expandNormalForm
    (resolveECombinationBasis left right configuration values)
    (evaluateNormalForm
      (decodeAbstractEValue left right values) target)

@[simp]
private theorem expandedAbstractValue_empty
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom)) :
    expandedAbstractValue left right configuration values ∅ = ∅ := by
  simp [expandedAbstractValue]

private theorem expandedAbstractValue_union
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (first second : NormalForm (ECombinationBasis left right) Var Hom) :
    expandedAbstractValue left right configuration values (first ∪ second) =
      expandedAbstractValue left right configuration values first ∪
        expandedAbstractValue left right configuration values second := by
  unfold expandedAbstractValue
  rw [evaluateNormalForm_union, expandNormalForm_union]

private theorem expandedAbstractValue_singleton_constant
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (path : List Hom) (basis : ECombinationBasis left right) :
    expandedAbstractValue left right configuration values
        ({(path, .constant basis)} :
          NormalForm (ECombinationBasis left right) Var Hom) =
      prefixHomPath path
        (normalize
          (resolveECombinationBasis left right configuration values basis)) := by
  unfold expandedAbstractValue
  rw [evaluateNormalForm_singleton_constant,
    expandNormalForm_prefixHomPath]
  unfold constantForm
  rw [expandNormalForm_singleton_constant]
  simp [prefixHomPath]

private theorem expandedAbstractValue_eq_term_expansion
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (target : NormalForm (ECombinationBasis left right) Var Hom) :
    expandedAbstractValue left right configuration values target =
      normalize
        (replaceBasisConstants
          (resolveECombinationBasis left right configuration values)
          (reify
            (applyAbstractMatrixAssignment values (reify target)))) := by
  unfold expandedAbstractValue
  rw [evaluateNormalForm_eq_applyGroundAssignment,
    expandNormalForm_eq_normalize_replaceBasisConstants]
  rfl

private theorem evaluateNormalForm_decodeAbstractEValue
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (target : NormalForm (ECombinationBasis left right) Var Hom) :
    evaluateNormalForm (decodeAbstractEValue left right values) target =
      applyAbstractMatrixAssignment values (reify target) := by
  rw [evaluateNormalForm_eq_applyGroundAssignment]
  rfl

structure ReconstructionProofScan
    (Const Var Hom : Type u)
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom)) where
  source : NormalForm Const Var Hom
  bodies : Finset (NormalForm Const Var Hom)
  purified : NormalForm (ECombinationBasis left right) Var Hom
  purifies : (source, purified) =
    purificationPair left right configuration source
  scans : bodies = (scanEBodySet source).2
  reconstructs : bodies ⊆ allEBodySet left right →
    evaluateNormalForm
        (decodeECombinationAssignment left right configuration values) source =
      expandedAbstractValue left right configuration values purified

private theorem ReconstructionProofScan.purified_eq
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    {configuration : EConfiguration left right}
    {values : Matrix Var (ECombinationBasis left right) (HomContext Hom)}
    (result : ReconstructionProofScan Const Var Hom left right configuration values) :
    result.purified =
      purifyNormalForm left right configuration result.source := by
  have proofPair := result.purifies
  have executablePair := purifyNormalFormScan_pair
    left right configuration result.source
  unfold purifyNormalForm
  exact (congrArg Prod.snd proofPair).trans
    (congrArg Prod.snd executablePair).symm

@[simp]
private theorem purificationPair_empty
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right) :
    purificationPair left right configuration ∅ = (∅, ∅) := by
  simp [purificationPair]

private theorem purificationPair_union
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (first second : NormalForm Const Var Hom) :
    purificationPair left right configuration (first ∪ second) =
      let firstResult := purificationPair left right configuration first
      let secondResult := purificationPair left right configuration second
      (firstResult.1 ∪ secondResult.1,
        firstResult.2 ∪ secondResult.2) := by
  unfold purificationPair
  apply NormalForm.fold_union
  intro result
  apply Prod.ext <;> exact normalUnionEmpty _

@[simp]
private theorem purificationPair_singleton_constant
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (path : List Hom) (name : Const) :
    purificationPair left right configuration
        ({(path, .constant name)} : NormalForm Const Var Hom) =
      ({(path, .constant name)}, {(path, .constant (.inl name))}) := by
  unfold purificationPair
  rw [NormalForm.fold_singleton]
  apply Prod.ext <;> exact normalUnionEmpty _

@[simp]
private theorem purificationPair_singleton_variable
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (path : List Hom) (name : Var) :
    purificationPair left right configuration
        ({(path, .variable name)} : NormalForm Const Var Hom) =
      ({(path, .variable name)}, {(path, .variable name)}) := by
  unfold purificationPair
  rw [NormalForm.fold_singleton]
  apply Prod.ext <;> exact normalUnionEmpty _

private theorem purificationPair_first
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (target : NormalForm Const Var Hom) :
    (purificationPair left right configuration target).1 = target := by
  unfold purificationPair
  have mapped := NormalForm.fold_hom
    (fun result : NormalForm Const Var Hom ×
        NormalForm (ECombinationBasis left right) Var Hom => result.1)
    (∅, ∅)
    (fun first second =>
      (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun path name =>
      ({(path, .variable name)}, {(path, .variable name)}))
    (fun path body =>
      let purified : NormalForm (ECombinationBasis left right) Var Hom :=
        alienConstantAtPath path (classOfBody? left right configuration body.1)
      ({(path, .eOperator body.1)}, purified))
    (∅ : NormalForm Const Var Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    rfl (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) target
  exact mapped.trans (rebuildNormalForm_eq target)

private theorem purificationPair_singleton_eOperator
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (path : List Hom) (body : NormalForm Const Var Hom) :
    purificationPair left right configuration
        ({(path, .eOperator body)} : NormalForm Const Var Hom) =
      ({(path, .eOperator body)},
        alienConstantAtPath path (classOfBody? left right configuration body)) := by
  unfold purificationPair
  rw [NormalForm.fold_singleton]
  change
    let bodyResult := purificationPair left right configuration body
    let result := purificationPairEOperator left right configuration path bodyResult
    (result.1 ∪ ∅, result.2 ∪ ∅) = _
  simp only [purificationPairEOperator]
  rw [purificationPair_first left right configuration body]
  apply Prod.ext <;> exact normalUnionEmpty _

private def reconstructionProofZero
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom)) :
    ReconstructionProofScan Const Var Hom left right configuration values :=
  ⟨∅, ∅, ∅, by simp, by simp, by simp [expandedAbstractValue]⟩

private def reconstructionProofCombine
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (first second :
      ReconstructionProofScan Const Var Hom left right configuration values) :
    ReconstructionProofScan Const Var Hom left right configuration values :=
  ⟨first.source ∪ second.source,
    first.bodies ∪ second.bodies,
    first.purified ∪ second.purified,
    by
      rw [purificationPair_union, ← first.purifies, ← second.purifies]
    , by
      rw [scanEBodySet_union, first.scans, second.scans]
    , by
      intro included
      have firstIncluded : first.bodies ⊆ allEBodySet left right :=
        Finset.Subset.trans Finset.subset_union_left included
      have secondIncluded : second.bodies ⊆ allEBodySet left right :=
        Finset.Subset.trans Finset.subset_union_right included
      rw [evaluateNormalForm_union, first.reconstructs firstIncluded,
        second.reconstructs secondIncluded]
      unfold expandedAbstractValue
      rw [evaluateNormalForm_union, expandNormalForm_union]⟩

private def reconstructionProofConstant
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (path : List Hom) (name : Const) :
    ReconstructionProofScan Const Var Hom left right configuration values :=
  ⟨{(path, .constant name)}, ∅, {(path, .constant (.inl name))},
    by simp,
    by simp,
    by
      intro _
      unfold expandedAbstractValue
      rw [evaluateNormalForm_singleton_constant,
        evaluateNormalForm_singleton_constant,
        expandNormalForm_prefixHomPath]
      unfold constantForm
      rw [expandNormalForm_singleton_constant]
      rfl⟩

private def reconstructionProofVariable
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (path : List Hom) (name : Var) :
    ReconstructionProofScan Const Var Hom left right configuration values :=
  ⟨{(path, .variable name)}, ∅, {(path, .variable name)},
    by simp,
    by simp,
    by
      intro _
      rw [evaluateNormalForm_singleton_variable]
      unfold expandedAbstractValue
      rw [evaluateNormalForm_singleton_variable,
        expandNormalForm_prefixHomPath,
        expandNormalForm_canonicalize]
      unfold decodeECombinationAssignment
      rw [canonicalize_normalize,
        expandNormalForm_eq_normalize_replaceBasisConstants]⟩

private def reconstructionProofEOperator
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (path : List Hom)
    (body : ReconstructionProofScan Const Var Hom
      left right configuration values) :
    ReconstructionProofScan Const Var Hom left right configuration values :=
  let purified : NormalForm (ECombinationBasis left right) Var Hom :=
    alienConstantAtPath path (classOfBody? left right configuration body.source)
  ⟨{(path, .eOperator body.source)},
    insert body.source body.bodies,
    purified,
    by
      rw [purificationPair_singleton_eOperator]
    , by
      rw [scanEBodySet_singleton_eOperator, body.scans]
    , by
      intro included
      have bodyMembership : body.source ∈ allEBodies left right :=
        mem_allEBodies_iff.mpr
          (included (Finset.mem_insert_self _ _))
      rcases findEOccurrence?_of_mem left right body.source bodyMembership with
        ⟨occurrence, found, occurrenceBodyEquality⟩
      have classEquality : classOfBody? left right configuration body.source =
          configuration.1 occurrence := by
        unfold classOfBody?
        rw [found]
        rfl
      have bodyIncluded : body.bodies ⊆ allEBodySet left right :=
        Finset.Subset.trans (Finset.subset_insert _ _) included
      have bodyReconstruction := body.reconstructs bodyIncluded
      have bodyPurified := body.purified_eq
      have abstractClassTerm := eCombination_abstract_body_class
        left right configuration values below occurrence
      have abstractClass : evaluateNormalForm
          (decodeAbstractEValue left right values) body.purified =
        match configuration.1 occurrence with
        | none => ∅
        | some representative =>
            evaluateNormalForm (decodeAbstractEValue left right values)
              (purifiedOccurrenceBody left right configuration representative) := by
        rw [bodyPurified]
        unfold purifiedOccurrenceBody
        rw [← occurrenceBodyEquality]
        simp_rw [evaluateNormalForm_decodeAbstractEValue]
        exact abstractClassTerm
      cases classResult : configuration.1 occurrence with
      | none =>
          rw [classResult] at abstractClass
          have bodyZero : evaluateNormalForm
              (decodeECombinationAssignment left right configuration values)
              body.source = ∅ := by
            rw [bodyReconstruction]
            unfold expandedAbstractValue
            rw [abstractClass, expandNormalForm_empty]
          rw [evaluateNormalForm_singleton_eOperator, bodyZero,
            wrapE_empty, prefixHomPath_empty]
          simp [expandedAbstractValue, purified, classEquality, classResult]
      | some representative =>
          rw [classResult] at abstractClass
          have fixed := EConfiguration.valid_representative
            configuration valid classResult
          have resolution := resolveERepresentative_normalize
            left right configuration values valid below representative fixed
          rw [← expandedAbstractValue_eq_term_expansion
            left right configuration values
              (purifiedOccurrenceBody left right configuration representative)]
            at resolution
          have expandedClass :
              expandedAbstractValue left right configuration values
                  body.purified =
                expandedAbstractValue left right configuration values
                  (purifiedOccurrenceBody left right configuration
                    representative) := by
            unfold expandedAbstractValue
            rw [abstractClass]
          rw [evaluateNormalForm_singleton_eOperator, bodyReconstruction,
            expandedClass]
          rw [show purified =
              ({(path, .constant (.inr representative))} :
                NormalForm (ECombinationBasis left right) Var Hom) by
              simp [purified, classEquality, classResult],
            expandedAbstractValue_singleton_constant]
          simp only [resolveECombinationBasis]
          rw [resolution]⟩

/-- Reconstruct every fragment in one body-keyed normal-form fold. -/
def reconstructionProofScan
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (target : NormalForm Const Var Hom) :
    ReconstructionProofScan Const Var Hom left right configuration values :=
  target.fold
    (reconstructionProofZero left right configuration values)
    (reconstructionProofCombine left right configuration values)
    (reconstructionProofConstant left right configuration values)
    (reconstructionProofVariable left right configuration values)
    (reconstructionProofEOperator left right configuration values valid below)

@[simp]
theorem reconstructionProofScan_source
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (target : NormalForm Const Var Hom) :
    (reconstructionProofScan left right configuration values valid below target).source =
      target := by
  unfold reconstructionProofScan
  have mapped := NormalForm.fold_hom
    (fun result : ReconstructionProofScan Const Var Hom
        left right configuration values => result.source)
    (reconstructionProofZero left right configuration values)
    (reconstructionProofCombine left right configuration values)
    (reconstructionProofConstant left right configuration values)
    (reconstructionProofVariable left right configuration values)
    (reconstructionProofEOperator left right configuration values valid below)
    (∅ : NormalForm Const Var Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    rfl (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) target
  exact mapped.trans (rebuildNormalForm_eq target)

theorem reconstructionProofScan_purified
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (target : NormalForm Const Var Hom) :
    (reconstructionProofScan left right configuration values valid below target).purified =
      purifyNormalForm left right configuration target := by
  let result := reconstructionProofScan
    left right configuration values valid below target
  calc
    result.purified = purifyNormalForm left right configuration result.source :=
      result.purified_eq
    _ = purifyNormalForm left right configuration target := by
      rw [reconstructionProofScan_source]

theorem reconstructionProofScan_bodies
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (target : NormalForm Const Var Hom) :
    (reconstructionProofScan left right configuration values valid below target).bodies =
      (scanEBodySet target).2 := by
  let result := reconstructionProofScan
    left right configuration values valid below target
  calc
    result.bodies = (scanEBodySet result.source).2 := result.scans
    _ = (scanEBodySet target).2 := by rw [reconstructionProofScan_source]

/-- Expanding direct normal-form purification reconstructs the original
fragment.  The only premise is semantic membership of its finite E-body set. -/
theorem reconstruct_purifyNormalForm
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (target : NormalForm Const Var Hom)
    (included : (scanEBodySet target).2 ⊆ allEBodySet left right) :
    applyGroundAssignment
        (decodeECombinationAssignment left right configuration values) target =
      expandedAbstractValue left right configuration values
        (purifyNormalForm left right configuration target) := by
  let result := reconstructionProofScan
    left right configuration values valid below target
  have bodyInclusion : result.bodies ⊆ allEBodySet left right := by
    rw [reconstructionProofScan_bodies]
    exact included
  have reconstructed := result.reconstructs bodyInclusion
  rw [reconstructionProofScan_source,
    reconstructionProofScan_purified,
    evaluateNormalForm_eq_applyGroundAssignment] at reconstructed
  exact reconstructed

/-- Ground normal forms over the empty variable type are recursively ground,
including inside `E` bodies. -/
theorem normalForm_isGround_fin_zero
    {Const Hom : Type u}
    [Encodable Const] [Encodable Hom]
    (target : NormalForm Const (Fin 0) Hom) : target.IsGround := by
  unfold NormalForm.IsGround NormalForm.isGround
  have folded := NormalForm.fold_hom
    (fun _ : Unit => true)
    () (fun _ _ => ()) (fun _ _ => ())
    (fun _ impossible => impossible.elim0)
    (fun _ _ => ())
    true (fun first second => first && second)
    (fun _ _ => true)
    (fun _ _ => false)
    (fun _ bodyGround => bodyGround)
    rfl (by intros; rfl) (by intros; rfl)
    (by intro path impossible; exact impossible.elim0)
    (by intros; rfl) target
  exact folded.symm

/-- Interpreting abstract basis constants by arbitrary ground ACUIhE terms
preserves semilattice inclusion between canonical abstract forms. -/
theorem replaceBasisConstants_preserves_below
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (left right : NormalForm Basis (Fin 0) Hom)
    (leftCanonical : IsCanonical left)
    (rightCanonical : IsCanonical right)
    (below : Below (Hom := Hom) left right) :
    Below (Hom := Hom)
      (normalize (replaceBasisConstants replacement (reify left)))
      (normalize (replaceBasisConstants replacement (reify right))) := by
  have sourceNormalization : normalize
      (.add (reify left) (reify right)) = normalize (reify right) := by
    simp only [normalize_add]
    change canonicalize left ∪ canonicalize right = canonicalize right
    rw [leftCanonical, rightCanonical]
    exact below
  have sourceDerivation : Derives
      (.add (reify left) (reify right)) (reify right) :=
    derives_of_normalize_eq sourceNormalization
  have targetNormalization := normalize_eq_of_derives
    (replaceBasisConstants_respectsDerives replacement sourceDerivation)
  change normalize (replaceBasisConstants replacement (reify left)) ∪
      normalize (replaceBasisConstants replacement (reify right)) =
    normalize (replaceBasisConstants replacement (reify right))
  exact targetNormalization

/-- Whole-side form of address-free normal-form reconstruction. -/
theorem reconstruct_side
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values)
    (side : Bool) :
    applyGroundAssignment
        (decodeECombinationAssignment left right configuration values)
        (if side then right else left) =
      normalize
        (replaceBasisConstants
          (resolveECombinationBasis left right configuration values)
          (reify
            (applyAbstractMatrixAssignment values
              (reify (purifiedSide left right configuration side))))) := by
  unfold purifiedSide
  cases side with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact (reconstruct_purifyNormalForm left right configuration values
        valid below left Finset.subset_union_left).trans
          (expandedAbstractValue_eq_term_expansion
            left right configuration values
              (purifyNormalForm left right configuration left))
  | true =>
      simp only [if_true]
      exact (reconstruct_purifyNormalForm left right configuration values
        valid below right Finset.subset_union_right).trans
          (expandedAbstractValue_eq_term_expansion
            left right configuration values
              (purifyNormalForm left right configuration right))

/-- Every matrix satisfying a valid certificate reconstructs to a genuine
solution of the original ACUIhE inequality. -/
theorem eCombination_reconstruction_solved
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (values : Matrix Var (ECombinationBasis left right) (HomContext Hom))
    (valid : configuration.valid = true)
    (below : eCombinationMatrixBelow left right configuration values) :
    IsSolvedInequality
      (applyGroundAssignment
        (decodeECombinationAssignment left right configuration values) left)
      (applyGroundAssignment
        (decodeECombinationAssignment left right configuration values) right) := by
  let abstractLeft := applyAbstractMatrixAssignment values
    (reify (purifiedSide left right configuration false))
  let abstractRight := applyAbstractMatrixAssignment values
    (reify (purifiedSide left right configuration true))
  have abstractSolved := eCombination_matrix_solution_solved_row
    left right configuration values below (.inl ()) True.intro
  change IsSolvedInequality abstractLeft abstractRight at abstractSolved
  have abstractLeftCanonical : IsCanonical abstractLeft := by
    dsimp only [abstractLeft, applyAbstractMatrixAssignment]
    exact canonicalize_normalize _
  have abstractRightCanonical : IsCanonical abstractRight := by
    dsimp only [abstractRight, applyAbstractMatrixAssignment]
    exact canonicalize_normalize _
  have expandedBelow := replaceBasisConstants_preserves_below
    (resolveECombinationBasis left right configuration values)
    abstractLeft abstractRight abstractLeftCanonical abstractRightCanonical
    abstractSolved.2.2
  have leftReconstruction := reconstruct_side
    left right configuration values valid below false
  have rightReconstruction := reconstruct_side
    left right configuration values valid below true
  change applyGroundAssignment
      (decodeECombinationAssignment left right configuration values) left =
    normalize
      (replaceBasisConstants
        (resolveECombinationBasis left right configuration values)
        (reify abstractLeft)) at leftReconstruction
  change applyGroundAssignment
      (decodeECombinationAssignment left right configuration values) right =
    normalize
      (replaceBasisConstants
        (resolveECombinationBasis left right configuration values)
        (reify abstractRight)) at rightReconstruction
  refine ⟨normalForm_isGround_fin_zero _, normalForm_isGround_fin_zero _, ?_⟩
  rw [leftReconstruction, rightReconstruction]
  exact expandedBelow

/-- Validity plus one exact matrix witness is sufficient for productivity;
reconstruction does not depend on which witness the search returns. -/
theorem productiveEConfiguration_of_valid_matrix
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (valid : configuration.valid = true)
    (matrixSolution : ∃ values :
      Matrix Var (ECombinationBasis left right) (HomContext Hom),
        eCombinationMatrixBelow left right configuration values) :
    ProductiveEConfiguration left right configuration := by
  refine ⟨valid, matrixSolution, ?_⟩
  intro values below
  apply (checkGroundInequality_eq_true_iff _ _).mpr
  exact eCombination_reconstruction_solved
    left right configuration values valid below

/-- Every genuine solution induces a productive finite alien certificate. -/
theorem exists_productive_configuration_of_solution
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (solved : IsSolvedInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right)) :
    ∃ configuration : EConfiguration left right,
      ProductiveEConfiguration left right configuration := by
  rcases exists_valid_configuration_matrix_of_solution
      left right assignment solved with
    ⟨configuration, valid, matrixSolution⟩
  exact ⟨configuration,
    productiveEConfiguration_of_valid_matrix
      left right configuration valid matrixSolution⟩

/-- Unconditional completeness of the total ACUIhE solver.  No arbitrary
search cutoff, extra premise, or caller-supplied certificate occurs here. -/
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

/-- Solver failure is equivalent to genuine ACUIhE unsatisfiability. -/
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


end ACUIHE.Solver.Search
