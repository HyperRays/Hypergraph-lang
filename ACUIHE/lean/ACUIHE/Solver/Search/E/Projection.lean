import ACUIHE.Solver.Search.E.Combination

/-!
The forward half of ACUIhE completeness.

Given an arbitrary genuine ground solution, this module evaluates every
canonical `E` body, groups equal evaluated bodies, assigns representatives by
strict structural rank, and projects the solution to the purified ACUIh matrix
problem.  `ProjectionProofScan` is the central invariant: one intrinsic
normal-form fold proves that evaluation commutes with purification and records
the dependencies needed to validate the finite certificate.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver
open ACUIHE.Solver.Linear
open ACUIHE.Solver.NormalForm.Internal

universe u v w x

local instance completenessEncodableDecidableEq
    {Alpha : Type*} [Encodable Alpha] : DecidableEq Alpha :=
  eCombinationDecidableEq

local instance (priority := 2000) completenessBasisFintype
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Fintype (ECombinationBasis left right) :=
  FinEnum.instFintype

local instance normalUnionCommutative
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Commutative
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun left right => by
    apply NormalForm.ext_raw
    exact rawUnion_comm left.raw right.raw⟩

local instance normalUnionAssociative
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Associative
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun left middle right => by
    apply NormalForm.ext_raw
    exact rawUnion_assoc left.raw middle.raw right.raw⟩

local instance normalUnionIdempotent
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.IdempotentOp
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun value => by
    apply NormalForm.ext_raw
    exact rawUnion_self value.raw⟩

theorem projectGroundNormalFormPair_first
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const (Fin 0) Hom) :
    (projectGroundNormalFormPair left right assignment target).1 = target := by
  have folded := NormalForm.fold_hom
    (fun result : NormalForm Const (Fin 0) Hom ×
        NormalForm (ECombinationBasis left right) (Fin 0) Hom => result.1)
    (∅, ∅)
    (fun first second => (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      let original : NormalForm Const (Fin 0) Hom :=
        {(path, .eOperator body.1)}
      let projected : NormalForm
          (ECombinationBasis left right) (Fin 0) Hom :=
        match representativeForBody? left right assignment body.1 with
        | none => ∅
        | some representative => {(path, .constant (.inr representative))}
      (original, projected))
    (∅ : NormalForm Const (Fin 0) Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    (by rfl) (by intro first second; rfl)
    (by intro path name; rfl)
    (by intro path impossible; exact impossible.elim0)
    (by intro path body; rfl) target
  refine Eq.trans ?_ (rebuildNormalForm_eq target)
  unfold projectGroundNormalFormPair
  exact folded

theorem normalUnionEmpty
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (value : NormalForm Const Var Hom) : value ∪ ∅ = value := by
  apply NormalForm.ext_raw
  exact rawUnion_empty value.raw

local instance projectionPairCommutative
    {Const₁ Var₁ Const₂ Var₂ Hom : Type*}
    [Encodable Const₁] [Encodable Var₁]
    [Encodable Const₂] [Encodable Var₂] [Encodable Hom] :
    Std.Commutative (fun first second :
        NormalForm Const₁ Var₁ Hom × NormalForm Const₂ Var₂ Hom =>
      (first.1 ∪ second.1, first.2 ∪ second.2)) :=
  ⟨by intro first second; apply Prod.ext <;> apply normalUnionCommutative.comm⟩

local instance projectionPairAssociative
    {Const₁ Var₁ Const₂ Var₂ Hom : Type*}
    [Encodable Const₁] [Encodable Var₁]
    [Encodable Const₂] [Encodable Var₂] [Encodable Hom] :
    Std.Associative (fun first second :
        NormalForm Const₁ Var₁ Hom × NormalForm Const₂ Var₂ Hom =>
      (first.1 ∪ second.1, first.2 ∪ second.2)) :=
  ⟨by intro first middle last; apply Prod.ext <;>
    apply normalUnionAssociative.assoc⟩

local instance projectionPairIdempotent
    {Const₁ Var₁ Const₂ Var₂ Hom : Type*}
    [Encodable Const₁] [Encodable Var₁]
    [Encodable Const₂] [Encodable Var₂] [Encodable Hom] :
    Std.IdempotentOp (fun first second :
        NormalForm Const₁ Var₁ Hom × NormalForm Const₂ Var₂ Hom =>
      (first.1 ∪ second.1, first.2 ∪ second.2)) :=
  ⟨by intro value; apply Prod.ext <;> apply normalUnionIdempotent.idempotent⟩

theorem projectGroundNormalFormPair_union
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (first second : NormalForm Const (Fin 0) Hom) :
    projectGroundNormalFormPair left right assignment (first ∪ second) =
      let firstResult := projectGroundNormalFormPair left right assignment first
      let secondResult := projectGroundNormalFormPair left right assignment second
      (firstResult.1 ∪ secondResult.1,
        firstResult.2 ∪ secondResult.2) := by
  unfold projectGroundNormalFormPair
  apply NormalForm.fold_union
  intro value
  apply Prod.ext <;> apply normalUnionEmpty

theorem projectGroundNormalForm_union
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (first second : NormalForm Const (Fin 0) Hom) :
    projectGroundNormalForm left right assignment (first ∪ second) =
      projectGroundNormalForm left right assignment first ∪
        projectGroundNormalForm left right assignment second := by
  exact congrArg Prod.snd
    (projectGroundNormalFormPair_union left right assignment first second)

private theorem prefixHom_singleton
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (path : List Hom) (atom : NormalAtom Const Var Hom) :
    prefixHom name ({(path, atom)} : NormalForm Const Var Hom) =
      {(name :: path, atom)} := by
  rcases atom with constant | «variable» | body
  all_goals
  apply NormalForm.ext_raw
  all_goals exact RecursiveFinset.image_singleton _ _

theorem projectGroundNormalFormPair_prefixHom
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (name : Hom) (target : NormalForm Const (Fin 0) Hom) :
    projectGroundNormalFormPair left right assignment (prefixHom name target) =
      let result := projectGroundNormalFormPair left right assignment target
      (prefixHom name result.1, prefixHom name result.2) := by
  have folded := NormalForm.fold_prefixHom
    (∅, ∅)
    (fun first second => (first.1 ∪ second.1, first.2 ∪ second.2))
    (by intro value; apply Prod.ext <;> apply normalUnionEmpty)
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      let original : NormalForm Const (Fin 0) Hom :=
        {(path, .eOperator body.1)}
      let projected : NormalForm
          (ECombinationBasis left right) (Fin 0) Hom :=
        match representativeForBody? left right assignment body.1 with
        | none => ∅
        | some representative => {(path, .constant (.inr representative))}
      (original, projected))
    name
    (fun result => (prefixHom name result.1, prefixHom name result.2))
    (by apply Prod.ext <;> apply prefixHom_empty)
    (by intro first second; apply Prod.ext <;> apply prefixHom_union)
    (by
      intro path constant
      apply Prod.ext
      · exact (prefixHom_singleton name path (.constant constant)).symm
      · exact (prefixHom_singleton name path
          (.constant (Sum.inl constant : ECombinationBasis left right))).symm)
    (by intro path impossible; exact impossible.elim0)
    (by
      intro path body
      dsimp only
      cases representativeForBody? left right assignment body.1 with
      | none =>
        apply Prod.ext
        · exact (prefixHom_singleton name path (.eOperator body.1)).symm
        · exact (prefixHom_empty name).symm
      | some representative =>
        apply Prod.ext
        · exact (prefixHom_singleton name path (.eOperator body.1)).symm
        · exact (prefixHom_singleton name path
            (.constant (Sum.inr representative :
              ECombinationBasis left right))).symm)
    target
  unfold projectGroundNormalFormPair
  exact folded

theorem projectGroundNormalForm_prefixHom
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (name : Hom) (target : NormalForm Const (Fin 0) Hom) :
    projectGroundNormalForm left right assignment (prefixHom name target) =
      prefixHom name (projectGroundNormalForm left right assignment target) := by
  exact congrArg Prod.snd
    (projectGroundNormalFormPair_prefixHom left right assignment name target)

theorem projectGroundNormalForm_wrapE
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (body : NormalForm Const (Fin 0) Hom) :
    projectGroundNormalForm left right assignment (wrapE body) =
      if body = ∅ then ∅ else
        match representativeForBody? left right assignment body with
        | none => ∅
        | some representative =>
            {([], .constant (Sum.inr representative))} := by
  by_cases bodyZero : body = ∅
  · subst body
    simp [projectGroundNormalForm, projectGroundNormalFormPair]
  · rw [if_neg bodyZero, wrapE_of_ne_empty bodyZero]
    have singletonFold :
        projectGroundNormalFormPair left right assignment
            ({([], .eOperator body)} : NormalForm Const (Fin 0) Hom) =
          let bodyResult :=
            projectGroundNormalFormPair left right assignment body
          let projected : NormalForm
              (ECombinationBasis left right) (Fin 0) Hom :=
            match representativeForBody? left right assignment bodyResult.1 with
            | none => ∅
            | some representative =>
                {([], .constant (Sum.inr representative))}
          ({([], .eOperator bodyResult.1)} ∪ ∅, projected ∪ ∅) := by
      unfold projectGroundNormalFormPair
      rw [NormalForm.fold_singleton]
      rfl
    unfold projectGroundNormalForm
    rw [singletonFold]
    dsimp only
    rw [projectGroundNormalFormPair_first]
    cases representativeForBody? left right assignment body <;>
      simp [normalUnionEmpty]

theorem findEOccurrence?_of_mem
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (body : NormalForm Const Var Hom)
    (membership : body ∈ allEBodies left right) :
    ∃ occurrence : EOccurrence left right,
      findEOccurrence? left right body = some occurrence ∧
        occurrence.body = body := by
  let selected : EOccurrence left right := ⟨body, membership⟩
  unfold findEOccurrence?
  cases found : (FinEnum.toList (EOccurrence left right)).find?
      (fun occurrence => occurrence.body = body) with
  | none =>
      have rejects := List.find?_eq_none.mp found selected
        (FinEnum.mem_toList selected)
      exact False.elim (rejects (by
        change decide (body = body) = true
        simp))
  | some occurrence =>
      refine ⟨occurrence, rfl, ?_⟩
      have accepted : decide (occurrence.body = body) = true :=
        List.find?_some (p := fun occurrence : EOccurrence left right =>
          occurrence.body = body) found
      exact of_decide_eq_true accepted

theorem representativeForBody?_some_value
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (body : NormalForm Const (Fin 0) Hom)
    {representative : EOccurrence left right}
    (found : representativeForBody? left right assignment body =
      some representative) :
    occurrenceBodyValue left right assignment representative = body := by
  unfold representativeForBody? at found
  have accepted : decide
      (occurrenceBodyValue left right assignment representative = body) = true :=
    List.find?_some
      (p := fun occurrence : EOccurrence left right =>
        occurrenceBodyValue left right assignment occurrence = body) found
  exact of_decide_eq_true accepted

theorem representativeForBody?_of_occurrence
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right) :
    ∃ representative : EOccurrence left right,
      representativeForBody? left right assignment
          (occurrenceBodyValue left right assignment occurrence) =
        some representative := by
  unfold representativeForBody?
  cases found : (FinEnum.toList (EOccurrence left right)).find?
      (fun candidate => occurrenceBodyValue left right assignment candidate =
        occurrenceBodyValue left right assignment occurrence) with
  | none =>
      have rejects := List.find?_eq_none.mp found occurrence
        (FinEnum.mem_toList occurrence)
      exact False.elim (rejects (by simp))
  | some representative => exact ⟨representative, rfl⟩

theorem projectedOccurrenceClass_eq_some
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right)
    (nonzero : occurrenceBodyValue left right assignment occurrence ≠ ∅) :
    ∃ representative : EOccurrence left right,
      projectedOccurrenceClass left right assignment occurrence =
          some representative ∧
        occurrenceBodyValue left right assignment representative =
          occurrenceBodyValue left right assignment occurrence := by
  rcases representativeForBody?_of_occurrence left right assignment occurrence with
    ⟨representative, found⟩
  refine ⟨representative, ?_,
    representativeForBody?_some_value left right assignment _ found⟩
  simp [projectedOccurrenceClass, nonzero, found]

theorem projectedOccurrenceClass_representative
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    {occurrence representative : EOccurrence left right}
    (classEquality : projectedOccurrenceClass left right assignment occurrence =
      some representative) :
    projectedOccurrenceClass left right assignment representative =
      some representative := by
  unfold projectedOccurrenceClass at classEquality ⊢
  dsimp only at classEquality ⊢
  by_cases occurrenceZero :
      occurrenceBodyValue left right assignment occurrence = ∅
  · simp [occurrenceZero] at classEquality
  simp [occurrenceZero] at classEquality
  have found : representativeForBody? left right assignment
      (occurrenceBodyValue left right assignment occurrence) =
      some representative := classEquality
  have valueEquality := representativeForBody?_some_value
    left right assignment _ found
  rw [valueEquality]
  simp [occurrenceZero, found]

theorem projectedOccurrenceClass_some_value
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    {occurrence representative : EOccurrence left right}
    (classEquality : projectedOccurrenceClass left right assignment occurrence =
      some representative) :
    occurrenceBodyValue left right assignment representative =
      occurrenceBodyValue left right assignment occurrence := by
  unfold projectedOccurrenceClass at classEquality
  dsimp only at classEquality
  by_cases occurrenceZero :
      occurrenceBodyValue left right assignment occurrence = ∅
  · simp [occurrenceZero] at classEquality
  simp [occurrenceZero] at classEquality
  exact representativeForBody?_some_value left right assignment _ classEquality

theorem projectedOccurrenceClass_none_value
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    {occurrence : EOccurrence left right}
    (classEquality : projectedOccurrenceClass left right assignment occurrence =
      none) :
    occurrenceBodyValue left right assignment occurrence = ∅ := by
  by_contra nonzero
  rcases projectedOccurrenceClass_eq_some
      left right assignment occurrence nonzero with
    ⟨representative, projected, _⟩
  rw [projected] at classEquality
  contradiction

theorem projectedOccurrenceClass_some_nonzero
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    {occurrence representative : EOccurrence left right}
    (classEquality : projectedOccurrenceClass left right assignment occurrence =
      some representative) :
    occurrenceBodyValue left right assignment occurrence ≠ ∅ := by
  intro valueZero
  unfold projectedOccurrenceClass at classEquality
  simp [valueZero] at classEquality

private theorem normalSingletonConstant_isACUIh
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Const) :
    isACUIh ({(path, .constant name)} : NormalForm Const Var Hom) = true := by
  simp [isACUIh, NormalForm.fold_singleton]

private theorem foldAllTrue
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    target.fold true (fun left right => left && right)
      (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) = true := by
  have folded := NormalForm.fold_hom
    (fun _ : Unit => true)
    () (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => ())
    true (fun left right => left && right)
    (fun _ _ => true) (fun _ _ => true) (fun _ _ => true)
    rfl (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) target
  exact folded.symm

theorem projectGroundNormalForm_isACUIh
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const (Fin 0) Hom) :
    isACUIh (projectGroundNormalForm left right assignment target) = true := by
  have folded := NormalForm.fold_hom
    (fun result : NormalForm Const (Fin 0) Hom ×
        NormalForm (ECombinationBasis left right) (Fin 0) Hom =>
      isACUIh result.2)
    (∅, ∅)
    (fun first second => (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      let original : NormalForm Const (Fin 0) Hom :=
        {(path, .eOperator body.1)}
      let projected : NormalForm
          (ECombinationBasis left right) (Fin 0) Hom :=
        match representativeForBody? left right assignment body.1 with
        | none => ∅
        | some representative => {(path, .constant (.inr representative))}
      (original, projected))
    true (fun first second => first && second)
    (fun _ _ => true) (fun _ _ => true) (fun _ _ => true)
    (by simp)
    (by intro first second; simp)
    (by intro path name; apply normalSingletonConstant_isACUIh)
    (by intro path impossible; exact impossible.elim0)
    (by
      intro path body
      dsimp only
      cases representativeForBody? left right assignment body.1 <;>
        simp [normalSingletonConstant_isACUIh])
    target
  unfold projectGroundNormalForm
  exact folded.trans (foldAllTrue target)

theorem canonicalize_eq_self_of_isACUIh_fin_zero
    {Const Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Hom] [Encodable Hom]
    (target : NormalForm Const (Fin 0) Hom)
    (acuih : isACUIh target = true) :
    canonicalize target = target := by
  have canonicalACUIh : isACUIh (canonicalize target) = true := by
    apply isACUIh_normalize
    exact reify_isACUIh target acuih
  have targetGround := isGround_of_isACUIh_fin_zero target acuih
  have canonicalGround :=
    isGround_of_isACUIh_fin_zero (canonicalize target) canonicalACUIh
  have canonicalBelowTarget : Below (Hom := Hom) (canonicalize target) target :=
    ((isSolvedInequality_iff_constantCoefficient_le
      (canonicalize target) target Finset.univ canonicalACUIh (by simp)).mpr
      ⟨canonicalGround, targetGround, by
        intro constant
        rw [constantCoefficient_canonicalize]⟩).2.2
  have targetBelowCanonical : Below (Hom := Hom) target (canonicalize target) :=
    ((isSolvedInequality_iff_constantCoefficient_le
      target (canonicalize target) Finset.univ acuih (by simp)).mpr
      ⟨targetGround, canonicalGround, by
        intro constant
        rw [constantCoefficient_canonicalize]⟩).2.2
  calc
    canonicalize target = target + canonicalize target := targetBelowCanonical.symm
    _ = canonicalize target + target := by
      apply NormalForm.ext_raw
      exact rawUnion_comm target.raw (canonicalize target).raw
    _ = target := canonicalBelowTarget

theorem projectGroundNormalForm_canonical
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const (Fin 0) Hom) :
    canonicalize (projectGroundNormalForm left right assignment target) =
      projectGroundNormalForm left right assignment target :=
  canonicalize_eq_self_of_isACUIh_fin_zero _
    (projectGroundNormalForm_isACUIh left right assignment target)

theorem classOfBody?_projected
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (body : NormalForm Const Var Hom)
    {occurrence : EOccurrence left right}
    (found : findEOccurrence? left right body = some occurrence) :
    classOfBody? left right (projectedEConfiguration left right assignment)
        body =
      if applyGroundAssignment assignment body = ∅ then
        none
      else
        representativeForBody? left right assignment
          (applyGroundAssignment assignment body) := by
  unfold classOfBody?
  rw [found]
  change projectedOccurrenceClass left right assignment occurrence = _
  unfold projectedOccurrenceClass occurrenceBodyValue EOccurrence.body
  have bodyEquality : occurrence.1 = body := by
    unfold findEOccurrence? at found
    exact of_decide_eq_true (List.find?_some
      (p := fun candidate : EOccurrence left right => candidate.body = body)
      found)
  rw [bodyEquality]

@[simp]
theorem projectGroundNormalForm_constantForm
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (name : Const) :
    projectGroundNormalForm left right assignment
        (constantForm (Var := Fin 0) (Hom := Hom) name) =
      constantForm (Var := Fin 0) (Hom := Hom)
        (Sum.inl name : ECombinationBasis left right) := by
  unfold projectGroundNormalForm projectGroundNormalFormPair constantForm
  rw [NormalForm.fold_singleton]
  simp [normalUnionEmpty]

@[simp]
theorem projectGroundNormalForm_empty
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom) :
    projectGroundNormalForm left right assignment ∅ = ∅ := by
  simp [projectGroundNormalForm, projectGroundNormalFormPair]

/-- Prefix an entire homomorphism path to a normal form. -/
def prefixHomPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (target : NormalForm Const Var Hom) :
    NormalForm Const Var Hom :=
  path.foldr prefixHom target

theorem normalize_substitute_reifyPath
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar]
    [Encodable Hom]
    (substitution : SourceVar → Term Const TargetVar Hom)
    (path : List Hom) (term : Term Const SourceVar Hom) :
    normalize (Term.substitute substitution (reifyPath path term)) =
      prefixHomPath path (normalize (Term.substitute substitution term)) := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      simp only [reifyPath, List.foldr_cons, Term.substitute_hom,
        normalize_hom, prefixHomPath]
      exact congrArg (prefixHom name) inductionHypothesis

/-- Direct evaluation of an intrinsic normal form by its recursive fold. -/
def evaluateNormalForm
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) : NormalForm Const (Fin 0) Hom :=
  target.fold ∅ (· ∪ ·)
    (fun path name => prefixHomPath (Const := Const) (Var := Fin 0)
      (Hom := Hom) path
      (constantForm (Var := Fin 0) (Hom := Hom) name))
    (fun path name => prefixHomPath (Const := Const) (Var := Fin 0)
      (Hom := Hom) path (canonicalize (assignment name)))
    (fun path body => prefixHomPath (Const := Const) (Var := Fin 0)
      (Hom := Hom) path
      (wrapE (Const := Const) (Var := Fin 0) (Hom := Hom) body))

/-- The direct fold evaluator is exactly normal-form substitution. -/
theorem evaluateNormalForm_eq_applyGroundAssignment
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) :
    evaluateNormalForm assignment target =
      applyGroundAssignment assignment target := by
  unfold evaluateNormalForm applyGroundAssignment substituteNormalForm induce
  change NormalForm.fold
      (∅ : NormalForm Const (Fin 0) Hom) (· ∪ ·)
      (fun path name => prefixHomPath (Const := Const) (Var := Fin 0)
        (Hom := Hom) path
        (constantForm (Var := Fin 0) (Hom := Hom) name))
      (fun path name => prefixHomPath (Const := Const) (Var := Fin 0)
        (Hom := Hom) path (canonicalize (assignment name)))
      (fun path body => prefixHomPath (Const := Const) (Var := Fin 0)
        (Hom := Hom) path
        (wrapE (Const := Const) (Var := Fin 0) (Hom := Hom) body)) target =
    normalize
      (Term.substitute (fun name => reify (assignment name))
        (reify target))
  symm
  unfold reify
  apply NormalForm.fold_hom
    (fun term : Term Const Var Hom =>
      normalize
        (Term.substitute (fun name => reify (assignment name)) term))
    (.zero : Term Const Var Hom) (.add)
    (fun path name => reifyPath path (.const name))
    (fun path name => reifyPath path (.var name))
    (fun path body => reifyPath path (.free body))
    (∅ : NormalForm Const (Fin 0) Hom) (· ∪ ·)
    (fun path name => prefixHomPath (Const := Const) (Var := Fin 0)
      (Hom := Hom) path
      (constantForm (Var := Fin 0) (Hom := Hom) name))
    (fun path name => prefixHomPath (Const := Const) (Var := Fin 0)
      (Hom := Hom) path (canonicalize (assignment name)))
    (fun path body => prefixHomPath (Const := Const) (Var := Fin 0)
      (Hom := Hom) path
      (wrapE (Const := Const) (Var := Fin 0) (Hom := Hom) body))
    (by rfl)
    (by intro leftTerm rightTerm; simp [normalize_add])
    (by
      intro path name
      rw [normalize_substitute_reifyPath]
      rfl)
    (by
      intro path name
      rw [normalize_substitute_reifyPath]
      rfl)
    (by
      intro path body
      rw [normalize_substitute_reifyPath]
      rfl)
    target

@[simp]
theorem prefixHomPath_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) :
    prefixHomPath (Const := Const) (Var := Var) path ∅ = ∅ := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      change prefixHom name (prefixHomPath path ∅) = ∅
      rw [inductionHypothesis, prefixHom_empty]

theorem prefixHomPath_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (first second : NormalForm Const Var Hom) :
    prefixHomPath path (first ∪ second) =
      prefixHomPath path first ∪ prefixHomPath path second := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      change prefixHom name (prefixHomPath path (first ∪ second)) = _
      rw [inductionHypothesis, prefixHom_union]
      rfl

@[simp]
theorem prefixHomPath_singleton
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (atom : NormalAtom Const Var Hom) :
    prefixHomPath path ({([], atom)} : NormalForm Const Var Hom) =
      {(path, atom)} := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      change prefixHom name
          (prefixHomPath path ({([], atom)} : NormalForm Const Var Hom)) = _
      rw [inductionHypothesis, prefixHom_singleton]

/-- A semantic summand survives prefixing, with the prefix concatenated to
its homomorphism path. -/
theorem mem_prefixHomPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (prefixPath : List Hom) (target : NormalForm Const Var Hom)
    (path : List Hom) (atom : RawNormalAtom Const Var Hom)
    (membership : (path, atom) ∈ RecursiveFinset.toFinset target.raw) :
    (prefixPath ++ path, atom) ∈
      RecursiveFinset.toFinset (prefixHomPath prefixPath target).raw := by
  induction prefixPath with
  | nil =>
      change (path, atom) ∈ RecursiveFinset.toFinset target.raw
      exact membership
  | cons name tailPath inductionHypothesis =>
      change (name :: tailPath ++ path, atom) ∈
        RecursiveFinset.toFinset
          (prefixHom name (prefixHomPath tailPath target)).raw
      change (name :: tailPath ++ path, atom) ∈
        RecursiveFinset.toFinset
          (RecursiveFinset.image
            (fun summand : RawNormalSummand Const Var Hom =>
              (name :: summand.1, summand.2))
            (prefixHomPath tailPath target).raw)
      rw [RecursiveFinset.toFinset_image _
        (prefixHomPath tailPath target).valid.outer]
      exact Finset.mem_image.mpr
        ⟨(tailPath ++ path, atom), inductionHypothesis, rfl⟩

theorem projectGroundNormalForm_prefixHomPath
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (path : List Hom) (target : NormalForm Const (Fin 0) Hom) :
    projectGroundNormalForm left right assignment
        (prefixHomPath path target) =
      prefixHomPath (Const := ECombinationBasis left right) (Var := Fin 0) path
        (projectGroundNormalForm left right assignment target) := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      change projectGroundNormalForm left right assignment
          (prefixHom name (prefixHomPath path target)) = _
      rw [projectGroundNormalForm_prefixHom, inductionHypothesis]
      rfl

@[simp]
theorem evaluateNormalForm_empty
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom) :
    evaluateNormalForm assignment (∅ : NormalForm Const Var Hom) = ∅ := by
  simp [evaluateNormalForm]

theorem evaluateNormalForm_union
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (first second : NormalForm Const Var Hom) :
    evaluateNormalForm assignment (first ∪ second) =
      evaluateNormalForm assignment first ∪
        evaluateNormalForm assignment second := by
  unfold evaluateNormalForm
  apply NormalForm.fold_union
  exact normalUnionEmpty

@[simp]
theorem evaluateNormalForm_singleton_constant
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (path : List Hom) (name : Const) :
    evaluateNormalForm assignment
        ({(path, .constant name)} : NormalForm Const Var Hom) =
      prefixHomPath path
        (constantForm (Var := Fin 0) (Hom := Hom) name) := by
  unfold evaluateNormalForm
  rw [NormalForm.fold_singleton]
  exact normalUnionEmpty _

@[simp]
theorem evaluateNormalForm_singleton_variable
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (path : List Hom) (name : Var) :
    evaluateNormalForm assignment
        ({(path, .variable name)} : NormalForm Const Var Hom) =
      prefixHomPath path (canonicalize (assignment name)) := by
  unfold evaluateNormalForm
  rw [NormalForm.fold_singleton]
  exact normalUnionEmpty _

@[simp]
theorem evaluateNormalForm_singleton_eOperator
    {Const Var Hom : Type u}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (path : List Hom) (body : NormalForm Const Var Hom) :
    evaluateNormalForm assignment
        ({(path, .eOperator body)} : NormalForm Const Var Hom) =
      prefixHomPath path (wrapE (evaluateNormalForm assignment body)) := by
  unfold evaluateNormalForm
  rw [NormalForm.fold_singleton]
  exact normalUnionEmpty _

/-! ## Address-free projection invariant -/

/-- Proof state computed in the same fold as purification.  Unlike the old
syntax-path argument, the only side condition is inclusion of the finite set
of bodies actually encountered by the fold. -/
structure ProjectionProofScan
    (Const Var Hom : Type u)
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom) where
  source : NormalForm Const Var Hom
  bodies : Finset (NormalForm Const Var Hom)
  purified : NormalForm (ECombinationBasis left right) Var Hom
  commutes : bodies ⊆ allEBodySet left right →
    projectGroundNormalForm left right assignment
        (evaluateNormalForm assignment source) =
      evaluateNormalForm (projectedAssignment left right assignment) purified
  dependencies : ∀ selected : EOccurrence left right,
    Sum.inr selected ∈ constantSupport purified →
      ∃ path,
        (path, RawNormalAtom.eOperator
            (occurrenceBodyValue left right assignment selected).raw) ∈
          RecursiveFinset.toFinset
            (evaluateNormalForm assignment source).raw
  variableDependencies : ∀ (name : Var) (selected : EOccurrence left right),
    name ∈ variableSupport purified →
      (∃ assignmentPath,
        (assignmentPath, RawNormalAtom.eOperator
            (occurrenceBodyValue left right assignment selected).raw) ∈
          RecursiveFinset.toFinset (canonicalize (assignment name)).raw) →
      ∃ path,
        (path, RawNormalAtom.eOperator
            (occurrenceBodyValue left right assignment selected).raw) ∈
          RecursiveFinset.toFinset
            (evaluateNormalForm assignment source).raw

private def projectionProofZero
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom) :
    ProjectionProofScan Const Var Hom left right assignment :=
  ⟨∅, ∅, ∅, by simp,
    by intro selected membership; simp at membership,
    by intro name selected membership; simp at membership⟩

private def projectionProofCombine
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (first second : ProjectionProofScan Const Var Hom left right assignment) :
    ProjectionProofScan Const Var Hom left right assignment :=
  ⟨first.source ∪ second.source,
    first.bodies ∪ second.bodies,
    first.purified ∪ second.purified,
    by
      intro included
      have firstIncluded : first.bodies ⊆ allEBodySet left right :=
        Finset.Subset.trans Finset.subset_union_left included
      have secondIncluded : second.bodies ⊆ allEBodySet left right :=
        Finset.Subset.trans Finset.subset_union_right included
      rw [evaluateNormalForm_union, projectGroundNormalForm_union,
        evaluateNormalForm_union, first.commutes firstIncluded,
        second.commutes secondIncluded],
    by
      intro selected membership
      rw [constantSupport_union] at membership
      simp only [Finset.mem_union] at membership
      rcases membership with membership | membership
      · rcases first.dependencies selected membership with
          ⟨path, pathMembership⟩
        refine ⟨path, ?_⟩
        rw [evaluateNormalForm_union]
        change _ ∈ RecursiveFinset.toFinset
          ((evaluateNormalForm assignment first.source).raw ∪
            (evaluateNormalForm assignment second.source).raw)
        rw [RecursiveFinset.toFinset_union]
        exact Finset.mem_union_left _ pathMembership
      · rcases second.dependencies selected membership with
          ⟨path, pathMembership⟩
        refine ⟨path, ?_⟩
        rw [evaluateNormalForm_union]
        change _ ∈ RecursiveFinset.toFinset
          ((evaluateNormalForm assignment first.source).raw ∪
            (evaluateNormalForm assignment second.source).raw)
        rw [RecursiveFinset.toFinset_union]
        exact Finset.mem_union_right _ pathMembership,
    by
      intro name selected variableMembership assignmentMembership
      rw [variableSupport_union] at variableMembership
      simp only [Finset.mem_union] at variableMembership
      rcases variableMembership with variableMembership | variableMembership
      · rcases first.variableDependencies name selected variableMembership
            assignmentMembership with ⟨path, pathMembership⟩
        refine ⟨path, ?_⟩
        rw [evaluateNormalForm_union]
        change _ ∈ RecursiveFinset.toFinset
          ((evaluateNormalForm assignment first.source).raw ∪
            (evaluateNormalForm assignment second.source).raw)
        rw [RecursiveFinset.toFinset_union]
        exact Finset.mem_union_left _ pathMembership
      · rcases second.variableDependencies name selected variableMembership
            assignmentMembership with ⟨path, pathMembership⟩
        refine ⟨path, ?_⟩
        rw [evaluateNormalForm_union]
        change _ ∈ RecursiveFinset.toFinset
          ((evaluateNormalForm assignment first.source).raw ∪
            (evaluateNormalForm assignment second.source).raw)
        rw [RecursiveFinset.toFinset_union]
        exact Finset.mem_union_right _ pathMembership⟩

private def projectionProofConstant
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (path : List Hom) (name : Const) :
    ProjectionProofScan Const Var Hom left right assignment :=
  ⟨{(path, .constant name)}, ∅,
    {(path, .constant (.inl name))},
        by
          intro _
          rw [evaluateNormalForm_singleton_constant,
            projectGroundNormalForm_prefixHomPath,
            projectGroundNormalForm_constantForm,
            evaluateNormalForm_singleton_constant],
        by
          intro selected membership
          unfold constantSupport at membership
          rw [NormalForm.fold_singleton] at membership
          simp at membership,
        by
          intro variableName selected membership
          unfold variableSupport at membership
          rw [NormalForm.fold_singleton] at membership
          simp at membership⟩

private def projectionProofVariable
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (path : List Hom) (name : Var) :
    ProjectionProofScan Const Var Hom left right assignment :=
  ⟨{(path, .variable name)}, ∅,
    {(path, .variable name)},
    by
      intro _
      rw [evaluateNormalForm_singleton_variable,
        projectGroundNormalForm_prefixHomPath,
        evaluateNormalForm_singleton_variable]
      unfold projectedAssignment
      rw [projectGroundNormalForm_canonical],
    by
      intro selected membership
      unfold constantSupport at membership
      rw [NormalForm.fold_singleton] at membership
      simp at membership,
    by
      intro selectedName selected variableMembership assignmentMembership
      unfold variableSupport at variableMembership
      rw [NormalForm.fold_singleton] at variableMembership
      simp only [Finset.union_empty, Finset.mem_singleton] at variableMembership
      subst selectedName
      rcases assignmentMembership with ⟨assignmentPath, assignmentMembership⟩
      refine ⟨path ++ assignmentPath, ?_⟩
      rw [evaluateNormalForm_singleton_variable]
      exact mem_prefixHomPath path (canonicalize (assignment name))
        assignmentPath _ assignmentMembership⟩

private def projectionProofEOperator
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (path : List Hom)
    (body : ProjectionProofScan Const Var Hom left right assignment) :
    ProjectionProofScan Const Var Hom left right assignment :=
  let purified : NormalForm (ECombinationBasis left right) Var Hom :=
    match classOfBody? left right
        (projectedEConfiguration left right assignment) body.source with
    | none => ∅
    | some representative =>
        {(path, .constant (.inr representative))}
  ⟨{(path, .eOperator body.source)},
    insert body.source body.bodies,
    purified,
    by
      intro included
      have bodyMembership : body.source ∈ allEBodies left right :=
        mem_allEBodies_iff.mpr
          (included (Finset.mem_insert_self _ _))
      rcases findEOccurrence?_of_mem left right body.source bodyMembership with
        ⟨occurrence, found, _⟩
      have classEquality := classOfBody?_projected
        left right assignment body.source found
      rw [← evaluateNormalForm_eq_applyGroundAssignment assignment body.source]
        at classEquality
      have opaqueProjection :
          projectGroundNormalForm left right assignment
              (wrapE (evaluateNormalForm assignment body.source)) =
            match classOfBody? left right
                (projectedEConfiguration left right assignment)
                body.source with
            | none => ∅
            | some representative =>
                constantForm (Var := Fin 0) (Hom := Hom)
                  (Sum.inr representative) := by
        rw [projectGroundNormalForm_wrapE, classEquality]
        by_cases bodyZero : evaluateNormalForm assignment body.source = ∅
        · simp [bodyZero]
        · simp only [if_neg bodyZero]
          cases representativeForBody? left right assignment
              (evaluateNormalForm assignment body.source) <;>
            simp [constantForm]
      rw [evaluateNormalForm_singleton_eOperator,
        projectGroundNormalForm_prefixHomPath, opaqueProjection]
      cases classResult : classOfBody? left right
          (projectedEConfiguration left right assignment) body.source <;>
        simp [purified, classResult],
    by
      intro selected membership
      cases classResult : classOfBody? left right
          (projectedEConfiguration left right assignment) body.source with
      | none =>
          simp [purified, classResult] at membership
      | some representative =>
          have representativeEquality : representative = selected := by
            unfold constantSupport at membership
            simp only [purified, classResult] at membership
            rw [NormalForm.fold_singleton] at membership
            have reverseEquality : selected = representative := by
              simpa using membership
            exact reverseEquality.symm
          subst representative
          unfold classOfBody? at classResult
          cases found : findEOccurrence? left right body.source with
          | none => simp [found] at classResult
          | some occurrence =>
              simp only [found, Option.bind_some] at classResult
              change projectedOccurrenceClass left right assignment occurrence =
                some selected at classResult
              have occurrenceBodyEquality : occurrence.body = body.source := by
                unfold findEOccurrence? at found
                exact of_decide_eq_true (List.find?_some
                  (p := fun candidate : EOccurrence left right =>
                    candidate.body = body.source) found)
              have valueEquality := projectedOccurrenceClass_some_value
                left right assignment classResult
              have valueNonzero := projectedOccurrenceClass_some_nonzero
                left right assignment classResult
              have evaluatedEquality :
                  evaluateNormalForm assignment body.source =
                    occurrenceBodyValue left right assignment selected := by
                rw [evaluateNormalForm_eq_applyGroundAssignment]
                unfold occurrenceBodyValue at valueEquality ⊢
                rw [occurrenceBodyEquality] at valueEquality
                exact valueEquality.symm
              have evaluatedNonzero :
                  evaluateNormalForm assignment body.source ≠ ∅ := by
                rw [evaluateNormalForm_eq_applyGroundAssignment]
                intro bodyZero
                apply valueNonzero
                unfold occurrenceBodyValue
                rw [occurrenceBodyEquality]
                exact bodyZero
              refine ⟨path, ?_⟩
              rw [evaluateNormalForm_singleton_eOperator,
                wrapE_of_ne_empty evaluatedNonzero,
                prefixHomPath_singleton, evaluatedEquality]
              change (path, RawNormalAtom.eOperator
                  (occurrenceBodyValue left right assignment selected).raw) ∈
                RecursiveFinset.toFinset
                  ({(path, RawNormalAtom.eOperator
                    (occurrenceBodyValue left right assignment selected).raw)} :
                    RawNormalForm Const (Fin 0) Hom)
              simp,
    by
      intro name selected membership
      cases classResult : classOfBody? left right
          (projectedEConfiguration left right assignment) body.source <;>
        simp [purified, classResult, variableSupport] at membership⟩

/-- Compute purification and its projection proof together. -/
def projectionProofScan
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) :
    ProjectionProofScan Const Var Hom left right assignment :=
  target.fold
    (projectionProofZero left right assignment)
    (projectionProofCombine left right assignment)
    (projectionProofConstant left right assignment)
    (projectionProofVariable left right assignment)
    (projectionProofEOperator left right assignment)

@[simp]
theorem projectionProofScan_source
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) :
    (projectionProofScan left right assignment target).source = target := by
  unfold projectionProofScan
  have mapped := NormalForm.fold_hom
    (fun result : ProjectionProofScan Const Var Hom left right assignment =>
      result.source)
    (projectionProofZero left right assignment)
    (projectionProofCombine left right assignment)
    (projectionProofConstant left right assignment)
    (projectionProofVariable left right assignment)
    (projectionProofEOperator left right assignment)
    (∅ : NormalForm Const Var Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    (by rfl)
    (by intro first second; rfl)
    (by intro path name; rfl)
    (by intro path name; rfl)
    (by intro path body; rfl)
    target
  exact mapped.trans (rebuildNormalForm_eq target)

theorem projectionProofScan_bodies
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) :
    (projectionProofScan left right assignment target).bodies =
      (scanEBodySet target).2 := by
  unfold projectionProofScan scanEBodySet
  have mapped := NormalForm.fold_hom
    (fun result : ProjectionProofScan Const Var Hom left right assignment =>
      (result.source, result.bodies))
    (projectionProofZero left right assignment)
    (projectionProofCombine left right assignment)
    (projectionProofConstant left right assignment)
    (projectionProofVariable left right assignment)
    (projectionProofEOperator left right assignment)
    (∅, ∅)
    (fun first second => (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name => ({(path, .constant name)}, ∅))
    (fun path name => ({(path, .variable name)}, ∅))
    (fun path body =>
      ({(path, .eOperator body.1)}, insert body.1 body.2))
    (by rfl)
    (by intro first second; rfl)
    (by intro path name; rfl)
    (by intro path name; rfl)
    (by intro path body; rfl)
    target
  exact congrArg Prod.snd mapped

def purificationPairEOperator
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (path : List Hom)
    (body : NormalForm Const Var Hom ×
      NormalForm (ECombinationBasis left right) Var Hom) :
    NormalForm Const Var Hom ×
      NormalForm (ECombinationBasis left right) Var Hom :=
  let purified : NormalForm (ECombinationBasis left right) Var Hom :=
    match classOfBody? left right configuration body.1 with
    | none => ∅
    | some representative =>
        {(path, .constant (.inr representative))}
  ({(path, .eOperator body.1)}, purified)

def purificationPair
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (target : NormalForm Const Var Hom) :
    NormalForm Const Var Hom ×
      NormalForm (ECombinationBasis left right) Var Hom :=
  target.fold
    (∅, ∅)
    (fun first second =>
      (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun path name =>
      ({(path, .variable name)}, {(path, .variable name)}))
    (purificationPairEOperator left right configuration)

private theorem projectionProofScan_pair
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) :
    let result := projectionProofScan left right assignment target
    (result.source, result.purified) =
      purificationPair left right
        (projectedEConfiguration left right assignment) target := by
  dsimp only
  unfold projectionProofScan purificationPair
  exact NormalForm.fold_hom
    (fun result : ProjectionProofScan Const Var Hom left right assignment =>
      (result.source, result.purified))
    (projectionProofZero left right assignment)
    (projectionProofCombine left right assignment)
    (projectionProofConstant left right assignment)
    (projectionProofVariable left right assignment)
    (projectionProofEOperator left right assignment)
    (∅, ∅)
    (fun first second =>
      (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun path name =>
      ({(path, .variable name)}, {(path, .variable name)}))
    (fun path body =>
      let purified : NormalForm (ECombinationBasis left right) Var Hom :=
        match classOfBody? left right
            (projectedEConfiguration left right assignment) body.1 with
        | none => ∅
        | some representative =>
            {(path, .constant (.inr representative))}
      ({(path, .eOperator body.1)}, purified))
    (by rfl)
    (by intro first second; rfl)
    (by intro path name; rfl)
    (by intro path name; rfl)
    (by intro path body; rfl)
    target

theorem purifyNormalFormScan_pair
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (target : NormalForm Const Var Hom) :
    let result := purifyNormalFormScan left right configuration target
    (result.source, result.purified) =
      purificationPair left right configuration target := by
  dsimp only
  unfold purifyNormalFormScan purificationPair
  exact NormalForm.fold_hom
    (fun result : EPurificationScan Const Var Hom
        (ECombinationBasis left right) =>
      (result.source, result.purified))
    ⟨∅, ∅, isACUIh_empty⟩
    (fun first second =>
      ⟨first.source ∪ second.source,
        first.purified ∪ second.purified,
        by simp [first.acuih, second.acuih]⟩)
    (fun path name =>
      ⟨{(path, .constant name)},
        {(path, .constant (.inl name))}, by simp [isACUIh]⟩)
    (fun path name =>
      ⟨{(path, .variable name)},
        {(path, .variable name)}, by simp [isACUIh]⟩)
    (fun path body =>
      let purified : NormalForm (ECombinationBasis left right) Var Hom :=
        match classOfBody? left right configuration body.source with
        | none => ∅
        | some representative =>
            {(path, .constant (.inr representative))}
      ⟨{(path, .eOperator body.source)}, purified, by
        simp only [purified]
        split <;> simp [isACUIh]⟩)
    (∅, ∅)
    (fun first second =>
      (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun path name =>
      ({(path, .variable name)}, {(path, .variable name)}))
    (fun path body =>
      let purified : NormalForm (ECombinationBasis left right) Var Hom :=
        match classOfBody? left right configuration body.1 with
        | none => ∅
        | some representative =>
            {(path, .constant (.inr representative))}
      ({(path, .eOperator body.1)}, purified))
    (by rfl)
    (by intro first second; rfl)
    (by intro path name; rfl)
    (by intro path name; rfl)
    (by intro path body; rfl)
    target

theorem projectionProofScan_purified
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom) :
    (projectionProofScan left right assignment target).purified =
      purifyNormalForm left right
        (projectedEConfiguration left right assignment) target := by
  have proofPair := projectionProofScan_pair left right assignment target
  have executablePair := purifyNormalFormScan_pair left right
    (projectedEConfiguration left right assignment) target
  unfold purifyNormalForm
  exact (congrArg Prod.snd proofPair).trans
    (congrArg Prod.snd executablePair).symm

/-- Projection commutes with evaluating any normal form whose recursively
occurring `E` bodies belong to the finite input table. -/
theorem project_applyGroundAssignment_eq_purify
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom)
    (included : (scanEBodySet target).2 ⊆ allEBodySet left right) :
    projectGroundNormalForm left right assignment
        (applyGroundAssignment assignment target) =
      applyGroundAssignment (projectedAssignment left right assignment)
        (purifyNormalForm left right
          (projectedEConfiguration left right assignment) target) := by
  let result := projectionProofScan left right assignment target
  have commutes := result.commutes
  have bodyInclusion : result.bodies ⊆ allEBodySet left right := by
    rw [projectionProofScan_bodies left right assignment target]
    exact included
  specialize commutes bodyInclusion
  rw [projectionProofScan_source left right assignment target,
    projectionProofScan_purified left right assignment target,
    evaluateNormalForm_eq_applyGroundAssignment,
    evaluateNormalForm_eq_applyGroundAssignment] at commutes
  exact commutes

theorem project_applyGroundAssignment_side
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (side : Bool) :
    projectGroundNormalForm left right assignment
        (applyGroundAssignment assignment (if side then right else left)) =
      applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedSide left right
          (projectedEConfiguration left right assignment) side) := by
  unfold purifiedSide
  cases side with
  | false =>
      apply project_applyGroundAssignment_eq_purify
      exact Finset.subset_union_left
  | true =>
      apply project_applyGroundAssignment_eq_purify
      exact Finset.subset_union_right

theorem project_occurrenceBodyValue
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right) :
    projectGroundNormalForm left right assignment
        (occurrenceBodyValue left right assignment occurrence) =
      applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedOccurrenceBody left right
          (projectedEConfiguration left right assignment) occurrence) := by
  unfold occurrenceBodyValue purifiedOccurrenceBody
  apply project_applyGroundAssignment_eq_purify
  intro nested membership
  exact mem_allEBodies_iff.mp
    (occurrence.nested_mem_allEBodies membership)

/-- Reified purified bodies are merely the term presentation of the direct
normal-form purification used by the executable matrix rows. -/
theorem applyGroundAssignment_purifiedOccurrenceBody
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (assignment : Var →
      NormalForm (ECombinationBasis left right) (Fin 0) Hom)
    (occurrence : EOccurrence left right) :
    applyGroundAssignment assignment
        (purifiedOccurrenceBody left right configuration occurrence) =
      normalize
        (Term.substitute (fun name => reify (assignment name))
          (reify
            (purifiedOccurrenceBody left right configuration occurrence))) := by
  rfl

theorem evaluate_fullMatrixRepresentation_projectedAssignment
    {Row Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (terms : Row → Term (ECombinationBasis left right) Var Hom)
    (acuih : ∀ row, (terms row).IsACUIh)
    (row : Row) (basis : ECombinationBasis left right) :
    evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun row => normalize (terms row)))
        (projectedAssignmentMatrix left right assignment) row basis =
      constantCoefficient
        (normalize
          (Term.substitute
            (fun name => reify (projectedAssignment left right assignment name))
            (terms row))) basis := by
  rw [constantCoefficient_normalize_substitute_acuih _ _ (acuih row)]
  change
    (∑ name : Var,
        variableCoefficient (normalize (terms row)) name *
          constantCoefficient
            (projectedAssignment left right assignment name) basis) +
        constantCoefficient (normalize (terms row)) basis =
      (∑ name : Var,
        variableCoefficient (normalize (terms row)) name *
          constantCoefficient
            (canonicalize
              (projectedAssignment left right assignment name)) basis) +
        constantCoefficient (normalize (terms row)) basis
  simp only [constantCoefficient_canonicalize]

theorem projectedAssignmentMatrix_outer_row
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (solved : IsSolvedInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right))
    (basis : ECombinationBasis left right) :
    evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right
          (projectedEConfiguration left right assignment) basis).1
        (projectedAssignmentMatrix left right assignment) (.inl ()) basis ≤
      evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right
          (projectedEConfiguration left right assignment) basis).2
        (projectedAssignmentMatrix left right assignment) (.inl ()) basis := by
  let configuration := projectedEConfiguration left right assignment
  have projectedBelow : Below (Hom := Hom)
      (projectGroundNormalForm left right assignment
        (applyGroundAssignment assignment left))
      (projectGroundNormalForm left right assignment
        (applyGroundAssignment assignment right)) := by
    have originalBelow := solved.2.2
    change applyGroundAssignment assignment left ∪
        applyGroundAssignment assignment right =
      applyGroundAssignment assignment right at originalBelow
    change projectGroundNormalForm left right assignment
          (applyGroundAssignment assignment left) ∪
        projectGroundNormalForm left right assignment
          (applyGroundAssignment assignment right) =
      projectGroundNormalForm left right assignment
        (applyGroundAssignment assignment right)
    rw [← projectGroundNormalForm_union, originalBelow]
  have abstractBelow : Below (Hom := Hom)
      (applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedSide left right configuration false))
      (applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedSide left right configuration true)) := by
    rw [← project_applyGroundAssignment_side left right assignment false,
      ← project_applyGroundAssignment_side left right assignment true]
    exact projectedBelow
  change evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationColumnLeftTerm left right configuration basis row)))
      (projectedAssignmentMatrix left right assignment) (.inl ()) basis ≤
    evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationRightTerm left right configuration row)))
      (projectedAssignmentMatrix left right assignment) (.inl ()) basis
  rw [evaluate_fullMatrixRepresentation_projectedAssignment
      left right assignment
      (eCombinationColumnLeftTerm left right configuration basis)
      (eCombinationColumnLeftTerm_isACUIh left right configuration basis)
      (.inl ()) basis,
    evaluate_fullMatrixRepresentation_projectedAssignment
      left right assignment
      (eCombinationRightTerm left right configuration)
      (eCombinationRightTerm_isACUIh left right configuration) (.inl ()) basis]
  have leftACUIh : isACUIh
      (applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedSide left right configuration false)) = true := by
    apply isACUIh_normalize
    apply isACUIh_substitute
    · intro name
      apply reify_isACUIh
      exact projectGroundNormalForm_isACUIh left right assignment _
    · apply reify_isACUIh
      unfold purifiedSide
      simp [purifyNormalForm_isACUIh left right configuration left]
  have solvedAbstract : IsSolvedInequality
      (applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedSide left right configuration false))
      (applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedSide left right configuration true)) := by
    refine ⟨isGround_of_isACUIh_fin_zero _ leftACUIh, ?_, abstractBelow⟩
    have rightACUIh : isACUIh
        (applyGroundAssignment (projectedAssignment left right assignment)
          (purifiedSide left right configuration true)) = true := by
      apply isACUIh_normalize
      apply isACUIh_substitute
      · intro name
        apply reify_isACUIh
        exact projectGroundNormalForm_isACUIh left right assignment _
      · apply reify_isACUIh
        unfold purifiedSide
        simp [purifyNormalForm_isACUIh left right configuration right]
    exact isGround_of_isACUIh_fin_zero _ rightACUIh
  have coefficientBelow :=
    (isSolvedInequality_iff_constantCoefficient_le
      _ _ Finset.univ leftACUIh (by simp)).mp solvedAbstract
  have selected := coefficientBelow.2.2 ⟨basis, by simp⟩
  simpa [applyGroundAssignment, substituteNormalForm, induce,
    eCombinationColumnLeftTerm, eCombinationLeftTerm,
    eCombinationRightTerm, purifiedSide] using selected

theorem projected_purified_body_class
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right) :
    let configuration := projectedEConfiguration left right assignment
    applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedOccurrenceBody left right configuration occurrence) =
      match configuration.1 occurrence with
      | none => ∅
      | some representative =>
          applyGroundAssignment (projectedAssignment left right assignment)
            (purifiedOccurrenceBody left right configuration representative) := by
  dsimp only
  change applyGroundAssignment (projectedAssignment left right assignment)
        (purifiedOccurrenceBody left right
          (projectedEConfiguration left right assignment) occurrence) =
    match projectedOccurrenceClass left right assignment occurrence with
    | none => ∅
    | some representative =>
        applyGroundAssignment (projectedAssignment left right assignment)
          (purifiedOccurrenceBody left right
            (projectedEConfiguration left right assignment) representative)
  cases classResult : projectedOccurrenceClass left right assignment occurrence with
  | none =>
      simp only
      have valueZero := projectedOccurrenceClass_none_value
        left right assignment classResult
      rw [← project_occurrenceBodyValue left right assignment occurrence,
        valueZero, projectGroundNormalForm_empty]
  | some representative =>
      simp only
      have valueEquality := projectedOccurrenceClass_some_value
        left right assignment classResult
      rw [← project_occurrenceBodyValue left right assignment occurrence,
        ← project_occurrenceBodyValue left right assignment representative,
        valueEquality]

theorem projectedAssignmentMatrix_body_row
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (occurrence : EOccurrence left right) (direction : Bool)
    (basis : ECombinationBasis left right) :
    let configuration := projectedEConfiguration left right assignment
    evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right configuration basis).1
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inl (occurrence, direction))) basis ≤
      evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right configuration basis).2
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inl (occurrence, direction))) basis := by
  dsimp only
  let configuration := projectedEConfiguration left right assignment
  change evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationColumnLeftTerm left right configuration basis row)))
      (projectedAssignmentMatrix left right assignment)
      (.inr (.inl (occurrence, direction))) basis ≤
    evaluateMatrixRepresentation
      (fullMatrixRepresentation (fun row => normalize
        (eCombinationRightTerm left right configuration row)))
      (projectedAssignmentMatrix left right assignment)
      (.inr (.inl (occurrence, direction))) basis
  rw [evaluate_fullMatrixRepresentation_projectedAssignment
      left right assignment
      (eCombinationColumnLeftTerm left right configuration basis)
      (eCombinationColumnLeftTerm_isACUIh left right configuration basis)
      (.inr (.inl (occurrence, direction))) basis,
    evaluate_fullMatrixRepresentation_projectedAssignment
      left right assignment
      (eCombinationRightTerm left right configuration)
      (eCombinationRightTerm_isACUIh left right configuration)
      (.inr (.inl (occurrence, direction))) basis]
  have bodyClass := projected_purified_body_class
    left right assignment occurrence
  dsimp only at bodyClass
  cases direction with
  | false =>
      simp only [eCombinationColumnLeftTerm, eCombinationLeftTerm,
        eCombinationRightTerm]
      cases classResult : configuration.1 occurrence with
      | none =>
          rw [classResult] at bodyClass
          rw [← applyGroundAssignment_purifiedOccurrenceBody]
          rw [bodyClass]

          simp
      | some representative =>
          rw [classResult] at bodyClass
          rw [← applyGroundAssignment_purifiedOccurrenceBody,
            ← applyGroundAssignment_purifiedOccurrenceBody]
          rw [bodyClass]
  | true =>
      simp only [eCombinationColumnLeftTerm, eCombinationLeftTerm,
        eCombinationRightTerm]
      cases classResult : configuration.1 occurrence with
      | none =>
          rw [classResult] at bodyClass
          rw [← applyGroundAssignment_purifiedOccurrenceBody]
          rw [bodyClass]
          simp
      | some representative =>
          rw [classResult] at bodyClass
          rw [← applyGroundAssignment_purifiedOccurrenceBody,
            ← applyGroundAssignment_purifiedOccurrenceBody]
          rw [bodyClass]

theorem mem_constantSupport_projected_purify_gives_eAtom
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom)
    (selected : EOccurrence left right)
    (membership : Sum.inr selected ∈ constantSupport
      (purifyNormalForm left right
        (projectedEConfiguration left right assignment) target)) :
    ∃ path,
      (path, RawNormalAtom.eOperator
          (occurrenceBodyValue left right assignment selected).raw) ∈
        RecursiveFinset.toFinset
          (applyGroundAssignment assignment target).raw := by
  let result := projectionProofScan left right assignment target
  have purifiedMembership : Sum.inr selected ∈
      constantSupport result.purified := by
    rw [projectionProofScan_purified left right assignment target]
    exact membership
  rcases result.dependencies selected purifiedMembership with
    ⟨path, pathMembership⟩
  refine ⟨path, ?_⟩
  rw [projectionProofScan_source left right assignment target,
    evaluateNormalForm_eq_applyGroundAssignment] at pathMembership
  exact pathMembership

theorem rawNormalFormMeasure_lt_of_mem_eOperator
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (outer : NormalForm Const Var Hom) (path : List Hom)
    (body : RawNormalForm Const Var Hom)
    (membership : (path, RawNormalAtom.eOperator body) ∈
      RecursiveFinset.toFinset outer.raw) :
    rawNormalFormMeasure body < rawNormalFormMeasure outer.raw := by
  let summand : RawNormalSummand Const Var Hom :=
    (path, RawNormalAtom.eOperator body)
  have inEncoded : summand ∈
      RecursiveFinset.ofFinset (RecursiveFinset.toFinset outer.raw) := by
    change Encodable.encode summand ∈
      (RecursiveFinset.toFinset outer.raw).image Encodable.encode
    exact Finset.mem_image.mpr ⟨summand, membership, rfl⟩
  rw [outer.valid.outer] at inEncoded
  apply rawNormalFormMeasure_lt_of_decode_eOperator
    (code := Encodable.encode summand) (path := path)
  · exact inEncoded
  · exact Encodable.decode₂_encode summand

theorem projectedOccurrenceRank_lt_of_measure_lt
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    {smaller larger : EOccurrence left right}
    (measureLess : rawNormalFormMeasure
        (occurrenceBodyValue left right assignment smaller).raw <
      rawNormalFormMeasure
        (occurrenceBodyValue left right assignment larger).raw) :
    projectedOccurrenceRank left right assignment smaller <
      projectedOccurrenceRank left right assignment larger := by
  let occurrences := FinEnum.toList (EOccurrence left right)
  let smallSet := (occurrences.filter fun candidate =>
    rawNormalFormMeasure
        (occurrenceBodyValue left right assignment candidate).raw <
      rawNormalFormMeasure
        (occurrenceBodyValue left right assignment smaller).raw).toFinset
  let largeSet := (occurrences.filter fun candidate =>
    rawNormalFormMeasure
        (occurrenceBodyValue left right assignment candidate).raw <
      rawNormalFormMeasure
        (occurrenceBodyValue left right assignment larger).raw).toFinset
  have setSubset : smallSet ⊆ largeSet := by
    intro candidate membership
    simp only [smallSet, largeSet, List.mem_toFinset,
      List.mem_filter] at membership ⊢
    exact ⟨membership.1, decide_eq_true
      ((of_decide_eq_true membership.2).trans measureLess)⟩
  have smallerInLarge : smaller ∈ largeSet := by
    simp [largeSet, occurrences, measureLess]
  have smallerNotInSmall : smaller ∉ smallSet := by
    simp [smallSet, occurrences]
  have strictSubset : smallSet ⊂ largeSet := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨setSubset, ?_⟩
    intro equality
    exact smallerNotInSmall (equality.symm ▸ smallerInLarge)
  change
    (occurrences.filter fun candidate =>
      rawNormalFormMeasure
          (occurrenceBodyValue left right assignment candidate).raw <
        rawNormalFormMeasure
          (occurrenceBodyValue left right assignment smaller).raw).length <
    (occurrences.filter fun candidate =>
      rawNormalFormMeasure
          (occurrenceBodyValue left right assignment candidate).raw <
        rawNormalFormMeasure
          (occurrenceBodyValue left right assignment larger).raw).length
  rw [← List.toFinset_card_of_nodup
      (FinEnum.nodup_toList.filter _),
    ← List.toFinset_card_of_nodup
      (FinEnum.nodup_toList.filter _)]
  exact Finset.card_lt_card strictSubset

theorem EConfiguration.valid_of_properties
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (configuration : EConfiguration left right)
    (representativesFixed : ∀ occurrence representative,
      configuration.1 occurrence = some representative →
        configuration.1 representative = some representative)
    (dependenciesSmaller : ∀ representative basisOccurrence,
      configuration.1 representative = some representative →
      Sum.inr basisOccurrence ∈ constantSupport
        (purifiedOccurrenceBody left right configuration representative) →
      configuration.2 basisOccurrence < configuration.2 representative) :
    configuration.valid = true := by
  unfold EConfiguration.valid
  apply List.all_eq_true.mpr
  intro occurrence occurrenceMembership
  cases classResult : configuration.1 occurrence with
  | none => simp
  | some representative =>
      simp only
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true
        (representativesFixed occurrence representative classResult), ?_⟩
      apply List.all_eq_true.mpr
      intro basisOccurrence basisMembership
      exact decide_eq_true (dependenciesSmaller representative basisOccurrence
        (representativesFixed occurrence representative classResult))

theorem projectedEConfiguration_valid
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom) :
    (projectedEConfiguration left right assignment).valid = true := by
  apply EConfiguration.valid_of_properties left right
  · intro occurrence representative classResult
    exact projectedOccurrenceClass_representative
      left right assignment classResult
  · intro representative basisOccurrence representativeFixed supportMembership
    rcases mem_constantSupport_projected_purify_gives_eAtom
        left right assignment representative.body
        basisOccurrence (by
          unfold purifiedOccurrenceBody at supportMembership
          exact supportMembership) with
      ⟨path, eMembership⟩
    apply projectedOccurrenceRank_lt_of_measure_lt left right assignment
    exact rawNormalFormMeasure_lt_of_mem_eOperator
      (Const := Const) (Var := Fin 0) (Hom := Hom)
      (occurrenceBodyValue left right assignment representative)
      path (occurrenceBodyValue left right assignment basisOccurrence).raw
      eMembership

def projectedCoefficientPair
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (selected : EOccurrence left right)
    (target : NormalForm Const (Fin 0) Hom) :
    NormalForm Const (Fin 0) Hom × HomContext Hom :=
  target.fold
    (∅, 0)
    (fun first second => (first.1 ∪ second.1, first.2 + second.2))
    (fun path name => ({(path, .constant name)}, 0))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      ({(path, .eOperator body.1)},
        if representativeForBody? left right assignment body.1 = some selected
        then {path} else 0))

theorem projectedCoefficientPair_first
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (selected : EOccurrence left right)
    (target : NormalForm Const (Fin 0) Hom) :
    (projectedCoefficientPair left right assignment selected target).1 =
      target := by
  have folded := NormalForm.fold_hom
    (fun result : NormalForm Const (Fin 0) Hom × HomContext Hom => result.1)
    (∅, 0)
    (fun first second => (first.1 ∪ second.1, first.2 + second.2))
    (fun path name => ({(path, .constant name)}, 0))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      ({(path, .eOperator body.1)},
        if representativeForBody? left right assignment body.1 = some selected
        then {path} else 0))
    (∅ : NormalForm Const (Fin 0) Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    rfl (by intros; rfl) (by intros; rfl)
    (by intro path impossible; exact impossible.elim0)
    (by intros; rfl) target
  refine Eq.trans ?_ (rebuildNormalForm_eq target)
  unfold projectedCoefficientPair
  exact folded

theorem constantCoefficient_projectGroundNormalForm_inr
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (selected : EOccurrence left right)
    (target : NormalForm Const (Fin 0) Hom) :
    constantCoefficient
        (projectGroundNormalForm left right assignment target)
        (Sum.inr selected) =
      (projectedCoefficientPair left right assignment selected target).2 := by
  have folded := NormalForm.fold_hom
    (fun result : NormalForm Const (Fin 0) Hom ×
        NormalForm (ECombinationBasis left right) (Fin 0) Hom =>
      (result.1,
        constantCoefficient result.2 (Sum.inr selected)))
    (∅, ∅)
    (fun first second => (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      let original : NormalForm Const (Fin 0) Hom :=
        {(path, .eOperator body.1)}
      let projected : NormalForm
          (ECombinationBasis left right) (Fin 0) Hom :=
        match representativeForBody? left right assignment body.1 with
        | none => ∅
        | some representative => {(path, .constant (.inr representative))}
      (original, projected))
    (∅, 0)
    (fun first second => (first.1 ∪ second.1, first.2 + second.2))
    (fun path name => ({(path, .constant name)}, 0))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      ({(path, .eOperator body.1)},
        if representativeForBody? left right assignment body.1 = some selected
        then {path} else 0))
    (by simp)
    (by intro first second; simp [constantCoefficient_union])
    (by intro path name; simp)
    (by intro path impossible; exact impossible.elim0)
    (by
      intro path body
      dsimp only
      cases found : representativeForBody? left right assignment body.1 with
      | none => simp
      | some representative =>
          by_cases equality : representative = selected
          · subst representative
            simp
          · simp [equality])
    target
  unfold projectGroundNormalForm projectGroundNormalFormPair
  exact congrArg Prod.snd folded

local instance coefficientPairCommutative
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Commutative (fun first second :
        NormalForm Const Var Hom × HomContext Hom =>
      (first.1 ∪ second.1, first.2 + second.2)) :=
  ⟨by
    intro first second
    apply Prod.ext
    · exact normalUnionCommutative.comm _ _
    · exact add_comm _ _⟩

local instance coefficientPairAssociative
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Associative (fun first second :
        NormalForm Const Var Hom × HomContext Hom =>
      (first.1 ∪ second.1, first.2 + second.2)) :=
  ⟨by
    intro first middle last
    apply Prod.ext
    · exact normalUnionAssociative.assoc _ _ _
    · exact add_assoc _ _ _⟩

local instance coefficientPairIdempotent
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.IdempotentOp (fun first second :
        NormalForm Const Var Hom × HomContext Hom =>
      (first.1 ∪ second.1, first.2 + second.2)) :=
  ⟨by
    intro value
    apply Prod.ext
    · exact normalUnionIdempotent.idempotent _
    · exact HomContext.add_self _⟩

local instance homContextAddCommutative
    {Hom : Type*} [Encodable Hom] :
    Std.Commutative (fun left right : HomContext Hom => left + right) :=
  ⟨add_comm⟩

local instance homContextAddAssociative
    {Hom : Type*} [Encodable Hom] :
    Std.Associative (fun left right : HomContext Hom => left + right) :=
  ⟨add_assoc⟩

local instance homContextAddIdempotent
    {Hom : Type*} [Encodable Hom] :
    Std.IdempotentOp (fun left right : HomContext Hom => left + right) :=
  ⟨HomContext.add_self⟩

private theorem mem_homContext_finsetFold
    {Alpha Hom : Type*} [DecidableEq Alpha] [Encodable Hom]
    (function : Alpha → HomContext Hom) (set : Finset Alpha)
    (path : List Hom)
    (membership : path ∈
      (set.fold
        (fun (left right : HomContext Hom) => left + right) 0 function).paths) :
    ∃ value ∈ set, path ∈ (function value).paths := by
  induction set using Finset.induction_on with
  | empty => simp at membership
  | @insert value set absent inductionHypothesis =>
      rw [Finset.fold_insert_idem] at membership
      rw [HomContext.mem_add] at membership
      rcases membership with membership | membership
      · exact ⟨value, by simp, membership⟩
      · rcases inductionHypothesis membership with
          ⟨found, foundMembership, pathMembership⟩
        exact ⟨found, by simp [foundMembership], pathMembership⟩

theorem mem_projectedCoefficientPair_gives_eAtom
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (selected : EOccurrence left right)
    (target : NormalForm Const (Fin 0) Hom) (path : List Hom)
    (membership : path ∈
      (projectedCoefficientPair left right assignment selected target).2.paths) :
    ∃ body : NormalForm Const (Fin 0) Hom,
      representativeForBody? left right assignment body = some selected ∧
        (path, RawNormalAtom.eOperator body.raw) ∈
          RecursiveFinset.toFinset target.raw := by
  let combine := fun first second :
      NormalForm Const (Fin 0) Hom × HomContext Hom =>
    (first.1 ∪ second.1, first.2 + second.2)
  let onConstant : List Hom → Const →
      NormalForm Const (Fin 0) Hom × HomContext Hom :=
    fun path name =>
    (({(path, NormalAtom.constant name)} : NormalForm Const (Fin 0) Hom), 0)
  let onVariable : List Hom → Fin 0 →
      NormalForm Const (Fin 0) Hom × HomContext Hom :=
    fun _ impossible => impossible.elim0
  let onEOperator : List Hom →
      (NormalForm Const (Fin 0) Hom × HomContext Hom) →
      (NormalForm Const (Fin 0) Hom × HomContext Hom) := fun path body =>
    ({(path, NormalAtom.eOperator body.1)},
      if representativeForBody? left right assignment body.1 = some selected
      then {path} else 0)
  have folded :
      rawFold (∅, 0) combine onConstant onVariable onEOperator target.raw =
        (RecursiveFinset.toFinset target.raw).fold combine (∅, 0)
          (rawFoldSummand (∅, 0) combine onConstant onVariable onEOperator) :=
    rawFold_toFinset (∅, 0) combine
      (by
        intro value
        apply Prod.ext
        · apply normalUnionEmpty
        · apply add_zero)
      onConstant onVariable onEOperator target.valid.outer
  have membershipFold : path ∈
      ((RecursiveFinset.toFinset target.raw).fold combine (∅, 0)
        (rawFoldSummand (∅, 0) combine onConstant onVariable
          onEOperator)).2.paths := by
    unfold projectedCoefficientPair NormalForm.fold at membership
    rw [folded] at membership
    exact membership
  have secondFold :
      (RecursiveFinset.toFinset target.raw).fold
          (fun (left right : HomContext Hom) => left + right) 0
          (fun summand =>
            (rawFoldSummand (∅, 0) combine onConstant onVariable
              onEOperator summand).2) =
        ((RecursiveFinset.toFinset target.raw).fold combine (∅, 0)
          (rawFoldSummand (∅, 0) combine onConstant onVariable
            onEOperator)).2 := by
    exact Finset.fold_hom
      (op := combine)
      (op' := fun (left right : HomContext Hom) => left + right)
      (f := rawFoldSummand (∅, 0) combine onConstant onVariable onEOperator)
      (b := (∅, 0))
      (s := RecursiveFinset.toFinset target.raw)
      (m := Prod.snd) (by intros; rfl)
  rw [← secondFold] at membershipFold
  rcases mem_homContext_finsetFold _ _ path membershipFold with
    ⟨summand, summandMembership, selectedMembership⟩
  rcases summand with ⟨summandPath, atom⟩
  rcases atom with constant | «variable» | rawBody
  · simp [rawFoldSummand, onConstant] at selectedMembership
  · exact «variable».elim0
  · have atomValid := target.valid.nested
        (summandPath, RawNormalAtom.eOperator rawBody) summandMembership
    cases atomValid with
    | eOperator bodyValid =>
        let body : NormalForm Const (Fin 0) Hom := ⟨rawBody, bodyValid⟩
        have bodyFirst :
            (rawFold (∅, 0) combine onConstant onVariable onEOperator
              rawBody).1 = body := by
          exact projectedCoefficientPair_first
            left right assignment selected body
        simp only [rawFoldSummand, onEOperator, bodyFirst] at selectedMembership
        have accepted : representativeForBody? left right assignment body =
            some selected := by
          by_contra rejected
          simp [rejected] at selectedMembership
        rw [if_pos accepted] at selectedMembership
        have pathEquality : summandPath = path := by
          have reverseEquality : path = summandPath := by
            change path ∈ ({summandPath} : Finset (List Hom)) at selectedMembership
            exact Finset.mem_singleton.mp selectedMembership
          exact reverseEquality.symm
        subst summandPath
        exact ⟨body, accepted, summandMembership⟩

theorem projectedAssignmentMatrix_nonzero_gives_eAtom
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (name : Var) (selected : EOccurrence left right)
    (nonzero : projectedAssignmentMatrix left right assignment name
      (Sum.inr selected) ≠ 0) :
    ∃ path,
      (path, RawNormalAtom.eOperator
          (occurrenceBodyValue left right assignment selected).raw) ∈
        RecursiveFinset.toFinset (canonicalize (assignment name)).raw := by
  have pathsNonempty :
      (projectedAssignmentMatrix left right assignment name
        (Sum.inr selected)).paths ≠ ∅ := by
    intro pathsEmpty
    apply nonzero
    apply HomContext.ext
    simpa using pathsEmpty
  rcases Finset.nonempty_iff_ne_empty.mpr pathsNonempty with
    ⟨path, pathMembership⟩
  have coefficientMembership : path ∈
      (projectedCoefficientPair left right assignment selected
        (canonicalize (assignment name))).2.paths := by
    rw [← constantCoefficient_projectGroundNormalForm_inr]
    exact pathMembership
  rcases mem_projectedCoefficientPair_gives_eAtom
      left right assignment selected (canonicalize (assignment name)) path
      coefficientMembership with ⟨body, found, bodyMembership⟩
  have bodyEquality := representativeForBody?_some_value
    left right assignment body found
  rw [← bodyEquality] at bodyMembership
  exact ⟨path, bodyMembership⟩

theorem mem_variableSupport_purify_and_assignment_eAtom
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (target : NormalForm Const Var Hom)
    (name : Var) (selected : EOccurrence left right)
    (variableMembership : name ∈ variableSupport
      (purifyNormalForm left right
        (projectedEConfiguration left right assignment) target))
    (assignmentMembership : ∃ assignmentPath,
      (assignmentPath, RawNormalAtom.eOperator
          (occurrenceBodyValue left right assignment selected).raw) ∈
        RecursiveFinset.toFinset (canonicalize (assignment name)).raw) :
    ∃ path,
      (path, RawNormalAtom.eOperator
          (occurrenceBodyValue left right assignment selected).raw) ∈
        RecursiveFinset.toFinset
          (applyGroundAssignment assignment target).raw := by
  let result := projectionProofScan left right assignment target
  have purifiedMembership : name ∈ variableSupport result.purified := by
    rw [projectionProofScan_purified left right assignment target]
    exact variableMembership
  rcases result.variableDependencies name selected purifiedMembership
      assignmentMembership with ⟨path, pathMembership⟩
  refine ⟨path, ?_⟩
  rw [projectionProofScan_source left right assignment target,
    evaluateNormalForm_eq_applyGroundAssignment] at pathMembership
  exact pathMembership

theorem projected_rank_lt_of_variable_dependency
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (representative basisOccurrence : EOccurrence left right)
    (name : Var)
    (variableMembership : name ∈ variableSupport
      (purifiedOccurrenceBody left right
        (projectedEConfiguration left right assignment) representative))
    (coefficientNonzero : projectedAssignmentMatrix left right assignment name
      (Sum.inr basisOccurrence) ≠ 0) :
    projectedOccurrenceRank left right assignment basisOccurrence <
      projectedOccurrenceRank left right assignment representative := by
  rcases projectedAssignmentMatrix_nonzero_gives_eAtom
      left right assignment name basisOccurrence coefficientNonzero with
    ⟨assignmentPath, assignmentMembership⟩
  rcases mem_variableSupport_purify_and_assignment_eAtom
      left right assignment representative.body name basisOccurrence
      (by
        unfold purifiedOccurrenceBody at variableMembership
        exact variableMembership)
      ⟨assignmentPath, assignmentMembership⟩ with
    ⟨path, bodyMembership⟩
  apply projectedOccurrenceRank_lt_of_measure_lt left right assignment
  exact rawNormalFormMeasure_lt_of_mem_eOperator
    (Const := Const) (Var := Fin 0) (Hom := Hom)
    (occurrenceBodyValue left right assignment representative)
    path (occurrenceBodyValue left right assignment basisOccurrence).raw
    bodyMembership

/-- Normalization never retains the forbidden atom `E(0)`. -/
theorem no_empty_eOperator_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) (path : List Hom) :
    (path, RawNormalAtom.eOperator
        (NormalForm.empty : NormalForm Const Var Hom).raw) ∉
      RecursiveFinset.toFinset (normalize term).raw := by
  induction term generalizing path with
  | zero =>
      change _ ∉ RecursiveFinset.toFinset
        (∅ : RawNormalForm Const Var Hom)
      simp
  | const name =>
      change _ ∉ RecursiveFinset.toFinset
        ({([], RawNormalAtom.constant name)} : RawNormalForm Const Var Hom)
      simp
  | var name =>
      change _ ∉ RecursiveFinset.toFinset
        ({([], RawNormalAtom.variable name)} : RawNormalForm Const Var Hom)
      simp
  | add first second firstHypothesis secondHypothesis =>
      simp only [normalize_add]
      change _ ∉ RecursiveFinset.toFinset
        ((normalize first).raw ∪ (normalize second).raw)
      rw [RecursiveFinset.toFinset_union]
      simp [firstHypothesis, secondHypothesis]
  | hom name body inductionHypothesis =>
      simp only [normalize_hom, prefixHom]
      change _ ∉ RecursiveFinset.toFinset
        (rawPrefixHom name (normalize body).raw)
      unfold rawPrefixHom
      rw [RecursiveFinset.toFinset_image _ (normalize body).valid.outer]
      intro membership
      rcases Finset.mem_image.mp membership with
        ⟨⟨innerPath, atom⟩, innerMembership, equality⟩
      have atomEquality : atom = RawNormalAtom.eOperator
          (NormalForm.empty : NormalForm Const Var Hom).raw :=
        congrArg Prod.snd equality
      subst atom
      exact inductionHypothesis innerPath innerMembership
  | free body inductionHypothesis =>
      simp only [normalize_free]
      by_cases bodyZero : normalize body =
          (NormalForm.empty : NormalForm Const Var Hom)
      · rw [bodyZero]
        change _ ∉ RecursiveFinset.toFinset
          (rawWrapE
            (NormalForm.empty : NormalForm Const Var Hom).raw)
        simp [NormalForm.empty, rawWrapE]
      · rw [wrapE_of_ne_empty bodyZero]
        change _ ∉ RecursiveFinset.toFinset
          ({([], RawNormalAtom.eOperator (normalize body).raw)} :
            RawNormalForm Const Var Hom)
        simp only [RecursiveFinset.toFinset_singleton, Finset.mem_singleton]
        intro equality
        have rawEquality : (normalize body).raw =
            (NormalForm.empty : NormalForm Const Var Hom).raw := by
          exact RawNormalAtom.eOperator.inj
            (congrArg Prod.snd equality).symm
        exact bodyZero (NormalForm.ext_raw rawEquality)

/-- A nonzero projected alien coefficient can only name the fixed
representative selected by the projection. -/
theorem projectedAssignmentMatrix_nonzero_is_representative
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (name : Var) (selected : EOccurrence left right)
    (nonzero : projectedAssignmentMatrix left right assignment name
      (Sum.inr selected) ≠ 0) :
    projectedOccurrenceClass left right assignment selected =
      some selected := by
  have pathsNonempty :
      (projectedAssignmentMatrix left right assignment name
        (Sum.inr selected)).paths ≠ ∅ := by
    intro pathsEmpty
    apply nonzero
    apply HomContext.ext
    simpa using pathsEmpty
  rcases Finset.nonempty_iff_ne_empty.mpr pathsNonempty with
    ⟨path, pathMembership⟩
  have coefficientMembership : path ∈
      (projectedCoefficientPair left right assignment selected
        (canonicalize (assignment name))).2.paths := by
    rw [← constantCoefficient_projectGroundNormalForm_inr]
    exact pathMembership
  rcases mem_projectedCoefficientPair_gives_eAtom
      left right assignment selected (canonicalize (assignment name)) path
      coefficientMembership with
    ⟨body, found, bodyMembership⟩
  have bodyNonempty : body ≠ ∅ := by
    intro bodyZero
    subst body
    unfold canonicalize at bodyMembership
    exact no_empty_eOperator_normalize (reify (assignment name)) path
      bodyMembership
  have valueEquality := representativeForBody?_some_value
    left right assignment body found
  unfold projectedOccurrenceClass
  rw [valueEquality]
  simp [bodyNonempty, found]

/-- The projected matrix satisfies every coefficient-local dependency row. -/
theorem projectedAssignmentMatrix_restriction_row
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (representative : EOccurrence left right) (name : Var)
    (basisOccurrence : EOccurrence left right)
    (basis : ECombinationBasis left right) :
    let configuration := projectedEConfiguration left right assignment
    evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right configuration basis).1
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inr (representative, name, basisOccurrence))) basis ≤
      evaluateMatrixRepresentation
        (eCombinationColumnRepresentations left right configuration basis).2
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inr (representative, name, basisOccurrence))) basis := by
  dsimp only
  let configuration := projectedEConfiguration left right assignment
  by_cases active : basis = Sum.inr basisOccurrence ∧
      forbiddenOccurrenceColumn left right configuration name
        basisOccurrence = true
  · have coefficientZero :
        projectedAssignmentMatrix left right assignment name
          (Sum.inr basisOccurrence) = 0 := by
      by_contra nonzero
      have fixed := projectedAssignmentMatrix_nonzero_is_representative
        left right assignment name basisOccurrence nonzero
      have forbidden :=
        (forbiddenOccurrenceColumn_eq_true_iff left right configuration
          name basisOccurrence).mp active.2
      rcases forbidden with notFixed |
          ⟨selectedRepresentative, selectedFixed, variableMembership,
            rankNotLess⟩
      · exact notFixed fixed
      · apply rankNotLess
        exact projected_rank_lt_of_variable_dependency left right assignment
          selectedRepresentative basisOccurrence name variableMembership nonzero
    rw [active.1]
    change evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun row => normalize
          (eCombinationColumnLeftTerm left right configuration
            (Sum.inr basisOccurrence) row)))
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inr (representative, name, basisOccurrence)))
        (Sum.inr basisOccurrence) ≤
      evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun row => normalize
          (eCombinationRightTerm left right configuration row)))
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inr (representative, name, basisOccurrence)))
        (Sum.inr basisOccurrence)
    rw [evaluate_fullMatrixRepresentation_projectedAssignment
        left right assignment
        (eCombinationColumnLeftTerm left right configuration
          (Sum.inr basisOccurrence))
        (eCombinationColumnLeftTerm_isACUIh left right configuration
          (Sum.inr basisOccurrence))
        (.inr (.inr (representative, name, basisOccurrence)))
        (Sum.inr basisOccurrence),
      evaluate_fullMatrixRepresentation_projectedAssignment
        left right assignment
        (eCombinationRightTerm left right configuration)
        (eCombinationRightTerm_isACUIh left right configuration)
        (.inr (.inr (representative, name, basisOccurrence)))
        (Sum.inr basisOccurrence)]
    simp only [eCombinationColumnLeftTerm]
    rw [if_pos ⟨True.intro, active.2⟩]
    simp only [eCombinationRightTerm, Term.substitute_var,
      Term.substitute_zero, normalize_zero, constantCoefficient_empty]
    change constantCoefficient
        (canonicalize (projectedAssignment left right assignment name))
        (Sum.inr basisOccurrence) ≤ 0
    rw [constantCoefficient_canonicalize]
    change projectedAssignmentMatrix left right assignment name
        (Sum.inr basisOccurrence) ≤ 0
    rw [coefficientZero]
  · change evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun row => normalize
          (eCombinationColumnLeftTerm left right configuration basis row)))
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inr (representative, name, basisOccurrence))) basis ≤
      evaluateMatrixRepresentation
        (fullMatrixRepresentation (fun row => normalize
          (eCombinationRightTerm left right configuration row)))
        (projectedAssignmentMatrix left right assignment)
        (.inr (.inr (representative, name, basisOccurrence))) basis
    rw [evaluate_fullMatrixRepresentation_projectedAssignment
        left right assignment
        (eCombinationColumnLeftTerm left right configuration basis)
        (eCombinationColumnLeftTerm_isACUIh left right configuration basis)
        (.inr (.inr (representative, name, basisOccurrence))) basis,
      evaluate_fullMatrixRepresentation_projectedAssignment
        left right assignment
        (eCombinationRightTerm left right configuration)
        (eCombinationRightTerm_isACUIh left right configuration)
        (.inr (.inr (representative, name, basisOccurrence))) basis]
    simp [eCombinationColumnLeftTerm, active, eCombinationRightTerm]

/-- Projecting any genuine solution produces a valid solution of every
column-specialized ACUIh certificate row. -/
theorem projectedAssignmentMatrix_below
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (assignment : Var → NormalForm Const (Fin 0) Hom)
    (solved : IsSolvedInequality
      (applyGroundAssignment assignment left)
      (applyGroundAssignment assignment right)) :
    eCombinationMatrixBelow left right
      (projectedEConfiguration left right assignment)
      (projectedAssignmentMatrix left right assignment) := by
  intro row basis
  rcases row with ⟨⟩ | row
  · exact projectedAssignmentMatrix_outer_row
      left right assignment solved basis
  · rcases row with ⟨occurrence, direction⟩ |
        ⟨representative, name, basisOccurrence⟩
    · exact projectedAssignmentMatrix_body_row
        left right assignment occurrence direction basis
    · exact projectedAssignmentMatrix_restriction_row
        left right assignment representative name basisOccurrence basis

/-- Every genuine solution therefore supplies a finite valid certificate and
an exact ACUIh matrix witness. -/
theorem exists_valid_configuration_matrix_of_solution
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
      configuration.valid = true ∧
        ∃ values : Matrix Var (ECombinationBasis left right) (HomContext Hom),
          eCombinationMatrixBelow left right configuration values := by
  exact ⟨projectedEConfiguration left right assignment,
    projectedEConfiguration_valid left right assignment,
    projectedAssignmentMatrix left right assignment,
    projectedAssignmentMatrix_below left right assignment solved⟩

end ACUIHE.Solver.Search
