import ACUIHE.Solver.RecursiveFinset

namespace ACUIHE.Solver.NormalForm.Internal

universe u v w x

/-- The atom payload used by the internal encoded backend. -/
inductive RawNormalAtom
    (Const : Type u) (Var : Type v) (Hom : Type w) where
  | constant (name : Const)
  | variable (name : Var)
  | eOperator
      (body : RecursiveFinset
        (List Hom × RawNormalAtom Const Var Hom))

abbrev RawNormalSummand
    (Const : Type u) (Var : Type v) (Hom : Type w) :=
  List Hom × RawNormalAtom Const Var Hom

/-- The internal code-based normal-form representation. -/
abbrev RawNormalForm
    (Const : Type u) (Var : Type v) (Hom : Type w) :=
  RecursiveFinset (RawNormalSummand Const Var Hom)

def rawNormalAtomEquiv
    {Const : Type u} {Var : Type v} {Hom : Type w} :
    RawNormalAtom Const Var Hom ≃
      Const ⊕ (Var ⊕ RawNormalForm Const Var Hom) where
  toFun
    | .constant name => .inl name
    | .variable name => .inr (.inl name)
    | .eOperator body => .inr (.inr body)
  invFun
    | .inl name => .constant name
    | .inr (.inl name) => .variable name
    | .inr (.inr body) => .eOperator body
  left_inv := by
    intro atom
    cases atom <;> rfl
  right_inv := by
    intro value
    rcases value with name | name | body <;> rfl

instance
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] :
    Encodable (RawNormalAtom Const Var Hom) :=
  Encodable.ofEquiv _ rawNormalAtomEquiv

def rawNormalFormMeasure
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (normalForm : RawNormalForm Const Var Hom) : Nat :=
  RecursiveFinset.codeBound normalForm

def rawEAtom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (body : RawNormalForm Const Var Hom) : RawNormalAtom Const Var Hom :=
  .eOperator body

@[simp]
theorem encode_rawEAtom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var]
    (body : RawNormalForm Const Var Hom) :
    Encodable.encode (rawEAtom body) =
      2 * (2 * Encodable.encode body + 1) + 1 := by
  rfl

theorem rawNormalFormMeasure_le_encode_eSummand
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (body : RawNormalForm Const Var Hom) :
    rawNormalFormMeasure body ≤ Encodable.encode (path, rawEAtom body) := by
  calc
    rawNormalFormMeasure body = RecursiveFinset.codeBound body := rfl
    _ ≤ Encodable.encode body + 1 :=
      RecursiveFinset.codeBound_le_encode_add_one body
    _ ≤ Encodable.encode (rawEAtom body) := by
      rw [encode_rawEAtom]
      omega
    _ ≤ Encodable.encode (path, rawEAtom body) := by
      rw [Encodable.encode_prod_val]
      exact Nat.right_le_pair _ _

theorem rawNormalFormMeasure_lt_of_decode_eOperator
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {outer body : RawNormalForm Const Var Hom} {code : Nat} {path : List Hom}
    (membership : code ∈ outer.codes)
    (decoded : Encodable.decode₂ (RawNormalSummand Const Var Hom) code =
      some (path, .eOperator body)) :
    rawNormalFormMeasure body < rawNormalFormMeasure outer := by
  have encodingEquality :
      Encodable.encode (path, rawEAtom body) = code :=
    Encodable.decode₂_eq_some.mp decoded
  have bodyMeasureLeCode : rawNormalFormMeasure body ≤ code := by
    rw [← encodingEquality]
    exact rawNormalFormMeasure_le_encode_eSummand path body
  exact bodyMeasureLeCode.trans_lt
    (RecursiveFinset.code_lt_codeBound membership)

/-- The private well-founded semantic fold over the encoded backend. -/
def rawFold
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (normalForm : RawNormalForm Const Var Hom) : Result :=
  (normalForm.codes.attach.sort
      (fun left right => left.1 ≤ right.1)).foldr
    (fun code rest =>
      match _decoded :
          Encodable.decode₂ (RawNormalSummand Const Var Hom) code.1 with
      | none => rest
      | some (path, .constant name) =>
          combine (onConstant path name) rest
      | some (path, .variable name) =>
          combine (onVariable path name) rest
      | some (path, .eOperator body) =>
          combine
            (onEOperator path
              (rawFold zero combine onConstant onVariable onEOperator body))
            rest)
    zero
termination_by rawNormalFormMeasure normalForm
decreasing_by
  exact rawNormalFormMeasure_lt_of_decode_eOperator code.property _decoded

def rawPrefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : RawNormalForm Const Var Hom) :
    RawNormalForm Const Var Hom :=
  normalForm.image (fun summand => (name :: summand.1, summand.2))

def rawWrapE
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (body : RawNormalForm Const Var Hom) : RawNormalForm Const Var Hom :=
  if body = ∅ then ∅ else {([], rawEAtom body)}

theorem rawUnion_assoc
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (left middle right : RawNormalForm Const Var Hom) :
    (left ∪ middle) ∪ right = left ∪ (middle ∪ right) :=
  RecursiveFinset.union_assoc left middle right

theorem rawUnion_comm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (left right : RawNormalForm Const Var Hom) :
    left ∪ right = right ∪ left :=
  RecursiveFinset.union_comm left right

theorem rawUnion_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (normalForm : RawNormalForm Const Var Hom) :
    normalForm ∪ ∅ = normalForm :=
  RecursiveFinset.union_empty normalForm

theorem rawUnion_self
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (normalForm : RawNormalForm Const Var Hom) :
    normalForm ∪ normalForm = normalForm :=
  RecursiveFinset.union_self normalForm

@[simp]
theorem rawFold_empty
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result) :
    rawFold zero combine onConstant onVariable onEOperator
      (∅ : RawNormalForm Const Var Hom) = zero := by
  rw [rawFold]
  have attachEmpty :
      (∅ : RawNormalForm Const Var Hom).codes.attach = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro code membership
    have impossible : code.1 ∈ (∅ : Finset Nat) := by
      simpa only [RecursiveFinset.codes_empty] using code.property
    exact Finset.notMem_empty _ impossible
  rw [attachEmpty, Finset.sort_empty]
  rfl

@[simp]
theorem rawFold_singleton
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (summand : RawNormalSummand Const Var Hom) :
    rawFold zero combine onConstant onVariable onEOperator
        ({summand} : RawNormalForm Const Var Hom) =
      combine
        (match summand with
        | (path, .constant name) => onConstant path name
        | (path, .variable name) => onVariable path name
        | (path, .eOperator body) =>
            onEOperator path
              (rawFold zero combine onConstant onVariable onEOperator body))
        zero := by
  change rawFold zero combine onConstant onVariable onEOperator
      (RecursiveFinset.singleton summand) = _
  rw [rawFold]
  let encodedCode :
      {code // code ∈ (RecursiveFinset.singleton summand).codes} :=
    ⟨Encodable.encode summand, by simp⟩
  have attachSingleton :
      (RecursiveFinset.singleton summand).codes.attach = {encodedCode} := by
    ext code
    simp only [Finset.mem_attach, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    simpa only [RecursiveFinset.codes_singleton, Finset.mem_singleton]
      using code.property
  rw [attachSingleton, Finset.sort_singleton]
  simp only [List.foldr_cons, List.foldr_nil]
  dsimp only [encodedCode]
  rw [Encodable.decode₂_encode]
  rcases summand with ⟨path, atom⟩
  cases atom <;> rfl

def rawFoldCodeResult
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (code : Nat) : Result :=
  match Encodable.decode₂ (RawNormalSummand Const Var Hom) code with
  | none => zero
  | some (path, .constant name) => onConstant path name
  | some (path, .variable name) => onVariable path name
  | some (path, .eOperator body) =>
      onEOperator path
        (rawFold zero combine onConstant onVariable onEOperator body)

def rawFoldSummand
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result) :
    RawNormalSummand Const Var Hom → Result
  | (path, .constant name) => onConstant path name
  | (path, .variable name) => onVariable path name
  | (path, .eOperator body) =>
      onEOperator path
        (rawFold zero combine onConstant onVariable onEOperator body)

@[simp]
theorem rawFoldCodeResult_encode
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (summand : RawNormalSummand Const Var Hom) :
    rawFoldCodeResult zero combine onConstant onVariable onEOperator
        (Encodable.encode summand) =
      rawFoldSummand zero combine onConstant onVariable onEOperator summand := by
  unfold rawFoldCodeResult
  rw [Encodable.decode₂_encode]
  rcases summand with ⟨path, atom⟩
  cases atom <;> rfl

theorem foldr_sort_eq_fold
    {A B : Type*} {operation : B → B → B}
    [Std.Commutative operation] [Std.Associative operation]
    (set : Finset A) (relation : A → A → Prop)
    [DecidableRel relation] [IsTrans A relation]
    [Std.Antisymm relation] [Std.Total relation]
    (seed : B) (function : A → B) :
    (set.sort relation).foldr
        (fun value result => operation (function value) result) seed =
      set.fold operation seed function := by
  rw [← List.foldr_map]
  change Multiset.fold operation seed
      (↑((set.sort relation).map function) : Multiset B) =
    Multiset.fold operation seed (set.1.map function)
  rw [show (↑((set.sort relation).map function) : Multiset B) =
    (↑(set.sort relation) : Multiset A).map function by rfl,
    Finset.sort_eq]

theorem rawFold_eq_codeFold
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    [Std.Commutative combine] [Std.Associative combine]
    (zeroRight : ∀ value, combine value zero = value)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (normalForm : RawNormalForm Const Var Hom) :
    rawFold zero combine onConstant onVariable onEOperator normalForm =
      normalForm.codes.fold combine zero
        (rawFoldCodeResult zero combine onConstant onVariable onEOperator) := by
  rw [rawFold]
  have zeroLeft : ∀ value, combine zero value = value := by
    intro value
    exact (Std.Commutative.comm zero value).trans (zeroRight value)
  have stepEquality :
      (fun (code : {code // code ∈ normalForm.codes}) (rest : Result) =>
        match _decoded :
            Encodable.decode₂ (RawNormalSummand Const Var Hom) code.1 with
        | none => rest
        | some (path, .constant name) => combine (onConstant path name) rest
        | some (path, .variable name) => combine (onVariable path name) rest
        | some (path, .eOperator body) =>
            combine
              (onEOperator path
                (rawFold zero combine onConstant onVariable onEOperator body))
              rest) =
      (fun code rest =>
        combine
          (rawFoldCodeResult zero combine onConstant onVariable onEOperator
            code.1)
          rest) := by
    funext code rest
    unfold rawFoldCodeResult
    generalize decodedEquality :
      Encodable.decode₂ (RawNormalSummand Const Var Hom) code.1 = decoded
    cases decoded with
    | none => exact (zeroLeft rest).symm
    | some summand =>
        rcases summand with ⟨path, atom⟩
        cases atom <;> rfl
  rw [stepEquality, foldr_sort_eq_fold]
  have attachedFold := Finset.fold_map
    (op := combine)
    (b := zero)
    (f := rawFoldCodeResult zero combine onConstant onVariable onEOperator)
    (g := Function.Embedding.subtype (fun code => code ∈ normalForm.codes))
    (s := normalForm.codes.attach)
  rw [Finset.attach_map_val] at attachedFold
  have functionEquality :
      (fun code : {code // code ∈ normalForm.codes} =>
        rawFoldCodeResult zero combine onConstant onVariable onEOperator
          code.1) =
      (rawFoldCodeResult zero combine onConstant onVariable onEOperator ∘
        Function.Embedding.subtype (fun code => code ∈ normalForm.codes)) := by
    funext code
    rfl
  rw [functionEquality]
  exact attachedFold.symm

theorem rawFold_ofFinset
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    [Std.Commutative combine] [Std.Associative combine]
    [Std.IdempotentOp combine]
    (zeroRight : ∀ value, combine value zero = value)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (summands : Finset (RawNormalSummand Const Var Hom)) :
    rawFold zero combine onConstant onVariable onEOperator
        (RecursiveFinset.ofFinset summands) =
      summands.fold combine zero
        (rawFoldSummand zero combine onConstant onVariable onEOperator) := by
  rw [rawFold_eq_codeFold zero combine zeroRight]
  unfold RecursiveFinset.ofFinset
  change (summands.image Encodable.encode).fold combine zero
      (rawFoldCodeResult zero combine onConstant onVariable onEOperator) = _
  rw [Finset.fold_image_idem]
  apply Finset.fold_congr
  intro summand membership
  exact rawFoldCodeResult_encode zero combine onConstant onVariable
    onEOperator summand

theorem rawFold_toFinset
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    [Std.Commutative combine] [Std.Associative combine]
    [Std.IdempotentOp combine]
    (zeroRight : ∀ value, combine value zero = value)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    {normalForm : RawNormalForm Const Var Hom}
    (valid : RecursiveFinset.Valid normalForm) :
    rawFold zero combine onConstant onVariable onEOperator normalForm =
      (RecursiveFinset.toFinset normalForm).fold combine zero
        (rawFoldSummand zero combine onConstant onVariable onEOperator) := by
  nth_rewrite 1 [← valid]
  exact rawFold_ofFinset zero combine zeroRight onConstant onVariable
    onEOperator _

theorem rawFold_image
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    [Std.Commutative combine] [Std.Associative combine]
    [Std.IdempotentOp combine]
    (zeroRight : ∀ value, combine value zero = value)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (function : RawNormalSummand Const Var Hom →
      RawNormalSummand Const Var Hom)
    (mapResult : Result → Result)
    (mapZero : mapResult zero = zero)
    (mapCombine : ∀ left right,
      mapResult (combine left right) = combine (mapResult left) (mapResult right))
    {normalForm : RawNormalForm Const Var Hom}
    (valid : RecursiveFinset.Valid normalForm)
    (pointwise : ∀ summand ∈ RecursiveFinset.toFinset normalForm,
      rawFoldSummand zero combine onConstant onVariable onEOperator
          (function summand) =
        mapResult
          (rawFoldSummand zero combine onConstant onVariable onEOperator
            summand)) :
    rawFold zero combine onConstant onVariable onEOperator
        (RecursiveFinset.image function normalForm) =
      mapResult
        (rawFold zero combine onConstant onVariable onEOperator normalForm) := by
  let _ := Encodable.decidableEqOfEncodable
    (RawNormalSummand Const Var Hom)
  have imageValid :
      RecursiveFinset.Valid (RecursiveFinset.image function normalForm) :=
    valid.image function
  rw [rawFold_toFinset zero combine zeroRight onConstant onVariable
      onEOperator imageValid,
    RecursiveFinset.toFinset_image function valid,
    rawFold_toFinset zero combine zeroRight onConstant onVariable
      onEOperator valid,
    Finset.fold_image_idem]
  simp only [Function.comp_apply]
  rw [Finset.fold_congr pointwise]
  have folded := Finset.fold_hom
    (s := RecursiveFinset.toFinset normalForm)
    (op := combine)
    (op' := combine)
    (m := mapResult)
    (b := zero)
    (f := rawFoldSummand zero combine onConstant onVariable onEOperator)
    mapCombine
  simpa only [mapZero] using folded

theorem finsetFold_union
    {Result A : Type*} {combine : Result → Result → Result}
    [DecidableEq A]
    [Std.Commutative combine] [Std.Associative combine]
    [Std.IdempotentOp combine]
    (zero : Result) (zeroRight : ∀ value, combine value zero = value)
    (function : A → Result) (left right : Finset A) :
    (left ∪ right).fold combine zero function =
      combine (left.fold combine zero function)
        (right.fold combine zero function) := by
  induction right using Finset.induction_on with
  | empty =>
      rw [Finset.union_empty, Finset.fold_empty, zeroRight]
  | @insert value right notMember inductionHypothesis =>
      rw [Finset.union_insert, Finset.fold_insert_idem,
        Finset.fold_insert_idem, inductionHypothesis]
      ac_rfl

theorem rawFold_union
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    [Std.Commutative combine] [Std.Associative combine]
    [Std.IdempotentOp combine]
    (zeroRight : ∀ value, combine value zero = value)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (left right : RawNormalForm Const Var Hom) :
    rawFold zero combine onConstant onVariable onEOperator (left ∪ right) =
      combine
        (rawFold zero combine onConstant onVariable onEOperator left)
        (rawFold zero combine onConstant onVariable onEOperator right) := by
  rw [rawFold_eq_codeFold zero combine zeroRight,
    RecursiveFinset.codes_union,
    finsetFold_union zero zeroRight,
    ← rawFold_eq_codeFold zero combine zeroRight,
    ← rawFold_eq_codeFold zero combine zeroRight]

/-- A handler-preserving map commutes with the internal semantic fold. -/
theorem rawFold_hom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    {Source : Type x} {Target : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (map : Source → Target)
    (sourceZero : Source) (sourceCombine : Source → Source → Source)
    (sourceConstant : List Hom → Const → Source)
    (sourceVariable : List Hom → Var → Source)
    (sourceEOperator : List Hom → Source → Source)
    (targetZero : Target) (targetCombine : Target → Target → Target)
    (targetConstant : List Hom → Const → Target)
    (targetVariable : List Hom → Var → Target)
    (targetEOperator : List Hom → Target → Target)
    (mapZero : map sourceZero = targetZero)
    (mapCombine : ∀ left right,
      map (sourceCombine left right) = targetCombine (map left) (map right))
    (mapConstant : ∀ path name,
      map (sourceConstant path name) = targetConstant path name)
    (mapVariable : ∀ path name,
      map (sourceVariable path name) = targetVariable path name)
    (mapEOperator : ∀ path body,
      map (sourceEOperator path body) = targetEOperator path (map body))
    (normalForm : RawNormalForm Const Var Hom) :
    map
        (rawFold sourceZero sourceCombine sourceConstant sourceVariable
          sourceEOperator normalForm) =
      rawFold targetZero targetCombine targetConstant targetVariable
        targetEOperator normalForm := by
  rw [rawFold, rawFold]
  generalize codesEquality :
    normalForm.codes.attach.sort (fun left right => left.1 ≤ right.1) = codes
  clear codesEquality
  induction codes with
  | nil => exact mapZero
  | cons code codes inductionHypothesis =>
    simp only [List.foldr_cons]
    generalize decodedEquality :
      Encodable.decode₂ (RawNormalSummand Const Var Hom) code.1 = decoded
    cases decoded with
    | none => exact inductionHypothesis
    | some summand =>
        rcases summand with ⟨path, atom⟩
        rcases atom with name | name | body
        · rw [mapCombine, mapConstant, inductionHypothesis]
        · rw [mapCombine, mapVariable, inductionHypothesis]
        · simp only
          rw [mapCombine, mapEOperator, inductionHypothesis]
          congr 1
          exact congrArg (targetEOperator path)
            (rawFold_hom map sourceZero sourceCombine sourceConstant
              sourceVariable sourceEOperator targetZero targetCombine
              targetConstant targetVariable targetEOperator mapZero mapCombine
              mapConstant mapVariable mapEOperator body)
termination_by rawNormalFormMeasure normalForm
decreasing_by
  exact rawNormalFormMeasure_lt_of_decode_eOperator
    code.property decodedEquality

theorem rawFold_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    [Std.Commutative combine] [Std.Associative combine]
    [Std.IdempotentOp combine]
    (zeroRight : ∀ value, combine value zero = value)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (name : Hom) (mapResult : Result → Result)
    (mapZero : mapResult zero = zero)
    (mapCombine : ∀ left right,
      mapResult (combine left right) = combine (mapResult left) (mapResult right))
    (mapConstant : ∀ path constantName,
      onConstant (name :: path) constantName =
        mapResult (onConstant path constantName))
    (mapVariable : ∀ path variableName,
      onVariable (name :: path) variableName =
        mapResult (onVariable path variableName))
    (mapEOperator : ∀ path body,
      onEOperator (name :: path) body = mapResult (onEOperator path body))
    {normalForm : RawNormalForm Const Var Hom}
    (valid : RecursiveFinset.Valid normalForm) :
    rawFold zero combine onConstant onVariable onEOperator
        (rawPrefixHom name normalForm) =
      mapResult
        (rawFold zero combine onConstant onVariable onEOperator normalForm) := by
  unfold rawPrefixHom
  apply rawFold_image zero combine zeroRight onConstant onVariable
    onEOperator _ mapResult mapZero mapCombine valid
  intro summand membership
  rcases summand with ⟨path, atom⟩
  rcases atom with constantName | variableName | body
  · exact mapConstant path constantName
  · exact mapVariable path variableName
  · exact mapEOperator path _

theorem rawPrefixHom_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (left right : RawNormalForm Const Var Hom) :
    rawPrefixHom name (left ∪ right) =
      rawPrefixHom name left ∪ rawPrefixHom name right := by
  simpa only [rawPrefixHom] using
    (RecursiveFinset.image_union
      (fun summand : RawNormalSummand Const Var Hom =>
        (name :: summand.1, summand.2)) left right)

@[simp]
theorem rawPrefixHom_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) :
    rawPrefixHom (Const := Const) (Var := Var) name ∅ = ∅ := by
  simp [rawPrefixHom]

@[simp]
theorem rawWrapE_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    rawWrapE (Const := Const) (Var := Var) (Hom := Hom) ∅ = ∅ := by
  simp [rawWrapE]

theorem rawEAtom_injective
    {Const : Type u} {Var : Type v} {Hom : Type w} :
    Function.Injective
      (rawEAtom (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro left right equality
  exact RawNormalAtom.eOperator.inj equality

theorem rawWrapE_injective
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Function.Injective
      (rawWrapE (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro left right equality
  by_cases leftZero : left = ∅
  · subst left
    by_cases rightZero : right = ∅
    · exact rightZero.symm
    · simp [rawWrapE, rightZero] at equality
  · by_cases rightZero : right = ∅
    · subst right
      simp [rawWrapE, leftZero] at equality
    · have atomEquality : rawEAtom left = rawEAtom right := by
        simpa [rawWrapE, leftZero, rightZero] using equality
      exact rawEAtom_injective atomEquality

/--
Mutually recursive validity of encoded atoms and encoded normal forms.

The form judgment validates every code stored at the current level and asks
for a valid-atom proof for every decoded summand.  The `eOperator` constructor
of the atom judgment then requires a recursively valid body.  Consequently a
proof is a tree following the complete `E` nesting structure.
-/
inductive ValidNode
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    (RawNormalAtom Const Var Hom ⊕
      RawNormalForm Const Var Hom) → Prop where
  | constant (name : Const) : ValidNode (.inl (.constant name))
  | variable (name : Var) : ValidNode (.inl (.variable name))
  | eOperator {body : RawNormalForm Const Var Hom}
      (bodyValid : ValidNode (.inr body)) :
      ValidNode (.inl (.eOperator body))
  | normalForm {normalForm : RawNormalForm Const Var Hom}
      (outer : RecursiveFinset.Valid normalForm)
      (nested : ∀ summand ∈ RecursiveFinset.toFinset normalForm,
        ValidNode (.inl summand.2)) :
      ValidNode (.inr normalForm)

abbrev RecursivelyValidAtom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (atom : RawNormalAtom Const Var Hom) : Prop :=
  ValidNode (.inl atom)

abbrev RecursivelyValid
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : RawNormalForm Const Var Hom) : Prop :=
  ValidNode (.inr normalForm)

theorem RecursivelyValid.outer
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {normalForm : RawNormalForm Const Var Hom}
    (valid : RecursivelyValid normalForm) :
    RecursiveFinset.Valid normalForm := by
  cases valid with
  | normalForm outer _ => exact outer

theorem RecursivelyValid.nested
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {normalForm : RawNormalForm Const Var Hom}
    (valid : RecursivelyValid normalForm)
    (summand : RawNormalSummand Const Var Hom)
    (membership : summand ∈ RecursiveFinset.toFinset normalForm) :
    RecursivelyValidAtom summand.2 := by
  cases valid with
  | normalForm _ nested => exact nested summand membership

theorem recursivelyValid_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    RecursivelyValid (∅ : RawNormalForm Const Var Hom) := by
  apply ValidNode.normalForm RecursiveFinset.valid_empty
  intro summand membership
  simp at membership

theorem recursivelyValid_singleton
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (summand : RawNormalSummand Const Var Hom)
    (atomValid : RecursivelyValidAtom summand.2) :
    RecursivelyValid ({summand} : RawNormalForm Const Var Hom) := by
  apply ValidNode.normalForm (RecursiveFinset.valid_singleton _)
  intro stored membership
  have storedEquality : stored = summand := by
    simpa only [RecursiveFinset.toFinset_singleton, Finset.mem_singleton]
      using membership
  subst stored
  exact atomValid

theorem recursivelyValid_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : RawNormalForm Const Var Hom}
    (leftValid : RecursivelyValid left)
    (rightValid : RecursivelyValid right) :
    RecursivelyValid (left ∪ right) := by
  let _ := Encodable.decidableEqOfEncodable
    (RawNormalSummand Const Var Hom)
  apply ValidNode.normalForm (leftValid.outer.union rightValid.outer)
  intro summand membership
  rw [RecursiveFinset.toFinset_union] at membership
  rcases Finset.mem_union.mp membership with leftMembership | rightMembership
  · exact leftValid.nested summand leftMembership
  · exact rightValid.nested summand rightMembership

theorem recursivelyValid_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) {normalForm : RawNormalForm Const Var Hom}
    (valid : RecursivelyValid normalForm) :
    RecursivelyValid (rawPrefixHom name normalForm) := by
  let _ := Encodable.decidableEqOfEncodable
    (RawNormalSummand Const Var Hom)
  let addPrefix : RawNormalSummand Const Var Hom →
      RawNormalSummand Const Var Hom :=
    fun summand => (name :: summand.1, summand.2)
  have outerValid : RecursiveFinset.Valid (rawPrefixHom name normalForm) := by
    exact valid.outer.image addPrefix
  apply ValidNode.normalForm outerValid
  intro stored membership
  have imageMembership :
      stored ∈ (RecursiveFinset.toFinset normalForm).image addPrefix := by
    change stored ∈ RecursiveFinset.toFinset
      (RecursiveFinset.image addPrefix normalForm) at membership
    rw [RecursiveFinset.toFinset_image addPrefix valid.outer] at membership
    exact membership
  rcases Finset.mem_image.mp imageMembership with
    ⟨source, sourceMembership, sourceEquality⟩
  subst stored
  exact valid.nested source sourceMembership

theorem recursivelyValid_wrapE
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {body : RawNormalForm Const Var Hom}
    (bodyValid : RecursivelyValid body) :
    RecursivelyValid (rawWrapE body) := by
  by_cases bodyZero : body = ∅
  · rw [rawWrapE, if_pos bodyZero]
    exact recursivelyValid_empty
  · rw [rawWrapE, if_neg bodyZero]
    apply ValidNode.normalForm (RecursiveFinset.valid_singleton _)
    intro stored membership
    have storedEquality : stored = ([], rawEAtom body) := by
      simpa only [RecursiveFinset.toFinset_singleton, Finset.mem_singleton]
        using membership
    subst stored
    exact ValidNode.eOperator bodyValid

end ACUIHE.Solver.NormalForm.Internal
