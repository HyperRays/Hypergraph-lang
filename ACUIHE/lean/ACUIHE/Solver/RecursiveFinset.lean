import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Finset

namespace ACUIHE.Solver

universe u v

/--
A finite set representation that can occur around a recursive occurrence in
an inductive declaration.

Lean rejects `Finset (F ...)` in a recursive constructor because `Finset` is
implemented using the quotient type `Multiset`. `RecursiveFinset` instead
stores the injective natural-number encodings of its elements. Its element
type is a phantom parameter, so the kernel can verify strict positivity.

The representation requires `Encodable α` only when elements are inserted or
mapped. Empty sets and union operate directly on the stored codes.
-/
structure RecursiveFinset (α : Type u) where
  codes : Finset Nat
  /-- Keeps the container in the same universe as its phantom element type,
  as required by Lean's nested-inductive translation. -/
  universeMarker : ULift.{u} Unit := ⟨()⟩

namespace RecursiveFinset

/-- Build a recursive finite set from its internal code set. -/
private def fromCodes (storedCodes : Finset Nat) : RecursiveFinset α :=
  ⟨storedCodes, ⟨()⟩⟩

/-- The representation is itself encodable, independently of its phantom
element type. -/
instance : Encodable (RecursiveFinset α) :=
  Encodable.ofEquiv (Finset Nat)
    { toFun := codes
      invFun := fromCodes
      left_inv := by
        intro value
        rcases value with ⟨storedCodes, ⟨marker⟩⟩
        cases marker
        rfl
      right_inv := by
        intro storedCodes
        rfl }

instance : DecidableEq (RecursiveFinset α) :=
  Encodable.decidableEqOfEncodable _

/-- Equality of encoded finite sets is equality of their stored codes. -/
theorem codes_injective :
    Function.Injective (codes : RecursiveFinset α → Finset Nat) := by
  intro left right equality
  rcases left with ⟨leftCodes, ⟨leftMarker⟩⟩
  rcases right with ⟨rightCodes, ⟨rightMarker⟩⟩
  cases leftMarker
  cases rightMarker
  cases equality
  rfl

/-- One more than the largest code stored in a recursive finite set.

This is a convenient well-founded measure for operations that inspect a
stored code and then recurse into data represented by that code. The empty
set has bound one. -/
def codeBound (set : RecursiveFinset α) : Nat :=
  set.codes.sup id + 1

/-- Every stored code is strictly smaller than the set's code bound. -/
theorem code_lt_codeBound {set : RecursiveFinset α} {code : Nat}
    (membership : code ∈ set.codes) :
    code < codeBound set := by
  simpa [codeBound] using
    Nat.lt_succ_of_le (Finset.le_sup (f := id) membership)

/-- An element's encoding is strictly smaller than the encoding of a list
containing it. This records the size property of mathlib's concrete list
encoding that is needed for the `RecursiveFinset` encoding bound below. -/
private theorem encode_lt_encodeList_of_mem [Encodable β]
    {value : β} {values : List β} (membership : value ∈ values) :
    Encodable.encode value < Encodable.encode values := by
  induction values with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      rw [Encodable.encode_list_cons]
      rcases List.mem_cons.mp membership with equality | membership
      · subst head
        exact Nat.lt_succ_of_le (Nat.left_le_pair _ _)
      · exact lt_of_lt_of_le (inductionHypothesis membership)
          (Nat.le_succ_of_le (Nat.right_le_pair _ _))

/-- Every stored code is strictly smaller than the concrete encoding of the
recursive finite set containing it. -/
theorem code_lt_encode {set : RecursiveFinset α} {code : Nat}
    (membership : code ∈ set.codes) :
    code < Encodable.encode set := by
  change code < Encodable.encode (set.codes.sort (fun a b => a ≤ b))
  simpa using encode_lt_encodeList_of_mem
    ((Finset.mem_sort (fun a b : Nat => a ≤ b)).2 membership)

/-- The code bound is at most one more than the concrete encoding of the
recursive finite set. The extra one is necessary for the empty set, whose
bound is one and whose encoding is zero. -/
theorem codeBound_le_encode_add_one (set : RecursiveFinset α) :
    codeBound set ≤ Encodable.encode set + 1 := by
  change Nat.succ (set.codes.sup id) ≤ Nat.succ (Encodable.encode set)
  exact Nat.succ_le_succ (Finset.sup_le fun code membership =>
    Nat.le_of_lt (code_lt_encode membership))

/-- The empty recursive finite set. -/
def empty : RecursiveFinset α :=
  fromCodes ∅

instance : EmptyCollection (RecursiveFinset α) :=
  ⟨empty⟩

instance : Zero (RecursiveFinset α) :=
  ⟨empty⟩

/-- A singleton recursive finite set. -/
def singleton [Encodable α] (value : α) : RecursiveFinset α :=
  fromCodes {Encodable.encode value}

instance [Encodable α] : Singleton α (RecursiveFinset α) :=
  ⟨singleton⟩

/-- Union of recursive finite sets. -/
def union (left right : RecursiveFinset α) : RecursiveFinset α :=
  fromCodes (left.codes ∪ right.codes)

instance : Union (RecursiveFinset α) :=
  ⟨union⟩

instance : Add (RecursiveFinset α) :=
  ⟨union⟩

/-- Membership is membership of the element's canonical encoding. -/
def Mem [Encodable α] (value : α) (set : RecursiveFinset α) : Prop :=
  Encodable.encode value ∈ set.codes

instance [Encodable α] : Membership α (RecursiveFinset α) :=
  ⟨fun set value => Mem value set⟩

/-- Map an encoded element. Codes outside the range of the source encoding
are retained. Such codes are not produced by the set-level constructors, and
retaining them makes `image` total on the raw representation. -/
private def mapCode [Encodable α] [Encodable β]
    (function : α → β) (code : Nat) : Nat :=
  match Encodable.decode₂ α code with
  | some value => Encodable.encode (function value)
  | none => code

/-- The image of a recursive finite set. -/
def image [Encodable α] [Encodable β]
    (function : α → β) (set : RecursiveFinset α) : RecursiveFinset β :=
  fromCodes (set.codes.image (mapCode function))

/-- Convert an ordinary finite set to the recursive representation. -/
def ofFinset [Encodable α] (set : Finset α) : RecursiveFinset α :=
  fromCodes (set.image Encodable.encode)

/-- Decode the valid element codes into an ordinary `Finset`. Codes that are
not in the range of the element encoding are ignored. -/
def toFinset [Encodable α] (set : RecursiveFinset α) : Finset α :=
  let _ := Encodable.decidableEqOfEncodable α
  set.codes.filterMap (Encodable.decode₂ α) (by
    intro leftCode rightCode value leftMembership rightMembership
    exact (Encodable.mem_decode₂.mp leftMembership).symm.trans
      (Encodable.mem_decode₂.mp rightMembership))

/-- Encoding an ordinary finite set and decoding it again is lossless. -/
@[simp]
theorem toFinset_ofFinset [Encodable α] (set : Finset α) :
    toFinset (ofFinset set) = set := by
  let _ := Encodable.decidableEqOfEncodable α
  ext value
  simp [toFinset, ofFinset, fromCodes, Encodable.decode₂_eq_some,
    Encodable.encode_inj]

@[simp]
theorem codes_empty : (∅ : RecursiveFinset α).codes = ∅ :=
  rfl

@[simp]
theorem codes_singleton [Encodable α] (value : α) :
    (singleton value).codes = {Encodable.encode value} :=
  rfl

@[simp]
theorem codes_union (left right : RecursiveFinset α) :
    (left ∪ right).codes = left.codes ∪ right.codes :=
  rfl

@[simp]
theorem codes_add (left right : RecursiveFinset α) :
    (left + right).codes = left.codes ∪ right.codes :=
  rfl

@[simp]
theorem mem_singleton [Encodable α] (left right : α) :
    left ∈ ({right} : RecursiveFinset α) ↔ left = right := by
  change Encodable.encode left ∈ ({Encodable.encode right} : Finset Nat) ↔ left = right
  simp [Encodable.encode_inj]

@[simp]
theorem mem_union [Encodable α] (value : α)
    (left right : RecursiveFinset α) :
    value ∈ left ∪ right ↔ value ∈ left ∨ value ∈ right := by
  change Encodable.encode value ∈ left.codes ∪ right.codes ↔
    Encodable.encode value ∈ left.codes ∨ Encodable.encode value ∈ right.codes
  exact Finset.mem_union

/-- Singleton construction is injective. -/
theorem singleton_injective [Encodable α] :
    Function.Injective (singleton : α → RecursiveFinset α) := by
  intro left right equality
  have codeEquality := congrArg codes equality
  simpa [singleton, fromCodes, Encodable.encode_inj] using codeEquality

@[simp]
theorem singleton_eq_singleton [Encodable α] (left right : α) :
    ({left} : RecursiveFinset α) = {right} ↔ left = right :=
  singleton_injective.eq_iff

@[simp]
theorem singleton_ne_empty [Encodable α] (value : α) :
    ({value} : RecursiveFinset α) ≠ ∅ := by
  intro equality
  have codeEquality := congrArg codes equality
  change (singleton value).codes = empty.codes at codeEquality
  change ({Encodable.encode value} : Finset Nat) = ∅ at codeEquality
  simp at codeEquality

@[simp]
theorem empty_ne_singleton [Encodable α] (value : α) :
    (∅ : RecursiveFinset α) ≠ {value} :=
  (singleton_ne_empty value).symm

@[simp]
theorem image_empty [Encodable α] [Encodable β] (function : α → β) :
    image function (∅ : RecursiveFinset α) = ∅ := by
  apply codes_injective
  simp [image, fromCodes]

theorem image_union [Encodable α] [Encodable β]
    (function : α → β) (left right : RecursiveFinset α) :
    image function (left ∪ right) = image function left ∪ image function right := by
  apply codes_injective
  simpa [image, union, fromCodes] using
    (Finset.image_union (f := mapCode function) left.codes right.codes)

@[simp]
theorem image_singleton [Encodable α] [Encodable β]
    (function : α → β) (value : α) :
    image function ({value} : RecursiveFinset α) = {function value} := by
  apply codes_injective
  change Finset.image (mapCode function) {Encodable.encode value} =
    {Encodable.encode (function value)}
  simp [mapCode]

/-- A recursive finite set is valid when all of its stored codes decode as
elements of its phantom element type. Equivalently, decoding and re-encoding
does not change the representation. -/
def Valid [Encodable α] (set : RecursiveFinset α) : Prop :=
  ofFinset (toFinset set) = set

@[simp]
theorem ofFinset_empty [Encodable α] :
    ofFinset (∅ : Finset α) = ∅ := by
  apply codes_injective
  simp [ofFinset, fromCodes]

@[simp]
theorem ofFinset_singleton [Encodable α] (value : α) :
    ofFinset ({value} : Finset α) = {value} := by
  apply codes_injective
  change ({Encodable.encode value} : Finset Nat) = {Encodable.encode value}
  rfl

theorem ofFinset_union [Encodable α] [DecidableEq α]
    (left right : Finset α) :
    ofFinset (left ∪ right) = ofFinset left ∪ ofFinset right := by
  apply codes_injective
  simpa [ofFinset, union, fromCodes] using
    (Finset.image_union (f := Encodable.encode) left right)

@[simp]
theorem toFinset_empty [Encodable α] :
    toFinset (∅ : RecursiveFinset α) = ∅ := by
  rw [← ofFinset_empty (α := α), toFinset_ofFinset]

@[simp]
theorem toFinset_singleton [Encodable α] (value : α) :
    toFinset ({value} : RecursiveFinset α) = {value} := by
  rw [← ofFinset_singleton value, toFinset_ofFinset]

theorem toFinset_union [Encodable α] [DecidableEq α]
    (left right : RecursiveFinset α) :
    toFinset (left ∪ right) = toFinset left ∪ toFinset right := by
  ext value
  simp only [toFinset, Finset.mem_filterMap, codes_union, Finset.mem_union]
  constructor
  · rintro ⟨code, codeInLeftOrRight, decoded⟩
    rcases codeInLeftOrRight with codeInLeft | codeInRight
    · exact Or.inl ⟨code, codeInLeft, decoded⟩
    · exact Or.inr ⟨code, codeInRight, decoded⟩
  · rintro (⟨code, codeInLeft, decoded⟩ | ⟨code, codeInRight, decoded⟩)
    · exact ⟨code, Or.inl codeInLeft, decoded⟩
    · exact ⟨code, Or.inr codeInRight, decoded⟩

@[simp]
theorem valid_empty [Encodable α] :
    Valid (∅ : RecursiveFinset α) := by
  simp [Valid]

@[simp]
theorem valid_singleton [Encodable α] (value : α) :
    Valid ({value} : RecursiveFinset α) := by
  simp [Valid]

theorem Valid.union [Encodable α] {left right : RecursiveFinset α}
    (leftValid : Valid left) (rightValid : Valid right) :
    Valid (left ∪ right) := by
  let _ := Encodable.decidableEqOfEncodable α
  rw [Valid, toFinset_union, ofFinset_union, leftValid, rightValid]

/-- Mapping a genuinely encoded finite set agrees with mapping its decoded
ordinary `Finset`. -/
theorem image_ofFinset [Encodable α] [Encodable β]
    [DecidableEq α] [DecidableEq β]
    (function : α → β) (set : Finset α) :
    image function (ofFinset set) = ofFinset (set.image function) := by
  apply codes_injective
  simp only [image, ofFinset, fromCodes]
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro value valueMembership
  simp [mapCode]

theorem toFinset_image [Encodable α] [Encodable β] [DecidableEq β]
    (function : α → β) {set : RecursiveFinset α}
    (valid : Valid set) :
    toFinset (image function set) = (toFinset set).image function := by
  let _ := Encodable.decidableEqOfEncodable α
  nth_rewrite 1 [← valid]
  rw [image_ofFinset, toFinset_ofFinset]

theorem Valid.image [Encodable α] [Encodable β]
    (function : α → β) {set : RecursiveFinset α}
    (valid : Valid set) :
    Valid (image function set) := by
  let _ := Encodable.decidableEqOfEncodable α
  let _ := Encodable.decidableEqOfEncodable β
  rw [Valid, toFinset_image function valid, ← image_ofFinset, valid]

/-- Every code in a valid recursive finite set decodes to an element. -/
theorem Valid.decode₂_of_mem [Encodable α] {set : RecursiveFinset α}
    (valid : Valid set) {code : Nat} (membership : code ∈ set.codes) :
    ∃ value : α, Encodable.decode₂ α code = some value := by
  have encodedMembership :
      code ∈ (ofFinset (toFinset set)).codes := by
    rw [valid]
    exact membership
  change code ∈ (toFinset set).image Encodable.encode at encodedMembership
  rcases Finset.mem_image.mp encodedMembership with
    ⟨value, _valueMembership, encodingEquality⟩
  subst code
  exact ⟨value, Encodable.decode₂_encode value⟩

theorem union_assoc (left middle right : RecursiveFinset α) :
    (left ∪ middle) ∪ right = left ∪ (middle ∪ right) := by
  apply codes_injective
  exact Finset.union_assoc _ _ _

theorem union_comm (left right : RecursiveFinset α) :
    left ∪ right = right ∪ left := by
  apply codes_injective
  exact Finset.union_comm _ _

theorem union_empty (set : RecursiveFinset α) :
    set ∪ ∅ = set := by
  apply codes_injective
  exact Finset.union_empty _

theorem union_self (set : RecursiveFinset α) :
    set ∪ set = set := by
  apply codes_injective
  exact Finset.union_self _

end RecursiveFinset

end ACUIHE.Solver
