import ACUIHE.Solver.Substitution

/-! Reverse substitution of complete `E` blocks by ordinary variables. -/

namespace ACUIHE

universe u v w

namespace Term

/-- A term belongs to the ACUIh fragment when it contains no `E` operator. -/
def IsACUIh {Const : Type u} {Var : Type v} {Hom : Type w} :
    Term Const Var Hom → Prop
  | .zero => True
  | .const _ => True
  | .var _ => True
  | .add left right => IsACUIh left ∧ IsACUIh right
  | .hom _ body => IsACUIh body
  | .free _ => False

end Term

namespace Solver

/-- The syntactic address of an `E` block in a reified normal form. -/
abbrev EBlockAddress := List Nat

/--
Variables after reverse substitution. An original variable is tagged with
`inl`; a fresh ordinary variable standing for an `E` block is tagged with the
block's syntactic address using `inr`.
-/
abbrev EBlockVariable (Var : Type v) := Sum Var EBlockAddress

/--
An executable check that a normal form belongs to the ACUIh fragment.

Constants, variables, and homomorphism paths are accepted. Encountering any
encoded `E` summand makes the result false.
-/
def isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Bool :=
  normalForm.fold true (fun left right => left && right)
    (fun _ _ => true)
    (fun _ _ => true)
    (fun _ _ => false)

@[simp]
theorem isACUIh_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    isACUIh (∅ : NormalForm Const Var Hom) = true := by
  simp [isACUIh]

@[simp]
theorem isACUIh_constantForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    isACUIh (constantForm (Var := Var) (Hom := Hom) name) = true := by
  simp [isACUIh, constantForm]

@[simp]
theorem isACUIh_variableForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    isACUIh (variableForm (Const := Const) (Hom := Hom) name) = true := by
  simp [isACUIh, variableForm]

@[simp]
theorem isACUIh_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    isACUIh (left ∪ right) = (isACUIh left && isACUIh right) := by
  unfold isACUIh
  apply NormalForm.fold_union
  intro value
  exact Bool.and_true value

@[simp]
theorem isACUIh_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) :
    isACUIh (prefixHom name normalForm) = isACUIh normalForm := by
  unfold isACUIh
  simpa only [id_eq] using
    (NormalForm.fold_prefixHom
      (zero := true)
      (combine := fun left right => left && right)
      (zeroRight := Bool.and_true)
      (onConstant := fun _ _ => true)
      (onVariable := fun _ _ => true)
      (onEOperator := fun _ _ => false)
      name id
      (mapZero := rfl)
      (mapCombine := by intro left right; rfl)
      (mapConstant := by intro path constantName; rfl)
      (mapVariable := by intro path variableName; rfl)
      (mapEOperator := by intro path body; rfl)
      normalForm)

/-- Normalizing an E-free term produces an ACUIh normal form. -/
theorem isACUIh_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) (acuih : term.IsACUIh) :
    isACUIh (normalize term) = true := by
  induction term with
  | zero => exact isACUIh_empty
  | const name => exact isACUIh_constantForm name
  | var name => exact isACUIh_variableForm name
  | add left right leftHypothesis rightHypothesis =>
      rw [normalize_add, isACUIh_union,
        leftHypothesis acuih.1, rightHypothesis acuih.2]
      rfl
  | hom name body inductionHypothesis =>
      rw [normalize_hom, isACUIh_prefixHom,
        inductionHypothesis acuih]
  | free body inductionHypothesis =>
      exact False.elim acuih

/--
The result of replacing every complete `E(body)` by an ordinary variable,
paired with the substitution that expands all those variables again.

The `acuih` field enforces that the resulting normal form is E-free.
-/
structure EBlockReverseSubstitution
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  normalForm : NormalForm Const (EBlockVariable Var) Hom
  substitution : EBlockVariable Var → Term Const Var Hom
  acuih : isACUIh normalForm = true

namespace EBlockReverseSubstitution

/--
Transform the E-free normal form while keeping its restoring substitution
attached.  The caller must prove that the transformed form remains ACUIh.
-/
def mapNormalForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (state : EBlockReverseSubstitution Const Var Hom)
    (transform : NormalForm Const (EBlockVariable Var) Hom →
      NormalForm Const (EBlockVariable Var) Hom)
    (acuih : isACUIh (transform state.normalForm) = true) :
    EBlockReverseSubstitution Const Var Hom where
  normalForm := transform state.normalForm
  substitution := state.substitution
  acuih := acuih

/-- Restore all address variables in a bundled E-free normal form. -/
def restore
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (state : EBlockReverseSubstitution Const Var Hom) :
    NormalForm Const Var Hom :=
  substituteNormalForm state.substitution state.normalForm

/-- Restoring a bundled E-free normal form produces a canonical form. -/
theorem restore_isCanonical
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (state : EBlockReverseSubstitution Const Var Hom) :
    IsCanonical state.restore := by
  unfold restore
  exact substituteNormalForm_isCanonical _ _

@[simp]
theorem mapNormalForm_normalForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (state : EBlockReverseSubstitution Const Var Hom)
    (transform : NormalForm Const (EBlockVariable Var) Hom →
      NormalForm Const (EBlockVariable Var) Hom)
    (acuih : isACUIh (transform state.normalForm) = true) :
    (state.mapNormalForm transform acuih).normalForm =
      transform state.normalForm :=
  rfl

@[simp]
theorem mapNormalForm_substitution
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (state : EBlockReverseSubstitution Const Var Hom)
    (transform : NormalForm Const (EBlockVariable Var) Hom →
      NormalForm Const (EBlockVariable Var) Hom)
    (acuih : isACUIh (transform state.normalForm) = true) :
    (state.mapNormalForm transform acuih).substitution = state.substitution :=
  rfl

@[simp]
theorem restore_mapNormalForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (state : EBlockReverseSubstitution Const Var Hom)
    (transform : NormalForm Const (EBlockVariable Var) Hom →
      NormalForm Const (EBlockVariable Var) Hom)
    (acuih : isACUIh (transform state.normalForm) = true) :
    (state.mapNormalForm transform acuih).restore =
      substituteNormalForm state.substitution (transform state.normalForm) :=
  rfl

end EBlockReverseSubstitution

/-- Follow an E-block address through additions and homomorphisms. -/
private def termAtEBlockAddress
    {Const : Type u} {Var : Type v} {Hom : Type w} :
    EBlockAddress → Term Const Var Hom → Option (Term Const Var Hom)
  | [], term => some term
  | 0 :: rest, .add left _ => termAtEBlockAddress rest left
  | 1 :: rest, .add _ right => termAtEBlockAddress rest right
  | 2 :: rest, .hom _ body => termAtEBlockAddress rest body
  | _ :: _, _ => none

private theorem termAtEBlockAddress_append
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (term : Term Const Var Hom) (start suffix : EBlockAddress) :
    termAtEBlockAddress (start ++ suffix) term =
      (termAtEBlockAddress start term).bind
        (fun selected => termAtEBlockAddress suffix selected) := by
  induction start generalizing term with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      cases term <;> cases step with
      | zero => simp [termAtEBlockAddress, inductionHypothesis]
      | succ step =>
          cases step with
          | zero => simp [termAtEBlockAddress, inductionHypothesis]
          | succ step =>
              cases step with
              | zero => simp [termAtEBlockAddress, inductionHypothesis]
              | succ step => simp [termAtEBlockAddress]

/--
Collect the addresses of the complete `E` blocks that are replaced by
`reverseSubstituteEBlocksTerm`.  Traversal stops at an `E` node because that
whole node becomes one placeholder; nested blocks remain inside its restoring
term and are handled by a later recursive subproblem.
-/
def eBlockAddressesTerm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (address : EBlockAddress) :
    Term Const Var Hom → List EBlockAddress
  | .zero => []
  | .const _ => []
  | .var _ => []
  | .add left right =>
      eBlockAddressesTerm (address ++ [0]) left ++
        eBlockAddressesTerm (address ++ [1]) right
  | .hom _ body => eBlockAddressesTerm (address ++ [2]) body
  | .free _ => [address]

/-- The executable list of outermost complete `E`-block addresses in a
normal form.  These are precisely the blocks processed by one reverse-
substitution/search round. -/
def eBlockAddresses
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) : List EBlockAddress :=
  eBlockAddressesTerm [] (reify target)

/-- Replace every complete `E` node by an ordinary address variable. -/
private def reverseSubstituteEBlocksTerm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (address : EBlockAddress) :
    Term Const Var Hom → Term Const (EBlockVariable Var) Hom
  | .zero => .zero
  | .const name => .const name
  | .var name => .var (.inl name)
  | .add left right =>
      .add
        (reverseSubstituteEBlocksTerm (address ++ [0]) left)
        (reverseSubstituteEBlocksTerm (address ++ [1]) right)
  | .hom name body =>
      .hom name (reverseSubstituteEBlocksTerm (address ++ [2]) body)
  | .free _ => .var (.inr address)

private theorem reverseSubstituteEBlocksTerm_isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (address : EBlockAddress) (term : Term Const Var Hom) :
    (reverseSubstituteEBlocksTerm address term).IsACUIh := by
  induction term generalizing address <;>
    simp [reverseSubstituteEBlocksTerm, Term.IsACUIh, *]

/--
The substitution accompanying complete E-block reverse substitution.
Original variables are unchanged; every address variable expands to the
complete `E(body)` occurring at that address in `target`.
-/
def restoreEBlockSubstitution
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    EBlockVariable Var → Term Const Var Hom
  | .inl name => .var name
  | .inr address =>
      match termAtEBlockAddress address (reify target) with
      | some (.free body) => .free body
      | _ => .zero

private theorem substitute_reverseSubstituteEBlocksTerm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (root term : Term Const Var Hom) (address : EBlockAddress)
    (located : termAtEBlockAddress address root = some term) :
    Term.substitute
        (fun sourceVariable =>
          match sourceVariable with
          | .inl name => .var name
          | .inr blockAddress =>
              match termAtEBlockAddress blockAddress root with
              | some (.free body) => .free body
              | _ => .zero)
        (reverseSubstituteEBlocksTerm address term) =
      term := by
  induction term generalizing address with
  | zero => rfl
  | const name => rfl
  | var name => rfl
  | add left right leftHypothesis rightHypothesis =>
      simp only [reverseSubstituteEBlocksTerm, Term.substitute_add]
      rw [leftHypothesis (address ++ [0]),
        rightHypothesis (address ++ [1])]
      · rw [termAtEBlockAddress_append, located]
        rfl
      · rw [termAtEBlockAddress_append, located]
        rfl
  | hom name body inductionHypothesis =>
      simp only [reverseSubstituteEBlocksTerm, Term.substitute_hom]
      rw [inductionHypothesis (address ++ [2])]
      rw [termAtEBlockAddress_append, located]
      rfl
  | free body inductionHypothesis =>
      simp only [reverseSubstituteEBlocksTerm, Term.substitute_var]
      rw [located]

/--
Replace every complete `E(body)` in `target` by an ordinary variable and
return the single substitution that restores all original E-blocks.

Nested E-blocks are retained inside the restoring value for their outermost
block; the transformed normal form itself contains no `E` operator.
-/
def reverseSubstituteEBlocks
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    EBlockReverseSubstitution Const Var Hom where
  normalForm :=
    normalize (reverseSubstituteEBlocksTerm [] (reify target))
  substitution := restoreEBlockSubstitution target
  acuih :=
    isACUIh_normalize _
      (reverseSubstituteEBlocksTerm_isACUIh [] (reify target))

@[simp]
theorem reverseSubstituteEBlocks_empty_normalForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    (reverseSubstituteEBlocks
      (∅ : NormalForm Const Var Hom)).normalForm = ∅ := by
  unfold reverseSubstituteEBlocks
  dsimp only
  have reifyEmpty :
      reify (∅ : NormalForm Const Var Hom) = .zero := by
    simp [reify]
  rw [reifyEmpty]
  rfl

@[simp]
theorem reverseSubstituteEBlocks_constantForm_normalForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    (reverseSubstituteEBlocks
      (constantForm (Var := Var) (Hom := Hom) name)).normalForm =
        constantForm (Var := EBlockVariable Var) (Hom := Hom) name := by
  unfold reverseSubstituteEBlocks
  dsimp only
  have reifyConstant :
      reify (constantForm (Var := Var) (Hom := Hom) name) =
        .add (.const name) .zero := by
    unfold reify constantForm
    rw [NormalForm.fold_singleton]
    rfl
  rw [reifyConstant]
  simp only [reverseSubstituteEBlocksTerm, normalize_add, normalize_const,
    normalize_zero]
  exact ACUIhE.add_zero (Hom := Hom) _

@[simp]
theorem reverseSubstituteEBlocks_variableForm_normalForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    (reverseSubstituteEBlocks
      (variableForm (Const := Const) (Hom := Hom) name)).normalForm =
        variableForm (Const := Const) (Hom := Hom) (.inl name) := by
  unfold reverseSubstituteEBlocks
  dsimp only
  have reifyVariable :
      reify (variableForm (Const := Const) (Hom := Hom) name) =
        .add (.var name) .zero := by
    unfold reify variableForm
    rw [NormalForm.fold_singleton]
    rfl
  rw [reifyVariable]
  simp only [reverseSubstituteEBlocksTerm, normalize_add, normalize_var,
    normalize_zero]
  exact ACUIhE.add_zero (Hom := Hom) _

@[simp]
theorem reverseSubstituteEBlocks_wrapE_normalForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (body : NormalForm Const Var Hom) (bodyNonempty : body ≠ ∅) :
    (reverseSubstituteEBlocks (wrapE body)).normalForm =
      variableForm
        (Const := Const) (Hom := Hom)
        (.inr ([0] : EBlockAddress)) := by
  unfold reverseSubstituteEBlocks
  dsimp only
  have reifyWrapped :
      reify (wrapE body) = .add (.free (reify body)) .zero := by
    rw [wrapE_of_ne_empty bodyNonempty]
    unfold reify
    rw [NormalForm.fold_singleton]
    rfl
  rw [reifyWrapped]
  simp only [reverseSubstituteEBlocksTerm, normalize_add, normalize_var,
    normalize_zero]
  exact ACUIhE.add_zero (Hom := Hom) _

/-- Reverse substitution always produces an ACUIh normal form. -/
theorem reverseSubstituteEBlocks_isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    isACUIh (reverseSubstituteEBlocks target).normalForm = true :=
  (reverseSubstituteEBlocks target).acuih

/--
Applying the accompanying substitution recovers the canonicalization of the
original target.
-/
theorem reverseSubstituteEBlocks_roundtrip
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    (reverseSubstituteEBlocks target).restore = canonicalize target := by
  unfold EBlockReverseSubstitution.restore reverseSubstituteEBlocks
  dsimp only
  rw [substituteNormalForm_normalize]
  unfold restoreEBlockSubstitution
  rw [substitute_reverseSubstituteEBlocksTerm
    (reify target) (reify target) []]
  · rfl
  · rfl

/-- For a canonical target, the accompanying substitution recovers the target
itself. -/
theorem reverseSubstituteEBlocks_roundtrip_of_canonical
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) (canonical : IsCanonical target) :
    (reverseSubstituteEBlocks target).restore = target := by
  rw [reverseSubstituteEBlocks_roundtrip target]
  exact canonical

end Solver

end ACUIHE
