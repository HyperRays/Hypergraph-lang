import ACUIHE.Soundness
import ACUIHE.NormalForm.Internal

/-! Core definitions and operations for abstract ACUIhE normal forms. -/

namespace ACUIHE.Solver

open NormalForm.Internal

universe u v w x

/--
The representation of an intrinsically valid normal form.

The raw encoded form and its recursive validity proof are public so that
specialized algorithms may inspect or construct the representation directly.
-/
structure NormalFormImpl
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  raw : RawNormalForm Const Var Hom
  valid : RecursivelyValid raw

/--
A completely valid normal form.

This convenient public name aliases `NormalFormImpl`.  Its constructor,
`raw` and `valid` projections, and recursor are publicly accessible alongside
the semantic API below.
-/
abbrev NormalForm (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] :=
  NormalFormImpl Const Var Hom

/-- Two normal forms with equal raw representations are equal. -/
theorem NormalForm.ext_raw
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (equality : left.raw = right.raw) : left = right := by
  rcases left with ⟨leftRaw, leftValid⟩
  rcases right with ⟨rightRaw, rightValid⟩
  dsimp only at equality
  subst rightRaw
  rfl

instance {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    DecidableEq (NormalForm Const Var Hom) := fun left right =>
  if equality : left.raw = right.raw then
    isTrue (NormalForm.ext_raw equality)
  else
    isFalse fun formsEqual => equality
      (congrArg (fun normalForm => normalForm.raw) formsEqual)

/-- A semantic atom: an `E` body is itself an abstract, recursively valid form. -/
inductive NormalAtom (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  | constant (name : Const)
  | variable (name : Var)
  | eOperator (body : NormalForm Const Var Hom)

/-- A homomorphism path paired with a semantic atom. -/
abbrev NormalSummand (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] :=
  List Hom × NormalAtom Const Var Hom

private def NormalAtom.toRaw
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    NormalAtom Const Var Hom → RawNormalAtom Const Var Hom
  | .constant name => .constant name
  | .variable name => .variable name
  | .eOperator body => .eOperator body.raw

private def NormalSummand.toRaw
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (summand : NormalSummand Const Var Hom) :
    RawNormalSummand Const Var Hom :=
  (summand.1, summand.2.toRaw)

private theorem NormalAtom.toRaw_valid
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (atom : NormalAtom Const Var Hom) :
    RecursivelyValidAtom atom.toRaw := by
  rcases atom with name | name | body
  · exact ValidNode.constant name
  · exact ValidNode.variable name
  · exact ValidNode.eOperator body.valid

def NormalForm.empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    NormalForm Const Var Hom :=
  ⟨∅, recursivelyValid_empty⟩

instance {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    EmptyCollection (NormalForm Const Var Hom) :=
  ⟨NormalForm.empty⟩

instance {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Zero (NormalForm Const Var Hom) :=
  ⟨NormalForm.empty⟩

/-- Construct a singleton from one semantic summand. -/
def NormalForm.singleton
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (summand : NormalSummand Const Var Hom) :
    NormalForm Const Var Hom :=
  ⟨{summand.toRaw},
    recursivelyValid_singleton summand.toRaw summand.2.toRaw_valid⟩

instance {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Singleton (NormalSummand Const Var Hom) (NormalForm Const Var Hom) :=
  ⟨NormalForm.singleton⟩

/-- Union of abstract normal forms. -/
def NormalForm.union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    NormalForm Const Var Hom :=
  ⟨left.raw ∪ right.raw, recursivelyValid_union left.valid right.valid⟩

instance {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Union (NormalForm Const Var Hom) :=
  ⟨NormalForm.union⟩

instance {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Add (NormalForm Const Var Hom) :=
  ⟨NormalForm.union⟩

/--
The semantic eliminator for abstract normal forms.  This is the only operation
that traverses a form; callers receive constants, variables, paths, and the
already-folded result of an `E` body, never encoded storage.
-/
def NormalForm.fold
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (normalForm : NormalForm Const Var Hom) : Result :=
  rawFold zero combine onConstant onVariable onEOperator normalForm.raw

@[simp]
theorem NormalForm.fold_empty
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result) :
    NormalForm.fold zero combine onConstant onVariable onEOperator
      (∅ : NormalForm Const Var Hom) = zero := by
  exact rawFold_empty zero combine onConstant onVariable onEOperator

@[simp]
theorem NormalForm.fold_singleton
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (summand : NormalSummand Const Var Hom) :
    NormalForm.fold zero combine onConstant onVariable onEOperator
        ({summand} : NormalForm Const Var Hom) =
      combine
        (match summand with
        | (path, .constant name) => onConstant path name
        | (path, .variable name) => onVariable path name
        | (path, .eOperator body) =>
            onEOperator path
              (NormalForm.fold zero combine onConstant onVariable onEOperator body))
        zero := by
  unfold NormalForm.fold
  change rawFold zero combine onConstant onVariable
      onEOperator ({summand.toRaw} : RawNormalForm Const Var Hom) = _
  rw [rawFold_singleton]
  rcases summand with ⟨path, atom⟩
  rcases atom with name | name | body <;> rfl

/-- Folding union requires no public validity premise: validity is intrinsic. -/
theorem NormalForm.fold_union
    {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (zero : Result) (combine : Result → Result → Result)
    [Std.Commutative combine] [Std.Associative combine]
    [Std.IdempotentOp combine]
    (zeroRight : ∀ value, combine value zero = value)
    (onConstant : List Hom → Const → Result)
    (onVariable : List Hom → Var → Result)
    (onEOperator : List Hom → Result → Result)
    (left right : NormalForm Const Var Hom) :
    NormalForm.fold zero combine onConstant onVariable onEOperator
        (left ∪ right) =
      combine
        (NormalForm.fold zero combine onConstant onVariable onEOperator left)
        (NormalForm.fold zero combine onConstant onVariable onEOperator right) := by
  exact rawFold_union zero combine zeroRight onConstant
    onVariable onEOperator left.raw right.raw

/-- A handler-preserving map commutes with the public semantic fold. -/
theorem NormalForm.fold_hom
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
    (normalForm : NormalForm Const Var Hom) :
    map
        (NormalForm.fold sourceZero sourceCombine sourceConstant sourceVariable
          sourceEOperator normalForm) =
      NormalForm.fold targetZero targetCombine targetConstant targetVariable
        targetEOperator normalForm := by
  exact rawFold_hom map sourceZero sourceCombine sourceConstant sourceVariable
    sourceEOperator targetZero targetCombine targetConstant targetVariable
    targetEOperator mapZero mapCombine mapConstant mapVariable mapEOperator
    normalForm.raw

/-- Insert a named homomorphism at the front of every semantic path. -/
def prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) :
    NormalForm Const Var Hom :=
  ⟨rawPrefixHom name normalForm.raw,
    recursivelyValid_prefixHom name normalForm.valid⟩

/--
Wrap a nonzero abstract normal form in `E`.  Accepting an abstract body makes
recursive validity structural: an invalid `E` body cannot be supplied.
-/
def wrapE
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (body : NormalForm Const Var Hom) : NormalForm Const Var Hom :=
  ⟨rawWrapE body.raw, recursivelyValid_wrapE body.valid⟩

/-- Prefixing distributes over union. -/
theorem prefixHom_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (left right : NormalForm Const Var Hom) :
    prefixHom name (left ∪ right) = prefixHom name left ∪ prefixHom name right := by
  apply NormalForm.ext_raw
  exact rawPrefixHom_union name left.raw right.raw

@[simp]
theorem prefixHom_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) :
    prefixHom (Const := Const) (Var := Var) name ∅ = ∅ := by
  apply NormalForm.ext_raw
  exact rawPrefixHom_empty name

@[simp]
theorem wrapE_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    wrapE (Const := Const) (Var := Var) (Hom := Hom) ∅ = ∅ := by
  apply NormalForm.ext_raw
  exact rawWrapE_empty

/-- A nonempty form is represented by one semantic `E` summand after wrapping. -/
theorem wrapE_of_ne_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {body : NormalForm Const Var Hom} (bodyNonempty : body ≠ ∅) :
    wrapE body = {([], .eOperator body)} := by
  have rawNonempty : body.raw ≠ ∅ := by
    intro rawEmpty
    apply bodyNonempty
    apply NormalForm.ext_raw
    exact rawEmpty
  apply NormalForm.ext_raw
  change rawWrapE body.raw =
    ({([], rawEAtom body.raw)} : RawNormalForm Const Var Hom)
  rw [rawWrapE, if_neg rawNonempty]

theorem wrapE_injective
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Function.Injective
      (wrapE (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro left right equality
  apply NormalForm.ext_raw
  apply rawWrapE_injective
  exact congrArg (fun normalForm => normalForm.raw) equality

/--
Folding through a prefixed form needs no validity argument.  The private proof
stored in `normalForm` discharges the raw representation theorem internally.
-/
theorem NormalForm.fold_prefixHom
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
    (normalForm : NormalForm Const Var Hom) :
    NormalForm.fold zero combine onConstant onVariable onEOperator
        (prefixHom name normalForm) =
      mapResult
        (NormalForm.fold zero combine onConstant onVariable onEOperator
          normalForm) := by
  exact rawFold_prefixHom zero combine zeroRight
    onConstant onVariable onEOperator name mapResult mapZero mapCombine
    mapConstant mapVariable mapEOperator normalForm.valid.outer

/-- Abstract normal forms themselves form an ACUIhE algebra. -/
instance {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    ACUIhE Hom (NormalForm Const Var Hom) where
  hom := prefixHom
  free := wrapE
  add_assoc := by
    intro left middle right
    apply NormalForm.ext_raw
    exact rawUnion_assoc left.raw middle.raw right.raw
  add_comm := by
    intro left right
    apply NormalForm.ext_raw
    exact rawUnion_comm left.raw right.raw
  add_zero := by
    intro normalForm
    apply NormalForm.ext_raw
    exact rawUnion_empty normalForm.raw
  add_idem := by
    intro normalForm
    apply NormalForm.ext_raw
    exact rawUnion_self normalForm.raw
  hom_add := prefixHom_union
  hom_zero := prefixHom_empty
  free_zero := wrapE_empty
  free_injective := wrapE_injective

/-- Embed a constant as a singleton abstract normal form. -/
def constantForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) : NormalForm Const Var Hom :=
  {([], .constant name)}

/-- Embed a variable as a singleton abstract normal form. -/
def variableForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) : NormalForm Const Var Hom :=
  {([], .variable name)}

/-- Normalize by evaluation in the intrinsically valid normal-form algebra. -/
def normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Term Const Var Hom → NormalForm Const Var Hom :=
  Term.eval constantForm variableForm

@[simp]
theorem normalize_zero
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    normalize (.zero : Term Const Var Hom) = ∅ := rfl

@[simp]
theorem normalize_const
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    normalize (.const name : Term Const Var Hom) = constantForm name := rfl

@[simp]
theorem normalize_var
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    normalize (.var name : Term Const Var Hom) = variableForm name := rfl

@[simp]
theorem normalize_add
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : Term Const Var Hom) :
    normalize (.add left right) = normalize left ∪ normalize right := rfl

@[simp]
theorem normalize_hom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (body : Term Const Var Hom) :
    normalize (.hom name body) = prefixHom name (normalize body) := rfl

@[simp]
theorem normalize_free
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (body : Term Const Var Hom) :
    normalize (.free body) = wrapE (normalize body) := rfl

/-- Rebuild homomorphism paths without exposing the representation. -/
def reifyPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (path : List Hom) (body : Term Const Var Hom) : Term Const Var Hom :=
  path.foldr (fun name inner => .hom name inner) body

/-- Reify entirely through the semantic fold interface. -/
def reify
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Term Const Var Hom :=
  normalForm.fold
    .zero
    .add
    (fun path name => reifyPath path (.const name))
    (fun path name => reifyPath path (.var name))
    (fun path body => reifyPath path (.free body))

/-- Every derivable equality has identical abstract normal forms. -/
theorem normalize_eq_of_derives
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : Term Const Var Hom} (derivation : Derives left right) :
    normalize left = normalize right :=
  derivation.sound constantForm variableForm

end ACUIHE.Solver
