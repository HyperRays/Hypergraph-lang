import ACUIHE.ACUIh
import ACUIHE.Solver.Substitution

/-!
Abstraction of complete `E` atoms into alien constants and expansion of those
constants back into terms. The caller supplies body classifications and
replacement values; this module does not depend on search configurations,
matrices, or the enumeration of input occurrences.

Abstraction preserves homomorphism prefixes and original variables. A body
classified as `none` contributes zero, so arbitrary classifications do not
have an unconditional round trip. Solver-specific reconstruction establishes
the required relationship for valid, solved configurations.
-/

namespace ACUIHE.Solver

open NormalForm.Internal

universe u v w x

local instance {Alpha : Type*} [Encodable Alpha] : DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

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

private theorem normalUnionEmpty
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (value : NormalForm Const Var Hom) : value ∪ ∅ = value := by
  apply NormalForm.ext_raw
  exact rawUnion_empty value.raw

/-- One alien atom under its original homomorphism path. An absent class
contributes zero. This handler is shared by execution and the proof folds. -/
def alienConstantAtPath
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom] [Encodable Alien]
    (path : List Hom) (representative : Option Alien) :
    NormalForm (Const ⊕ Alien) Var Hom :=
  match representative with
  | none => ∅
  | some name => {(path, .constant (.inr name))}

@[simp]
theorem alienConstantAtPath_none
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom] [Encodable Alien]
    (path : List Hom) :
    alienConstantAtPath (Const := Const) (Var := Var) (Alien := Alien) path none = ∅ := rfl

@[simp]
theorem alienConstantAtPath_some
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom] [Encodable Alien]
    (path : List Hom) (name : Alien) :
    alienConstantAtPath (Const := Const) (Var := Var) path (some name) =
      {(path, .constant (.inr name))} := rfl

@[simp]
theorem alienConstantAtPath_isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom] [Encodable Alien]
    (path : List Hom) (representative : Option Alien) :
    isACUIh (alienConstantAtPath (Const := Const) (Var := Var) path representative) = true := by
  cases representative <;> simp [alienConstantAtPath, isACUIh]

/-- A body-aware fold rebuilds the source normal form alongside its purified
E-free image.  The proof field makes E-freeness intrinsic to construction. -/
structure EPurificationScan
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (Basis : Type x) [Encodable Basis] where
  source : NormalForm Const Var Hom
  purified : NormalForm Basis Var Hom
  acuih : isACUIh purified = true

/-- Replace complete `E` atoms by alien constants selected from their bodies.
`none` replaces the atom by zero. Original variables and all surrounding
homomorphism paths are preserved; nested bodies are rebuilt for lookup but
their projected images are discarded when replacing the enclosing atom. -/
def substituteEBlocksScan
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom] [Encodable Alien]
    (classOfBody : NormalForm Const Var Hom → Option Alien)
    (target : NormalForm Const Var Hom) :
    EPurificationScan Const Var Hom (Const ⊕ Alien) :=
  target.fold
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
    (fun path scannedBody =>
      let purified : NormalForm (Const ⊕ Alien) Var Hom :=
        alienConstantAtPath path (classOfBody scannedBody.source)
      ⟨{(path, .eOperator scannedBody.source)}, purified, by
        exact alienConstantAtPath_isACUIh _ _⟩)

/-- The alien image of a normal form is always E-free. -/
def substituteEBlocks
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom] [Encodable Alien]
    (classOfBody : NormalForm Const Var Hom → Option Alien)
    (target : NormalForm Const Var Hom) : NormalForm (Const ⊕ Alien) Var Hom :=
  (substituteEBlocksScan classOfBody target).purified

@[simp]
theorem substituteEBlocks_isACUIh
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom] [Encodable Alien]
    (classOfBody : NormalForm Const Var Hom → Option Alien)
    (target : NormalForm Const Var Hom) :
    isACUIh (substituteEBlocks classOfBody target) = true :=
  (substituteEBlocksScan classOfBody target).acuih

/-- Ground projection with the source retained alongside its alien image.
The caller chooses which ground bodies have representatives; unmatched atoms
are discarded. This is the pair-valued traversal used in completeness. -/
def projectEBlocksPair
    {Const : Type u} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Hom] [Encodable Alien]
    (classOfBody : NormalForm Const (Fin 0) Hom → Option Alien)
    (target : NormalForm Const (Fin 0) Hom) :
    NormalForm Const (Fin 0) Hom × NormalForm (Const ⊕ Alien) (Fin 0) Hom :=
  target.fold
    (∅, ∅)
    (fun first second => (first.1 ∪ second.1, first.2 ∪ second.2))
    (fun path name =>
      ({(path, .constant name)}, {(path, .constant (.inl name))}))
    (fun _ impossible => impossible.elim0)
    (fun path body =>
      let original : NormalForm Const (Fin 0) Hom :=
        {(path, .eOperator body.1)}
      let projected : NormalForm
          (Const ⊕ Alien) (Fin 0) Hom :=
        alienConstantAtPath path (classOfBody body.1)
      (original, projected))

/-- The pair-valued ground projection agrees with the production scan. -/
theorem projectEBlocksPair_eq_scan
    {Const : Type u} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Hom] [Encodable Alien]
    (classOfBody : NormalForm Const (Fin 0) Hom → Option Alien)
    (target : NormalForm Const (Fin 0) Hom) :
    projectEBlocksPair classOfBody target =
      let result := substituteEBlocksScan classOfBody target
      (result.source, result.purified) := by
  symm
  change (fun result : EPurificationScan Const (Fin 0) Hom (Const ⊕ Alien) =>
    (result.source, result.purified)) (substituteEBlocksScan classOfBody target) = _
  unfold substituteEBlocksScan projectEBlocksPair
  apply NormalForm.fold_hom
    (fun result : EPurificationScan Const (Fin 0) Hom (Const ⊕ Alien) =>
      (result.source, result.purified))
  · rfl
  · intro first second; rfl
  · intro path name; rfl
  · intro path impossible; exact impossible.elim0
  · intro path body; rfl

/-- Replace abstract basis constants in a ground term. -/
def replaceBasisConstants
    {Basis : Type u} {Const : Type v} {Hom : Type w}
    (replacement : Basis → Term Const (Fin 0) Hom) :
    Term Basis (Fin 0) Hom → Term Const (Fin 0) Hom
  | .zero => .zero
  | .const name => replacement name
  | .var impossible => impossible.elim0
  | .add left right =>
      .add (replaceBasisConstants replacement left)
        (replaceBasisConstants replacement right)
  | .hom name body => .hom name (replaceBasisConstants replacement body)
  | .free body => .free (replaceBasisConstants replacement body)

/-- Abstract every constant of a ground term into a variable. Since the
result has no constants, its constant type can be chosen independently. -/
def abstractBasisConstants
    {Basis : Type u} {Const : Type v} {Hom : Type w} :
    Term Basis (Fin 0) Hom → Term Const Basis Hom
  | .zero => .zero
  | .const name => .var name
  | .var impossible => impossible.elim0
  | .add left right => .add (abstractBasisConstants left) (abstractBasisConstants right)
  | .hom name body => .hom name (abstractBasisConstants body)
  | .free body => .free (abstractBasisConstants body)

/-- Direct constant expansion is exactly constant abstraction followed by
ordinary heterogeneous variable substitution. -/
theorem replaceBasisConstants_eq_substitute
    {Basis : Type u} {Const : Type v} {Hom : Type w}
    (replacement : Basis → Term Const (Fin 0) Hom)
    (term : Term Basis (Fin 0) Hom) :
    replaceBasisConstants replacement term =
      Term.substitute replacement (abstractBasisConstants term) := by
  induction term with
  | var impossible => exact impossible.elim0
  | _ => simp_all [replaceBasisConstants, abstractBasisConstants]

/-- Replacing basis constants by arbitrary ground terms preserves every
ACUIhE derivation. -/
theorem replaceBasisConstants_respectsDerives
    {Basis : Type u} {Const : Type v} {Hom : Type w}
    (replacement : Basis → Term Const (Fin 0) Hom)
    {left right : Term Basis (Fin 0) Hom}
    (derivation : Derives left right) :
    Derives (replaceBasisConstants replacement left)
      (replaceBasisConstants replacement right) := by
  induction derivation with
  | refl term => exact Derives.refl _
  | symm derivation inductionHypothesis =>
      exact Derives.symm inductionHypothesis
  | trans leftDerivation rightDerivation leftHypothesis rightHypothesis =>
      exact Derives.trans leftHypothesis rightHypothesis
  | add_congr leftDerivation rightDerivation leftHypothesis rightHypothesis =>
      exact Derives.add_congr leftHypothesis rightHypothesis
  | hom_congr name derivation inductionHypothesis =>
      exact Derives.hom_congr name inductionHypothesis
  | free_congr derivation inductionHypothesis =>
      exact Derives.free_congr inductionHypothesis
  | free_inj derivation inductionHypothesis =>
      exact Derives.free_inj inductionHypothesis
  | add_assoc first middle last => exact Derives.add_assoc _ _ _
  | add_comm first second => exact Derives.add_comm _ _
  | add_zero term => exact Derives.add_zero _
  | add_idem term => exact Derives.add_idem _
  | hom_add name first second => exact Derives.hom_add name _ _
  | hom_zero name => exact Derives.hom_zero name
  | free_zero => exact Derives.free_zero

/-- Replacing constants before or after canonical ACUIhE normalization gives
the same target normal form. -/
theorem normalize_replaceBasisConstants_reify_normalize
    {Basis : Type u} {Const : Type v} {Hom : Type w}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (term : Term Basis (Fin 0) Hom) :
    normalize (replaceBasisConstants replacement term) =
      normalize
        (replaceBasisConstants replacement (reify (normalize term))) := by
  apply normalize_eq_of_derives
  exact replaceBasisConstants_respectsDerives replacement
    (derives_reify_normalize term)

/-- Prefix an entire homomorphism path to a normal form. -/
def prefixHomPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (target : NormalForm Const Var Hom) :
    NormalForm Const Var Hom :=
  path.foldr prefixHom target

/-- Evaluate a ground normal form after interpreting each of its constants by
an arbitrary ground term. -/
def expandNormalForm
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (target : NormalForm Basis (Fin 0) Hom) :
    NormalForm Const (Fin 0) Hom :=
  target.fold ∅ (· ∪ ·)
    (fun path basis => prefixHomPath path (normalize (replacement basis)))
    (fun _ impossible => impossible.elim0)
    (fun path body => prefixHomPath path (wrapE body))

theorem expandNormalForm_union
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (first second : NormalForm Basis (Fin 0) Hom) :
    expandNormalForm replacement (first ∪ second) =
      expandNormalForm replacement first ∪
        expandNormalForm replacement second := by
  unfold expandNormalForm
  apply NormalForm.fold_union
  exact normalUnionEmpty

theorem expandNormalForm_prefixHom
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (name : Hom) (target : NormalForm Basis (Fin 0) Hom) :
    expandNormalForm replacement (prefixHom name target) =
      prefixHom name (expandNormalForm replacement target) := by
  unfold expandNormalForm
  apply NormalForm.fold_prefixHom
      (zeroRight := normalUnionEmpty)
      (mapResult := prefixHom name)
  · exact prefixHom_empty name
  · exact prefixHom_union name
  · intro path basis
    rfl
  · intro path impossible
    exact impossible.elim0
  · intro path body
    rfl

theorem expandNormalForm_prefixHomPath
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (path : List Hom) (target : NormalForm Basis (Fin 0) Hom) :
    expandNormalForm replacement (prefixHomPath path target) =
      prefixHomPath path (expandNormalForm replacement target) := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      change expandNormalForm replacement
          (prefixHom name (prefixHomPath path target)) = _
      rw [expandNormalForm_prefixHom, inductionHypothesis]
      rfl

@[simp]
theorem expandNormalForm_empty
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom) :
    expandNormalForm replacement (∅ : NormalForm Basis (Fin 0) Hom) = ∅ := by
  simp [expandNormalForm]

@[simp]
theorem expandNormalForm_singleton_constant
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (path : List Hom) (basis : Basis) :
    expandNormalForm replacement
        ({(path, .constant basis)} : NormalForm Basis (Fin 0) Hom) =
      prefixHomPath path (normalize (replacement basis)) := by
  unfold expandNormalForm
  rw [NormalForm.fold_singleton]
  exact normalUnionEmpty _

theorem normalize_replaceBasisConstants_reifyPath
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (path : List Hom) (term : Term Basis (Fin 0) Hom) :
    normalize (replaceBasisConstants replacement (reifyPath path term)) =
      prefixHomPath path
        (normalize (replaceBasisConstants replacement term)) := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      simp only [reifyPath, List.foldr_cons, replaceBasisConstants,
        normalize_hom, prefixHomPath]
      exact congrArg (prefixHom name) inductionHypothesis

/-- The fold evaluator is exactly normalized term-level replacement. -/
theorem expandNormalForm_eq_normalize_replaceBasisConstants
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (target : NormalForm Basis (Fin 0) Hom) :
    expandNormalForm replacement target =
      normalize (replaceBasisConstants replacement (reify target)) := by
  unfold expandNormalForm reify
  symm
  apply NormalForm.fold_hom
    (fun term : Term Basis (Fin 0) Hom =>
      normalize (replaceBasisConstants replacement term))
    (.zero : Term Basis (Fin 0) Hom) (.add)
    (fun path basis => reifyPath path (.const basis))
    (fun path impossible => reifyPath path (.var impossible))
    (fun path body => reifyPath path (.free body))
    (∅ : NormalForm Const (Fin 0) Hom) (· ∪ ·)
    (fun path basis => prefixHomPath path (normalize (replacement basis)))
    (fun _ impossible => impossible.elim0)
    (fun path body => prefixHomPath path (wrapE body))
    (by rfl)
    (by intro first second; simp [replaceBasisConstants])
    (by
      intro path basis
      rw [normalize_replaceBasisConstants_reifyPath]
      rfl)
    (by intro path impossible; exact impossible.elim0)
    (by
      intro path body
      rw [normalize_replaceBasisConstants_reifyPath]
      rfl)
    target

theorem expandNormalForm_canonicalize
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (target : NormalForm Basis (Fin 0) Hom) :
    expandNormalForm replacement (canonicalize target) =
      expandNormalForm replacement target := by
  rw [expandNormalForm_eq_normalize_replaceBasisConstants,
    expandNormalForm_eq_normalize_replaceBasisConstants]
  exact (normalize_replaceBasisConstants_reify_normalize
    replacement (reify target)).symm

/-- Normal-form expansion is also ordinary substitution after abstracting
the source constants into variables of the source basis type. -/
theorem expandNormalForm_eq_substituteNormalForm
    {Basis Const Hom : Type u}
    [Encodable Basis] [Encodable Const] [Encodable Hom]
    (replacement : Basis → Term Const (Fin 0) Hom)
    (target : NormalForm Basis (Fin 0) Hom) :
    expandNormalForm replacement target =
      substituteNormalForm replacement
        (normalize (abstractBasisConstants (reify target))) := by
  rw [substituteNormalForm_normalize,
    ← replaceBasisConstants_eq_substitute,
    expandNormalForm_eq_normalize_replaceBasisConstants]

end ACUIHE.Solver
