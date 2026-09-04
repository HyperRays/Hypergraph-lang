import ACUIHE.NormalForm.Canonical

/-! Transport between transformations of terms and transformations of normal forms. -/

namespace ACUIHE.Solver

universe u v w x

/-- A term transformation respects the equational theory. -/
def RespectsDerives
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom) : Prop :=
  ∀ ⦃left right⦄, Derives left right → Derives (function left) (function right)

/-- A normal-form transformation sends canonical forms to canonical forms. -/
def PreservesCanonical
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom) : Prop :=
  ∀ ⦃normalForm⦄, IsCanonical normalForm → IsCanonical (function normalForm)

/-- Descend a term transformation to normal forms through reification. -/
def induce
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom)
    (normalForm : NormalForm Const SourceVar Hom) :
    NormalForm Const TargetVar Hom :=
  normalize (function (reify normalForm))

/-- Realize a normal-form transformation as a transformation of raw terms. -/
def realize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom)
    (term : Term Const SourceVar Hom) : Term Const TargetVar Hom :=
  reify (function (normalize term))

/-- Inducing commutes with normalization for derivation-respecting maps. -/
theorem induce_normalize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom)
    (respects : RespectsDerives function) (term : Term Const SourceVar Hom) :
    induce function (normalize term) = normalize (function term) := by
  unfold induce
  apply normalize_eq_of_derives
  exact (respects (derives_reify_normalize term)).symm

/-- Respecting derivability is equivalent to commuting with normalization. -/
theorem respectsDerives_iff_induce_normalize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom) :
    RespectsDerives function ↔
      ∀ term, induce function (normalize term) = normalize (function term) := by
  constructor
  · intro respects term
    exact induce_normalize function respects term
  · intro commutes left right derivation
    apply derives_of_normalize_eq
    calc
      normalize (function left) = induce function (normalize left) :=
        (commutes left).symm
      _ = induce function (normalize right) :=
        congrArg (induce function) (normalize_eq_of_derives derivation)
      _ = normalize (function right) := commutes right

/-- Normalizing a realized map canonicalizes its result. -/
@[simp]
theorem normalize_realize_canonicalize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom)
    (term : Term Const SourceVar Hom) :
    normalize (realize function term) = canonicalize (function (normalize term)) :=
  rfl

/-- Realization commutes with normalization for canonicality-preserving maps. -/
theorem normalize_realize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom)
    (preserves : PreservesCanonical function)
    (term : Term Const SourceVar Hom) :
    normalize (realize function term) = function (normalize term) := by
  rw [normalize_realize_canonicalize]
  exact preserves (canonicalize_normalize term)

/-- Preserving canonical forms is equivalent to realization commuting with normalization. -/
theorem preservesCanonical_iff_normalize_realize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom) :
    PreservesCanonical function ↔
      ∀ term, normalize (realize function term) = function (normalize term) := by
  constructor
  · intro preserves term
    exact normalize_realize function preserves term
  · intro commutes normalForm canonical
    unfold IsCanonical
    have equality := commutes (reify normalForm)
    rw [normalize_realize_canonicalize] at equality
    change canonicalize (function (canonicalize normalForm)) =
      function (canonicalize normalForm) at equality
    rw [canonical] at equality
    exact equality

/-- Inducing a realized map canonicalizes both its input and output. -/
@[simp]
theorem induce_realize_canonicalize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom)
    (normalForm : NormalForm Const SourceVar Hom) :
    induce (realize function) normalForm =
      canonicalize (function (canonicalize normalForm)) :=
  rfl

theorem realize_induce_eq_reify_normalize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom)
    (respects : RespectsDerives function)
    (term : Term Const SourceVar Hom) :
    realize (induce function) term =
      reify (normalize (function term)) := by
  unfold realize
  rw [induce_normalize function respects term]

theorem induce_realize_eq_apply_canonicalize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom)
    (preserves : PreservesCanonical function)
    (normalForm : NormalForm Const SourceVar Hom) :
    induce (realize function) normalForm =
      function (canonicalize normalForm) := by
  rw [induce_realize_canonicalize]
  exact preserves (canonicalize_idempotent normalForm)

/-- Inducing a realization recovers a canonicality-preserving map on canonical forms. -/
theorem induce_realize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom)
    (preserves : PreservesCanonical function)
    {normalForm : NormalForm Const SourceVar Hom}
    (canonical : IsCanonical normalForm) :
    induce (realize function) normalForm = function normalForm := by
  rw [induce_realize_eq_apply_canonicalize function preserves normalForm]
  exact congrArg function canonical

/-- Realizing an induced map agrees derivably with the original term map. -/
theorem realize_induce
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom)
    (respects : RespectsDerives function) (term : Term Const SourceVar Hom) :
    Derives (realize (induce function) term) (function term) := by
  rw [realize_induce_eq_reify_normalize function respects term]
  exact (derives_reify_normalize (function term)).symm

/-- Every result of an induced term transformation is canonical. -/
theorem induce_isCanonical
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom)
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (normalForm : NormalForm Const SourceVar Hom) :
    IsCanonical (induce function normalForm) := by
  unfold induce
  exact canonicalize_normalize _

/-- Every induced term transformation preserves canonical forms. -/
theorem induce_preservesCanonical
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    (function : Term Const SourceVar Hom → Term Const TargetVar Hom)
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom] :
    PreservesCanonical (induce function) := by
  intro normalForm _
  exact induce_isCanonical function normalForm

theorem realize_respectsDerives
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (function : NormalForm Const SourceVar Hom →
      NormalForm Const TargetVar Hom) :
    RespectsDerives (realize function) := by
      intro left right derives
      have equality :
          normalize left = normalize right :=
        normalize_eq_of_derives derives

      unfold realize
      rw [equality]
      exact Derives.refl (reify (function (normalize right)))


end ACUIHE.Solver
