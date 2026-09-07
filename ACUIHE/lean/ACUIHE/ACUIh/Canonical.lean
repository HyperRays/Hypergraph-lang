import ACUIHE.ACUIh.NormalForm

/-! Canonicalization of standalone ACUIh normal forms. -/

namespace ACUIHE.ACUIh.NormalForm

universe u v

variable {Generator : Type u} {Hom : Type v}

/-- Canonicalize an ACUIh normal form by reifying and normalizing it. -/
def canonicalize [Encodable Generator] [Encodable Hom]
    [DecidableEq Generator] [DecidableEq Hom]
    (normalForm : NormalForm Generator Hom) : NormalForm Generator Hom :=
  Term.normalize (reify normalForm)

/-- An ACUIh normal form is canonical when canonicalizing it makes no change. -/
def IsCanonical [Encodable Generator] [Encodable Hom]
    [DecidableEq Generator] [DecidableEq Hom]
    (normalForm : NormalForm Generator Hom) : Prop :=
  canonicalize normalForm = normalForm

/-- Every standalone ACUIh normal form is already canonical. -/
@[simp]
theorem canonicalize_eq_self [Encodable Generator] [Encodable Hom]
    [DecidableEq Generator] [DecidableEq Hom]
    (normalForm : NormalForm Generator Hom) :
    canonicalize normalForm = normalForm := by
  exact normalize_reify normalForm

/-- Normal forms produced by normalization are fixed by canonicalization. -/
@[simp]
theorem canonicalize_normalize [Encodable Generator] [Encodable Hom]
    [DecidableEq Generator] [DecidableEq Hom]
    (term : Term Generator Hom) :
    canonicalize (Term.normalize term) = Term.normalize term := by
  exact canonicalize_eq_self (Term.normalize term)

/-- Canonicalization of ACUIh normal forms is idempotent. -/
@[simp]
theorem canonicalize_idempotent [Encodable Generator] [Encodable Hom]
    [DecidableEq Generator] [DecidableEq Hom]
    (normalForm : NormalForm Generator Hom) :
    canonicalize (canonicalize normalForm) = canonicalize normalForm := by
  exact canonicalize_eq_self (canonicalize normalForm)

/-- Every standalone ACUIh normal form satisfies the canonicality predicate. -/
@[simp]
theorem isCanonical [Encodable Generator] [Encodable Hom]
    [DecidableEq Generator] [DecidableEq Hom]
    (normalForm : NormalForm Generator Hom) :
    IsCanonical normalForm := by
  exact canonicalize_eq_self normalForm

end ACUIHE.ACUIh.NormalForm
