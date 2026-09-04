import ACUIHE.Solver.Linear.Context
import Mathlib.Data.Matrix.Mul

/-! Basis-changing matrices over the homomorphism-context semiring. -/

namespace ACUIHE.Solver.Linear

universe u v w x

/-- Embed coordinates along an injective map of finite bases. -/
def basisExtension
    {Small : Type u} {Large : Type v} {Hom : Type w}
    [DecidableEq Large] [Encodable Hom]
    (inclusion : Small ↪ Large) :
    Matrix Small Large (HomContext Hom) :=
  fun source target => if inclusion source = target then 1 else 0

/-- Restrict coordinates along an injective map of finite bases. -/
def basisRestriction
    {Small : Type u} {Large : Type v} {Hom : Type w}
    [DecidableEq Large] [Encodable Hom]
    (inclusion : Small ↪ Large) :
    Matrix Large Small (HomContext Hom) :=
  fun source target => if source = inclusion target then 1 else 0

@[simp]
theorem basisExtension_apply_same
    {Small : Type u} {Large : Type v} {Hom : Type w}
    [DecidableEq Large] [Encodable Hom]
    (inclusion : Small ↪ Large) (source : Small) :
    basisExtension (Hom := Hom) inclusion source (inclusion source) = 1 := by
  simp [basisExtension]

@[simp]
theorem basisRestriction_apply_same
    {Small : Type u} {Large : Type v} {Hom : Type w}
    [DecidableEq Large] [Encodable Hom]
    (inclusion : Small ↪ Large) (source : Small) :
    basisRestriction (Hom := Hom) inclusion (inclusion source) source = 1 := by
  simp [basisRestriction]

/-- Restricting immediately after extending a row recovers the row. -/
theorem basisExtension_mul_basisRestriction
    {Small : Type u} {Large : Type v} {Hom : Type w}
    [Fintype Small] [Fintype Large] [DecidableEq Small] [DecidableEq Large]
    [Encodable Hom]
    (inclusion : Small ↪ Large) :
    basisExtension (Hom := Hom) inclusion * basisRestriction inclusion =
      (1 : Matrix Small Small (HomContext Hom)) := by
  funext source target
  simp [Matrix.mul_apply, basisExtension, basisRestriction,
    Matrix.one_apply, inclusion.injective.eq_iff]

/-- Extending and then restricting the columns of a matrix changes nothing. -/
theorem mul_basisExtension_mul_basisRestriction
    {Row : Type x} {Small : Type u} {Large : Type v} {Hom : Type w}
    [Fintype Small] [Fintype Large] [DecidableEq Small] [DecidableEq Large]
    [Encodable Hom]
    (matrix : Matrix Row Small (HomContext Hom))
    (inclusion : Small ↪ Large) :
    matrix * basisExtension inclusion * basisRestriction inclusion = matrix := by
  rw [Matrix.mul_assoc, basisExtension_mul_basisRestriction,
    Matrix.mul_one]

/-- Extending after restricting is the projection onto the included basis. -/
def basisProjection
    {Small : Type u} {Large : Type v} {Hom : Type w}
    [Fintype Small] [DecidableEq Large] [Encodable Hom]
    (inclusion : Small ↪ Large) :
    Matrix Large Large (HomContext Hom) :=
  basisRestriction inclusion * basisExtension inclusion

end ACUIHE.Solver.Linear
