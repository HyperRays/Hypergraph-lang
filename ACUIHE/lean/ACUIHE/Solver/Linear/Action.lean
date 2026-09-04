import ACUIHE.NormalForm.Core
import ACUIHE.Solver.Linear.Context
import Mathlib.Algebra.Module.Defs

/-! The finite-language semiring action on ACUIhE normal forms. -/

namespace ACUIHE.Solver.Linear

open ACUIHE.Solver.NormalForm.Internal

universe u v w

local instance actionEncodableDecidableEq {α : Type*} [Encodable α] :
    DecidableEq α :=
  Encodable.decidableEqOfEncodable α

/-- Prefix one encoded normal-form summand by a complete homomorphism path. -/
def prefixSummand
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (path : List Hom) (summand : RawNormalSummand Const Var Hom) :
    RawNormalSummand Const Var Hom :=
  (path ++ summand.1, summand.2)

@[simp]
theorem prefixSummand_nil
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (summand : RawNormalSummand Const Var Hom) :
    prefixSummand [] summand = summand := by
  rcases summand with ⟨path, atom⟩
  rfl

theorem prefixSummand_append
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (leftPath rightPath : List Hom)
    (summand : RawNormalSummand Const Var Hom) :
    prefixSummand (leftPath ++ rightPath) summand =
      prefixSummand leftPath (prefixSummand rightPath summand) := by
  rcases summand with ⟨path, atom⟩
  simp [prefixSummand, List.append_assoc]

/-- Apply every path in a context to every summand in a finite collection. -/
def transformSummands
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom)
    (summands : Finset (RawNormalSummand Const Var Hom)) :
    Finset (RawNormalSummand Const Var Hom) :=
  Finset.image₂ prefixSummand context.paths summands

@[simp]
theorem transformSummands_zero
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (summands : Finset (RawNormalSummand Const Var Hom)) :
    transformSummands (0 : HomContext Hom) summands = ∅ := by
  exact Finset.image₂_empty_left

@[simp]
theorem transformSummands_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom) :
    transformSummands context
      (∅ : Finset (RawNormalSummand Const Var Hom)) = ∅ := by
  exact Finset.image₂_empty_right

@[simp]
theorem transformSummands_one
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (summands : Finset (RawNormalSummand Const Var Hom)) :
    transformSummands (1 : HomContext Hom) summands = summands := by
  exact Finset.image₂_left_identity prefixSummand_nil summands

theorem transformSummands_add
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : HomContext Hom)
    (summands : Finset (RawNormalSummand Const Var Hom)) :
    transformSummands (left + right) summands =
      transformSummands left summands ∪ transformSummands right summands := by
  exact Finset.image₂_union_left

theorem transformSummands_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom)
    (left right : Finset (RawNormalSummand Const Var Hom)) :
    transformSummands context (left ∪ right) =
      transformSummands context left ∪ transformSummands context right := by
  exact Finset.image₂_union_right

theorem transformSummands_mul
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : HomContext Hom)
    (summands : Finset (RawNormalSummand Const Var Hom)) :
    transformSummands (left * right) summands =
      transformSummands left (transformSummands right summands) := by
  exact Finset.image₂_assoc fun leftPath rightPath summand =>
    prefixSummand_append leftPath rightPath summand

private theorem transformedRecursivelyValid
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom) (normalForm : NormalForm Const Var Hom) :
    RecursivelyValid
      (RecursiveFinset.ofFinset
        (transformSummands context
          (RecursiveFinset.toFinset normalForm.raw))) := by
  apply ValidNode.normalForm
  · simp [RecursiveFinset.Valid]
  · intro stored membership
    rw [RecursiveFinset.toFinset_ofFinset] at membership
    rcases Finset.mem_image₂.mp membership with
      ⟨path, _pathMembership, source, sourceMembership, equality⟩
    subst stored
    exact normalForm.valid.nested source sourceMembership

namespace HomContext

/--
Apply a finite homomorphism context to a normal form.  Every context path is
concatenated in front of every outer path in the normal form.
-/
def act
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom) (normalForm : NormalForm Const Var Hom) :
    NormalForm Const Var Hom :=
  ⟨RecursiveFinset.ofFinset
      (transformSummands context
        (RecursiveFinset.toFinset normalForm.raw)),
    transformedRecursivelyValid context normalForm⟩

@[simp]
theorem toFinset_act
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom) (normalForm : NormalForm Const Var Hom) :
    RecursiveFinset.toFinset (act context normalForm).raw =
      transformSummands context
        (RecursiveFinset.toFinset normalForm.raw) := by
  simp [act]

end HomContext

private theorem normalFormExtToFinset
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (equality : RecursiveFinset.toFinset left.raw =
      RecursiveFinset.toFinset right.raw) :
    left = right := by
  apply NormalForm.ext_raw
  calc
    left.raw = RecursiveFinset.ofFinset
        (RecursiveFinset.toFinset left.raw) := left.valid.outer.symm
    _ = RecursiveFinset.ofFinset
        (RecursiveFinset.toFinset right.raw) := congrArg _ equality
    _ = right.raw := right.valid.outer

/-- The existing union and empty form give normal forms an additive monoid. -/
instance normalFormAddCommMonoid
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    AddCommMonoid (NormalForm Const Var Hom) where
  add := NormalForm.union
  zero := NormalForm.empty
  add_assoc left middle right := by
    apply NormalForm.ext_raw
    exact rawUnion_assoc left.raw middle.raw right.raw
  zero_add normalForm := by
    apply NormalForm.ext_raw
    calc
      (∅ : RawNormalForm Const Var Hom) ∪ normalForm.raw =
          normalForm.raw ∪ ∅ := rawUnion_comm _ _
      _ = normalForm.raw := rawUnion_empty _
  add_zero normalForm := by
    apply NormalForm.ext_raw
    exact rawUnion_empty normalForm.raw
  add_comm left right := by
    apply NormalForm.ext_raw
    exact rawUnion_comm left.raw right.raw
  nsmul := nsmulRec

@[simp]
theorem normalForm_raw_zero
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    (0 : NormalForm Const Var Hom).raw =
      (∅ : RawNormalForm Const Var Hom) :=
  rfl

@[simp]
theorem normalForm_raw_add
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    (left + right).raw = left.raw ∪ right.raw :=
  rfl

theorem HomContext.act_one
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    HomContext.act (1 : HomContext Hom) normalForm = normalForm := by
  apply normalFormExtToFinset
  simp

theorem HomContext.act_mul
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : HomContext Hom)
    (normalForm : NormalForm Const Var Hom) :
    HomContext.act (left * right) normalForm =
      HomContext.act left (HomContext.act right normalForm) := by
  apply normalFormExtToFinset
  simp [transformSummands_mul]

theorem HomContext.act_zero
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    HomContext.act (0 : HomContext Hom) normalForm = 0 := by
  apply normalFormExtToFinset
  simp [normalForm_raw_zero]

theorem HomContext.act_add
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : HomContext Hom)
    (normalForm : NormalForm Const Var Hom) :
    HomContext.act (left + right) normalForm =
      HomContext.act left normalForm + HomContext.act right normalForm := by
  apply normalFormExtToFinset
  rw [HomContext.toFinset_act, normalForm_raw_add,
    RecursiveFinset.toFinset_union, HomContext.toFinset_act,
    HomContext.toFinset_act]
  exact transformSummands_add left right _

theorem HomContext.act_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom) :
    HomContext.act context (0 : NormalForm Const Var Hom) = 0 := by
  apply normalFormExtToFinset
  simp [normalForm_raw_zero]

theorem HomContext.act_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom)
    (left right : NormalForm Const Var Hom) :
    HomContext.act context (left + right) =
      HomContext.act context left + HomContext.act context right := by
  apply normalFormExtToFinset
  rw [HomContext.toFinset_act, normalForm_raw_add,
    RecursiveFinset.toFinset_union, normalForm_raw_add,
    RecursiveFinset.toFinset_union, HomContext.toFinset_act,
    HomContext.toFinset_act]
  exact transformSummands_union context _ _

/-- Normal forms are a left module over the finite homomorphism-context semiring. -/
instance
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Module (HomContext Hom) (NormalForm Const Var Hom) where
  smul := HomContext.act
  one_smul := HomContext.act_one
  mul_smul := HomContext.act_mul
  smul_zero := HomContext.act_empty
  smul_add := HomContext.act_union
  add_smul := HomContext.act_add
  zero_smul := HomContext.act_zero

@[simp]
theorem smul_eq_act
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (context : HomContext Hom) (normalForm : NormalForm Const Var Hom) :
    context • normalForm = HomContext.act context normalForm :=
  rfl

/-- A singleton context concatenates its path onto a singleton summand. -/
@[simp]
theorem singleton_smul_singleton
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (contextPath path : List Hom) (atom : NormalAtom Const Var Hom) :
    ({contextPath} : HomContext Hom) •
        ({(path, atom)} : NormalForm Const Var Hom) =
      ({(contextPath ++ path, atom)} : NormalForm Const Var Hom) := by
  rw [smul_eq_act]
  change
    HomContext.act (HomContext.singleton contextPath)
        (NormalForm.singleton (path, atom)) =
      NormalForm.singleton (contextPath ++ path, atom)
  apply normalFormExtToFinset
  simp [HomContext.act, transformSummands, prefixSummand,
    HomContext.singleton, NormalForm.singleton]
  cases atom <;> rfl

/-- A one-letter singleton context is the existing named-homomorphism action. -/
@[simp]
theorem singleton_hom_smul
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) :
    ({[name]} : HomContext Hom) • normalForm =
      prefixHom name normalForm := by
  rw [smul_eq_act]
  apply normalFormExtToFinset
  rw [HomContext.toFinset_act]
  change
    transformSummands (HomContext.singleton [name])
        (RecursiveFinset.toFinset normalForm.raw) =
      RecursiveFinset.toFinset
        (rawPrefixHom name normalForm.raw)
  unfold rawPrefixHom
  rw [RecursiveFinset.toFinset_image _ normalForm.valid.outer]
  simp [transformSummands, prefixSummand, HomContext.singleton]

end ACUIHE.Solver.Linear
