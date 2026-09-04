import ACUIHE.NormalForm.Core
import Mathlib.Data.FinEnum

/-!
Finite, normal-form-native identities for the `E` bodies occurring in an
ACUIhE inequality.

The old combination search identified an `E` node by a path through a
reified `Term`.  This module instead folds the intrinsic `NormalForm`, rebuilds
each recursive body while traversing it, and records the bodies themselves.
Consequently an occurrence carries its body directly and no partial syntax
address lookup is required.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver
open ACUIHE.Solver.NormalForm.Internal

universe u v w

local instance eBodyDecidableEq {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

local instance eBodyRecursiveUnionCommutative {Alpha : Type*} :
    Std.Commutative (fun left right : RecursiveFinset Alpha => left ∪ right) :=
  ⟨RecursiveFinset.union_comm⟩

local instance eBodyRecursiveUnionAssociative {Alpha : Type*} :
    Std.Associative (fun left right : RecursiveFinset Alpha => left ∪ right) :=
  ⟨RecursiveFinset.union_assoc⟩

local instance eBodyRecursiveUnionIdempotent {Alpha : Type*} :
    Std.IdempotentOp (fun left right : RecursiveFinset Alpha => left ∪ right) :=
  ⟨RecursiveFinset.union_self⟩

private theorem recursiveFoldSingleton_eq_ofFinset
    {Alpha : Type*} [Encodable Alpha] [DecidableEq Alpha]
    (set : Finset Alpha) :
    set.fold (fun left right : RecursiveFinset Alpha => left ∪ right)
        (∅ : RecursiveFinset Alpha) (fun value => {value}) =
      RecursiveFinset.ofFinset set := by
  induction set using Finset.induction_on with
  | empty => simp
  | @insert value set absent inductionHypothesis =>
      rw [Finset.fold_insert_idem, inductionHypothesis]
      rw [show insert value set = {value} ∪ set by ext; simp]
      rw [RecursiveFinset.ofFinset_union,
        RecursiveFinset.ofFinset_singleton]

private theorem rawFoldRebuild
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {item : RawNormalAtom Const Var Hom ⊕ RawNormalForm Const Var Hom}
    (valid : ValidNode item) :
    match item with
    | .inl atom => ∀ path,
        rawFoldSummand
          (∅ : RawNormalForm Const Var Hom) (· ∪ ·)
          (fun path name => {(path, RawNormalAtom.constant name)})
          (fun path name => {(path, RawNormalAtom.variable name)})
          (fun path body => {(path, RawNormalAtom.eOperator body)})
          (path, atom) = {(path, atom)}
    | .inr normalForm =>
        rawFold
          (∅ : RawNormalForm Const Var Hom) (· ∪ ·)
          (fun path name => {(path, RawNormalAtom.constant name)})
          (fun path name => {(path, RawNormalAtom.variable name)})
          (fun path body => {(path, RawNormalAtom.eOperator body)})
          normalForm = normalForm := by
  let _ := Encodable.decidableEqOfEncodable
    (RawNormalSummand Const Var Hom)
  induction valid with
  | constant name => intro path; rfl
  | «variable» name => intro path; rfl
  | eOperator bodyValid inductionHypothesis =>
      intro path
      simp only [rawFoldSummand]
      rw [inductionHypothesis]
  | @normalForm normalForm outer nested inductionHypothesis =>
      change rawFold
          (∅ : RawNormalForm Const Var Hom) (· ∪ ·)
          (fun path name => {(path, RawNormalAtom.constant name)})
          (fun path name => {(path, RawNormalAtom.variable name)})
          (fun path body => {(path, RawNormalAtom.eOperator body)})
          _ = _
      rw [rawFold_toFinset _ _ (fun value => RecursiveFinset.union_empty value)
        _ _ _ outer]
      have pointwise : ∀ summand ∈ RecursiveFinset.toFinset normalForm,
          rawFoldSummand
            (∅ : RawNormalForm Const Var Hom) (· ∪ ·)
            (fun path name => {(path, RawNormalAtom.constant name)})
            (fun path name => {(path, RawNormalAtom.variable name)})
            (fun path body => {(path, RawNormalAtom.eOperator body)})
            summand = {summand} := by
        intro summand membership
        exact inductionHypothesis summand membership summand.1
      rw [Finset.fold_congr pointwise]
      rw [recursiveFoldSingleton_eq_ofFinset]
      exact outer

/-- Folding a normal form back into semantic singleton summands is the
identity.  This is the common rebuilding fact used by body-aware folds. -/
theorem rebuildNormalForm_eq
    {Const Var Hom : Type*}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    target.fold
      (∅ : NormalForm Const Var Hom) (· ∪ ·)
      (fun path name => {(path, .constant name)})
      (fun path name => {(path, .variable name)})
      (fun path body => {(path, .eOperator body)}) = target := by
  apply NormalForm.ext_raw
  rw [NormalForm.fold_hom
    (fun result : NormalForm Const Var Hom => result.raw)
    (∅ : NormalForm Const Var Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    (∅ : RawNormalForm Const Var Hom) (· ∪ ·)
    (fun path name => {(path, RawNormalAtom.constant name)})
    (fun path name => {(path, RawNormalAtom.variable name)})
    (fun path body => {(path, RawNormalAtom.eOperator body)})
    (by rfl) (by intro left right; rfl)
    (by intro path name; rfl) (by intro path name; rfl)
    (by intro path body; rfl) target]
  exact rawFoldRebuild target.valid

/-- The result of traversing a normal form while rebuilding every recursive
body.  `source` is definitionally accumulated alongside the ordered list of
all bodies of `E` atoms, including nested ones. -/
abbrev EBodyScan
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] :=
  NormalForm Const Var Hom × List (NormalForm Const Var Hom)

/-- Collect all `E` bodies without leaving the intrinsic normal-form
representation. -/
def scanEBodies
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) : EBodyScan Const Var Hom :=
  target.fold
    (∅, [])
    (fun left right => (left.1 ∪ right.1, left.2 ++ right.2))
    (fun path name => ({(path, .constant name)}, []))
    (fun path name => ({(path, .variable name)}, []))
    (fun path scannedBody =>
      ({(path, .eOperator scannedBody.1)},
        scannedBody.1 :: scannedBody.2))

/-- The rebuilding component of `scanEBodies` is exactly its input. -/
@[simp]
theorem scanEBodies_source
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    (scanEBodies target).1 = target := by
  unfold scanEBodies
  rw [NormalForm.fold_hom
    (fun result : EBodyScan Const Var Hom => result.1)
    (∅, [])
    (fun left right => (left.1 ∪ right.1, left.2 ++ right.2))
    (fun path name => ({(path, .constant name)}, []))
    (fun path name => ({(path, .variable name)}, []))
    (fun path body => ({(path, .eOperator body.1)}, body.1 :: body.2))
    (∅ : NormalForm Const Var Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    rfl (by intro left right; rfl)
    (by intro path name; rfl) (by intro path name; rfl)
    (by intro path body; rfl) target]
  exact rebuildNormalForm_eq target

/-- Extensional set version of the body scan.  This is used for proofs where
the order chosen by the executable list is irrelevant. -/
def scanEBodySet
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    NormalForm Const Var Hom × Finset (NormalForm Const Var Hom) :=
  target.fold
    (∅, ∅)
    (fun left right => (left.1 ∪ right.1, left.2 ∪ right.2))
    (fun path name => ({(path, .constant name)}, ∅))
    (fun path name => ({(path, .variable name)}, ∅))
    (fun path scannedBody =>
      ({(path, .eOperator scannedBody.1)},
        insert scannedBody.1 scannedBody.2))

theorem scanEBodySet_eq_fold
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    scanEBodySet target =
      target.fold
        (∅, ∅)
        (fun left right => (left.1 ∪ right.1, left.2 ∪ right.2))
        (fun path name => ({(path, .constant name)}, ∅))
        (fun path name => ({(path, .variable name)}, ∅))
        (fun path scannedBody =>
          ({(path, .eOperator scannedBody.1)},
            insert scannedBody.1 scannedBody.2)) :=
  rfl

/-- The ordered and extensional scans contain exactly the same bodies. -/
theorem scanEBodies_toFinset
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    ((scanEBodies target).1, (scanEBodies target).2.toFinset) =
      scanEBodySet target := by
  unfold scanEBodies scanEBodySet
  exact NormalForm.fold_hom
    (fun result : EBodyScan Const Var Hom =>
      (result.1, result.2.toFinset))
    (∅, [])
    (fun left right => (left.1 ∪ right.1, left.2 ++ right.2))
    (fun path name => ({(path, .constant name)}, []))
    (fun path name => ({(path, .variable name)}, []))
    (fun path body =>
      ({(path, .eOperator body.1)}, body.1 :: body.2))
    (∅, ∅)
    (fun left right => (left.1 ∪ right.1, left.2 ∪ right.2))
    (fun path name => ({(path, .constant name)}, ∅))
    (fun path name => ({(path, .variable name)}, ∅))
    (fun path body =>
      ({(path, .eOperator body.1)}, insert body.1 body.2))
    rfl
    (by intro left right; simp)
    (by intro path name; simp)
    (by intro path name; simp)
    (by intro path body; simp)
    target

@[simp]
theorem mem_scanEBodies_iff
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {body target : NormalForm Const Var Hom} :
    body ∈ (scanEBodies target).2 ↔ body ∈ (scanEBodySet target).2 := by
  have equality := congrArg Prod.snd (scanEBodies_toFinset target)
  simpa using congrArg (fun bodies => body ∈ bodies) equality

private theorem eBodyNormalUnionEmpty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) : target ∪ ∅ = target := by
  apply NormalForm.ext_raw
  exact rawUnion_empty target.raw

local instance eBodyNormalUnionCommutative
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Commutative
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun left right => by
    apply NormalForm.ext_raw
    exact rawUnion_comm left.raw right.raw⟩

local instance eBodyNormalUnionAssociative
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Associative
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun left middle right => by
    apply NormalForm.ext_raw
    exact rawUnion_assoc left.raw middle.raw right.raw⟩

local instance eBodyNormalUnionIdempotent
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.IdempotentOp
      (fun left right : NormalForm Const Var Hom => left ∪ right) :=
  ⟨fun target => by
    apply NormalForm.ext_raw
    exact rawUnion_self target.raw⟩

local instance eBodySetScanCommutative
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Commutative (fun left right :
        NormalForm Const Var Hom × Finset (NormalForm Const Var Hom) =>
      (left.1 ∪ right.1, left.2 ∪ right.2)) :=
  ⟨by intro left right; apply Prod.ext <;> simp [Std.Commutative.comm]⟩

local instance eBodySetScanAssociative
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Associative (fun left right :
        NormalForm Const Var Hom × Finset (NormalForm Const Var Hom) =>
      (left.1 ∪ right.1, left.2 ∪ right.2)) :=
  ⟨by intro left middle right; apply Prod.ext <;>
    simp [Std.Associative.assoc]⟩

local instance eBodySetScanIdempotent
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.IdempotentOp (fun left right :
        NormalForm Const Var Hom × Finset (NormalForm Const Var Hom) =>
      (left.1 ∪ right.1, left.2 ∪ right.2)) :=
  ⟨by intro target; apply Prod.ext <;> simp [Std.IdempotentOp.idempotent]⟩

@[simp]
theorem scanEBodySet_source
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    (scanEBodySet target).1 = target := by
  have equality := congrArg Prod.fst (scanEBodies_toFinset target)
  simpa using equality.symm.trans (scanEBodies_source target)

@[simp]
theorem scanEBodySet_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    scanEBodySet (∅ : NormalForm Const Var Hom) = (∅, ∅) := by
  simp [scanEBodySet]

theorem scanEBodySet_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    scanEBodySet (left ∪ right) =
      let leftResult := scanEBodySet left
      let rightResult := scanEBodySet right
      (leftResult.1 ∪ rightResult.1,
        leftResult.2 ∪ rightResult.2) := by
  unfold scanEBodySet
  apply NormalForm.fold_union
  intro result
  apply Prod.ext
  · exact eBodyNormalUnionEmpty result.1
  · simp

@[simp]
theorem scanEBodySet_singleton_constant
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Const) :
    scanEBodySet
        ({(path, .constant name)} : NormalForm Const Var Hom) =
      ({(path, .constant name)}, ∅) := by
  unfold scanEBodySet
  rw [NormalForm.fold_singleton]
  apply Prod.ext
  · exact eBodyNormalUnionEmpty _
  · simp

@[simp]
theorem scanEBodySet_singleton_variable
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Var) :
    scanEBodySet
        ({(path, .variable name)} : NormalForm Const Var Hom) =
      ({(path, .variable name)}, ∅) := by
  unfold scanEBodySet
  rw [NormalForm.fold_singleton]
  apply Prod.ext
  · exact eBodyNormalUnionEmpty _
  · simp

@[simp]
theorem scanEBodySet_singleton_eOperator
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (body : NormalForm Const Var Hom) :
    scanEBodySet
        ({(path, .eOperator body)} : NormalForm Const Var Hom) =
      ({(path, .eOperator body)}, insert body (scanEBodySet body).2) := by
  conv_lhs => rw [scanEBodySet_eq_fold]
  rw [NormalForm.fold_singleton]
  dsimp only
  rw [← scanEBodySet_eq_fold body]
  rw [scanEBodySet_source]
  apply Prod.ext
  · exact eBodyNormalUnionEmpty _
  · simp

/-- A proof-oriented scan carrying the transitive-closure invariant. -/
structure ClosedEBodyScan
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  source : NormalForm Const Var Hom
  bodies : Finset (NormalForm Const Var Hom)
  represents : (scanEBodySet source).2 = bodies
  closed : ∀ body ∈ bodies, (scanEBodySet body).2 ⊆ bodies

/-- Compute the same body set while establishing closure compositionally. -/
def closedEBodyScan
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    ClosedEBodyScan Const Var Hom :=
  target.fold
    ⟨∅, ∅, by simp, by simp⟩
    (fun left right =>
      ⟨left.source ∪ right.source, left.bodies ∪ right.bodies,
        by
          have unionEquality := congrArg Prod.snd
            (scanEBodySet_union left.source right.source)
          dsimp only at unionEquality
          rw [unionEquality, left.represents, right.represents],
        by
          intro body membership
          simp only [Finset.mem_union] at membership
          rcases membership with membership | membership
          · exact Finset.Subset.trans (left.closed body membership)
              (Finset.subset_union_left)
          · exact Finset.Subset.trans (right.closed body membership)
              (Finset.subset_union_right)⟩)
    (fun path name =>
      ⟨{(path, .constant name)}, ∅, by simp, by simp⟩)
    (fun path name =>
      ⟨{(path, .variable name)}, ∅, by simp, by simp⟩)
    (fun path body =>
      ⟨{(path, .eOperator body.source)}, insert body.source body.bodies,
        by rw [scanEBodySet_singleton_eOperator, body.represents],
        by
          intro nested membership
          simp only [Finset.mem_insert] at membership
          rcases membership with equality | membership
          · subst nested
            rw [body.represents]
            exact Finset.subset_insert _ _
          · exact Finset.Subset.trans (body.closed nested membership)
              (Finset.subset_insert _ _)⟩)

@[simp]
theorem closedEBodyScan_source
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (target : NormalForm Const Var Hom) :
    (closedEBodyScan target).source = target := by
  unfold closedEBodyScan
  rw [NormalForm.fold_hom
    (fun result : ClosedEBodyScan Const Var Hom => result.source)
    ⟨∅, ∅, by simp, by simp⟩
    (fun left right =>
      ⟨left.source ∪ right.source, left.bodies ∪ right.bodies,
        by
          have unionEquality := congrArg Prod.snd
            (scanEBodySet_union left.source right.source)
          dsimp only at unionEquality
          rw [unionEquality, left.represents, right.represents],
        by
          intro body membership
          simp only [Finset.mem_union] at membership
          rcases membership with membership | membership
          · exact Finset.Subset.trans (left.closed body membership)
              Finset.subset_union_left
          · exact Finset.Subset.trans (right.closed body membership)
              Finset.subset_union_right⟩)
    (fun path name =>
      ⟨{(path, .constant name)}, ∅, by simp, by simp⟩)
    (fun path name =>
      ⟨{(path, .variable name)}, ∅, by simp, by simp⟩)
    (fun path body =>
      ⟨{(path, .eOperator body.source)}, insert body.source body.bodies,
        by rw [scanEBodySet_singleton_eOperator, body.represents],
        by
          intro nested membership
          simp only [Finset.mem_insert] at membership
          rcases membership with equality | membership
          · subst nested
            rw [body.represents]
            exact Finset.subset_insert _ _
          · exact Finset.Subset.trans (body.closed nested membership)
              (Finset.subset_insert _ _)⟩)
    (∅ : NormalForm Const Var Hom) (· ∪ ·)
    (fun path name => {(path, .constant name)})
    (fun path name => {(path, .variable name)})
    (fun path body => {(path, .eOperator body)})
    rfl (by intro left right; rfl)
    (by intro path name; rfl) (by intro path name; rfl)
    (by intro path body; rfl) target]
  exact rebuildNormalForm_eq target

/-- Every collected body brings all of its nested bodies with it. -/
theorem scanEBodySet_closed
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {body target : NormalForm Const Var Hom}
    (membership : body ∈ (scanEBodySet target).2) :
    (scanEBodySet body).2 ⊆ (scanEBodySet target).2 := by
  let result := closedEBodyScan target
  have sourceEquality : result.source = target := closedEBodyScan_source target
  have bodiesEquality : result.bodies = (scanEBodySet target).2 := by
    rw [← result.represents, sourceEquality]
  rw [← bodiesEquality] at membership ⊢
  exact result.closed body membership

/-- Extensional set of all bodies in both sides. -/
def allEBodySet
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Finset (NormalForm Const Var Hom) :=
  (scanEBodySet left).2 ∪ (scanEBodySet right).2

/-- Ordered finite table of all canonical `E` bodies in both sides.  Duplicate
bodies are removed, since the same `E(body)` has the same value at every
position. -/
def allEBodies
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    List (NormalForm Const Var Hom) :=
  ((scanEBodies left).2 ++ (scanEBodies right).2).dedup

@[simp]
theorem mem_allEBodies_iff
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {body left right : NormalForm Const Var Hom} :
    body ∈ allEBodies left right ↔ body ∈ allEBodySet left right := by
  simp [allEBodies, allEBodySet, mem_scanEBodies_iff]

/-- A finite `E` occurrence is now a canonical input body, rather than a
path into a reified term. -/
abbrev EOccurrence
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :=
  {body : NormalForm Const Var Hom // body ∈ allEBodies left right}

instance eOccurrenceFinEnum
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    FinEnum (EOccurrence left right) :=
  inferInstance

/-- Encode a body occurrence through its explicit finite enumeration.  No
global encoding of arbitrary normal forms is needed. -/
instance eOccurrenceEncodable
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    Encodable (EOccurrence left right) :=
  Encodable.ofEquiv
    (Fin (FinEnum.card (EOccurrence left right)))
    (FinEnum.equiv : EOccurrence left right ≃
      Fin (FinEnum.card (EOccurrence left right)))

/-- Direct, total access to the canonical body named by an occurrence. -/
def EOccurrence.body
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (occurrence : EOccurrence left right) : NormalForm Const Var Hom :=
  occurrence.1

theorem mem_allEBodies_left
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    {body : NormalForm Const Var Hom}
    (membership : body ∈ (scanEBodySet left).2) :
    body ∈ allEBodies left right := by
  rw [mem_allEBodies_iff]
  exact Finset.mem_union_left _ membership

theorem mem_allEBodies_right
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    {body : NormalForm Const Var Hom}
    (membership : body ∈ (scanEBodySet right).2) :
    body ∈ allEBodies left right := by
  rw [mem_allEBodies_iff]
  exact Finset.mem_union_right _ membership

/-- Nested bodies of an occurrence are occurrences in the same problem. -/
theorem EOccurrence.nested_mem_allEBodies
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : NormalForm Const Var Hom}
    (occurrence : EOccurrence left right)
    {nested : NormalForm Const Var Hom}
    (membership : nested ∈ (scanEBodySet occurrence.body).2) :
    nested ∈ allEBodies left right := by
  have occurrenceMembership : occurrence.body ∈ allEBodySet left right :=
    mem_allEBodies_iff.mp occurrence.2
  rw [allEBodySet, Finset.mem_union] at occurrenceMembership
  rw [mem_allEBodies_iff, allEBodySet, Finset.mem_union]
  rcases occurrenceMembership with leftMembership | rightMembership
  · exact Or.inl (scanEBodySet_closed leftMembership membership)
  · exact Or.inr (scanEBodySet_closed rightMembership membership)

/-- Find the finite occurrence whose canonical body is `body`. -/
def findEOccurrence?
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom)
    (body : NormalForm Const Var Hom) : Option (EOccurrence left right) :=
  (FinEnum.toList (EOccurrence left right)).find? fun occurrence =>
    occurrence.body = body

end ACUIHE.Solver.Search
