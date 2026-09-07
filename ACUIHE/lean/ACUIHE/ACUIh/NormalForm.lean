import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.List

/-!
Standalone ACUIh normal forms.

Each summand is a homomorphism word paired with a generator. Ordinary finite
sets account for associativity, commutativity, idempotence, and zero.
-/

namespace ACUIHE.ACUIh

universe u v

/-- A finite set of summands `h₁(…(hₙ(a)))`, with outermost homomorphisms first. -/
abbrev NormalForm (Generator : Type u) (Hom : Type v) :=
  Finset (List Hom × Generator)

namespace NormalForm

variable {Generator : Type u} {Hom : Type v}

/-- One generator, with no surrounding homomorphisms. -/
def generator (name : Generator) : NormalForm Generator Hom :=
  {([], name)}

/-- Apply a homomorphism to every summand, distributing over the ACUI sum. -/
def prefixHom (name : Hom) (form : NormalForm Generator Hom) :
    NormalForm Generator Hom :=
  form.map ⟨fun summand => (name :: summand.1, summand.2), by
    rintro ⟨leftPath, leftAtom⟩ ⟨rightPath, rightAtom⟩ equality
    simpa using equality⟩

@[simp]
theorem prefixHom_empty (name : Hom) :
    prefixHom name (∅ : NormalForm Generator Hom) = ∅ := by
  simp [prefixHom]

@[simp]
theorem prefixHom_singleton (name : Hom) (path : List Hom) (atom : Generator) :
    prefixHom name {(path, atom)} = {(name :: path, atom)} := by
  rw [prefixHom, Finset.map_singleton]
  rfl

@[simp]
theorem prefixHom_union [DecidableEq Generator] [DecidableEq Hom]
    (name : Hom) (left right : NormalForm Generator Hom) :
    prefixHom name (left ∪ right) = prefixHom name left ∪ prefixHom name right := by
  exact Finset.map_union _ _

theorem prefixHom_injective (name : Hom) :
    Function.Injective (prefixHom (Generator := Generator) name) := by
  intro left right equality
  exact Finset.map_injective _ equality

@[simp]
theorem mem_prefixHom (name : Hom) (form : NormalForm Generator Hom)
    (path : List Hom) (atom : Generator) :
    (path, atom) ∈ prefixHom name form ↔
      ∃ suffix, path = name :: suffix ∧ (suffix, atom) ∈ form := by
  simp only [prefixHom, Finset.mem_map]
  constructor
  · rintro ⟨⟨suffix, value⟩, membership, equality⟩
    cases equality
    exact ⟨suffix, rfl, membership⟩
  · rintro ⟨suffix, rfl, membership⟩
    exact ⟨(suffix, atom), membership, rfl⟩

end NormalForm

/-- Pure ACUIh syntax: generators, ACUI addition, and named homomorphisms. -/
inductive Term (Generator : Type u) (Hom : Type v) where
  | zero
  | atom (name : Generator)
  | add (left right : Term Generator Hom)
  | hom (name : Hom) (body : Term Generator Hom)
  deriving DecidableEq

namespace Term

variable {Generator : Type u} {Hom : Type v}
variable [DecidableEq Generator] [DecidableEq Hom]

/-- Normalize pure ACUIh syntax directly into an ordinary finite set. -/
def normalize : Term Generator Hom → NormalForm Generator Hom
  | .zero => ∅
  | .atom name => NormalForm.generator name
  | .add left right => normalize left ∪ normalize right
  | .hom name body => NormalForm.prefixHom name (normalize body)

@[simp] theorem normalize_zero :
    normalize (.zero : Term Generator Hom) = ∅ := rfl

@[simp] theorem normalize_atom (name : Generator) :
    normalize (.atom name : Term Generator Hom) = NormalForm.generator name := rfl

@[simp] theorem normalize_add (left right : Term Generator Hom) :
    normalize (.add left right) = normalize left ∪ normalize right := rfl

@[simp] theorem normalize_hom (name : Hom) (body : Term Generator Hom) :
    normalize (.hom name body) = NormalForm.prefixHom name (normalize body) := rfl

theorem normalize_add_assoc (a b c : Term Generator Hom) :
    normalize (.add (.add a b) c) = normalize (.add a (.add b c)) :=
  Finset.union_assoc _ _ _

theorem normalize_add_comm (a b : Term Generator Hom) :
    normalize (.add a b) = normalize (.add b a) := Finset.union_comm _ _

@[simp] theorem normalize_add_zero (a : Term Generator Hom) :
    normalize (.add a .zero) = normalize a := Finset.union_empty _

@[simp] theorem normalize_add_self (a : Term Generator Hom) :
    normalize (.add a a) = normalize a := Finset.union_self _

theorem normalize_hom_add (name : Hom) (a b : Term Generator Hom) :
    normalize (.hom name (.add a b)) =
      normalize (.add (.hom name a) (.hom name b)) :=
  NormalForm.prefixHom_union _ _ _

@[simp] theorem normalize_hom_zero (name : Hom) :
    normalize (.hom name (.zero : Term Generator Hom)) = ∅ :=
  NormalForm.prefixHom_empty _

end Term

namespace Term

variable {Generator : Type u} {Hom : Type v}

/-- Rebuild the nested homomorphisms recorded by a summand path. -/
def reifyPath (path : List Hom) (body : Term Generator Hom) :
    Term Generator Hom :=
  path.foldr (fun name inner => .hom name inner) body

end Term

namespace NormalForm

variable {Generator : Type u} {Hom : Type v}

private def reifyList : List (List Hom × Generator) → Term Generator Hom
  | [] => .zero
  | (path, name) :: summands =>
      .add (Term.reifyPath path (.atom name)) (reifyList summands)

/--
Reify an ACUIh normal form to pure ACUIh syntax.

Summands are ordered by their injective natural-number encodings so that the
chosen syntactic representative is deterministic without requiring callers to
supply linear orders on generators and homomorphism names.
-/
def reify [Encodable Generator] [Encodable Hom]
    (normalForm : NormalForm Generator Hom) : Term Generator Hom :=
  let _ : LinearOrder (List Hom × Generator) :=
    LinearOrder.lift' Encodable.encode Encodable.encode_injective
  reifyList normalForm.sort

@[simp]
theorem normalize_reifyPath_atom
    [DecidableEq Generator] [DecidableEq Hom]
    (path : List Hom) (name : Generator) :
    Term.normalize (Term.reifyPath path (.atom name)) = {(path, name)} := by
  induction path with
  | nil => rfl
  | cons hom path inductionHypothesis =>
      simp only [Term.reifyPath, List.foldr_cons, Term.normalize_hom]
      change prefixHom hom
        (Term.normalize (Term.reifyPath path (.atom name))) = _
      rw [inductionHypothesis, prefixHom_singleton]

private theorem normalize_reifyList
    [DecidableEq Generator] [DecidableEq Hom]
    (summands : List (List Hom × Generator)) :
    Term.normalize (reifyList summands) = summands.toFinset := by
  induction summands with
  | nil => rfl
  | cons summand summands inductionHypothesis =>
      rcases summand with ⟨path, name⟩
      simp only [reifyList, Term.normalize_add, normalize_reifyPath_atom,
        inductionHypothesis, List.toFinset_cons]
      exact Finset.singleton_union _ _

/-- Reifying and normalizing recovers the original finite-set normal form. -/
@[simp]
theorem normalize_reify [Encodable Generator] [Encodable Hom]
    [DecidableEq Generator] [DecidableEq Hom]
    (normalForm : NormalForm Generator Hom) :
    Term.normalize (reify normalForm) = normalForm := by
  let _ : LinearOrder (List Hom × Generator) :=
    LinearOrder.lift' Encodable.encode Encodable.encode_injective
  rw [reify, normalize_reifyList, Finset.sort_toFinset]

end NormalForm

end ACUIHE.ACUIh
