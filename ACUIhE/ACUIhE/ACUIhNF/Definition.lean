import ACUIhE.ACUIh
import Mathlib.Data.Finset.Fold

/-!
# Finite-set normal forms for ACUIh

A summand consists of a word of homomorphism names, in outermost-to-innermost
order, and a constant or variable. Normalization is executable with decidable
label equality. `NF.reifyWith` reifies a supplied, certified enumeration
computably. `NF.reify` chooses a noncomputable enumeration without imposing
an order on any of the label types.
-/

namespace ACUIhE.ACUIh

universe u v w

/-- The two disjoint kinds of generators; zero is represented by the empty set. -/
inductive Particle (Const : Type u) (Var : Type v) where
  | const : Const → Particle Const Var
  | var : Var → Particle Const Var
  deriving DecidableEq

/-- A word `[h₁, h₂]` paired with `p` represents `h₁(h₂(p))`. -/
abbrev Summand (Const : Type u) (Var : Type v) (Hom : Type w) :=
  List Hom × Particle Const Var

/-- Canonical ACUIh expressions, represented as finite sets of summands. -/
abbrev NF (Const : Type u) (Var : Type v) (Hom : Type w) :=
  Finset (Summand Const Var Hom)

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- View a particle as a term in the fragment. -/
def Particle.reify : Particle Const Var → Term Const Var Hom
  | .const name => .const name
  | .var name => .var name

/-- Apply a word of homomorphisms, with its head as the outermost operator. -/
def reifyWord : List Hom → Term Const Var Hom → Term Const Var Hom
  | [], term => term
  | name :: word, term => .hom name (reifyWord word term)

/-- Reconstruct one homomorphism word applied to one particle. -/
def Summand.reify (summand : Summand Const Var Hom) : Term Const Var Hom :=
  reifyWord summand.1 summand.2.reify

/-- Prefixing is injective and preserves the entire original summand. -/
def Summand.prepend (name : Hom) : Summand Const Var Hom ↪ Summand Const Var Hom where
  toFun := fun summand => (name :: summand.1, summand.2)
  inj' := by
    intro ⟨word, particle⟩ ⟨word', particle'⟩ equality
    simpa using equality

namespace NF

/-- Apply a named homomorphism to every summand. -/
def prepend (name : Hom) (normal : NF Const Var Hom) : NF Const Var Hom :=
  normal.map (Summand.prepend name)

@[simp] theorem prepend_empty (name : Hom) :
    prepend name (∅ : NF Const Var Hom) = ∅ := Finset.map_empty _

@[simp] theorem prepend_singleton (name : Hom) (summand : Summand Const Var Hom) :
    prepend name ({summand} : NF Const Var Hom) = {(name :: summand.1, summand.2)} :=
  Finset.map_singleton _ _

/-- Reconstruct a sum in the supplied enumeration order. -/
def reifyList : List (Summand Const Var Hom) → Term Const Var Hom
  | [] => .zero
  | summand :: rest => .add summand.reify (reifyList rest)

/-- Choose an enumeration and reconstruct a raw term representing the normal form. -/
noncomputable def reify (normal : NF Const Var Hom) : Term Const Var Hom :=
  reifyList normal.toList

end NF

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Normalize a term by distributing homomorphisms and taking finite unions. -/
def Term.normalize : Term Const Var Hom → NF Const Var Hom
  | .zero => ∅
  | .const name => {([], .const name)}
  | .var name => {([], .var name)}
  | .add left right => left.normalize ∪ right.normalize
  | .hom name body => NF.prepend name body.normalize

namespace NF

@[simp] theorem prepend_union (name : Hom) (left right : NF Const Var Hom) :
    prepend name (left ∪ right) = prepend name left ∪ prepend name right :=
  Finset.map_union _ _

/--
The concrete normal-form algebra. Install it locally with `letI := NF.algebra`;
it is explicit so that importing this module does not change finset arithmetic.
-/
@[instance_reducible] def algebra : ACUIh Hom (NF Const Var Hom) where
  add := fun left right => left ∪ right
  zero := ∅
  hom := prepend
  add_assoc := Finset.union_assoc
  add_comm := Finset.union_comm
  add_zero := Finset.union_empty
  add_idem := Finset.union_self
  hom_add := prepend_union
  hom_zero := prepend_empty

/-- Normalization recovers a singleton from a reified summand. -/
@[simp] theorem normalize_reify_summand (summand : Summand Const Var Hom) :
    summand.reify.normalize = ({summand} : NF Const Var Hom) := by
  rcases summand with ⟨word, particle⟩
  induction word with
  | nil => cases particle <;> rfl
  | cons name word ih =>
      change prepend name (Summand.reify (word, particle)).normalize = _
      rw [ih, prepend_singleton]

/-- Reifying any list normalizes to the set of its members, including duplicates. -/
@[simp] theorem normalize_reifyList (summands : List (Summand Const Var Hom)) :
    (reifyList summands).normalize = summands.toFinset := by
  induction summands with
  | nil => rfl
  | cons summand rest ih =>
      change summand.reify.normalize ∪ (reifyList rest).normalize = _
      rw [normalize_reify_summand, ih]
      simp

/--
Reify a supplied enumeration of a normal form and return a term with its
normalization certificate. This definition is computable: the enumeration
is supplied by the caller, and the certificate is erased during execution.
The enumeration may contain duplicates and may use any order.
-/
def reifyWith (normal : NF Const Var Hom) (summands : List (Summand Const Var Hom))
    (enumerates : summands.toFinset = normal) :
    {term : Term Const Var Hom // term.normalize = normal} :=
  ⟨reifyList summands, (normalize_reifyList summands).trans enumerates⟩

/-- The certified interface computes exactly the term produced by the supplied list. -/
@[simp] theorem reifyWith_val (normal : NF Const Var Hom)
    (summands : List (Summand Const Var Hom)) (enumerates : summands.toFinset = normal) :
    (reifyWith normal summands enumerates).val = reifyList summands := rfl

/-- Reification followed by normalization is exactly the identity on normal forms. -/
@[simp] theorem normalize_reify (normal : NF Const Var Hom) :
    normal.reify.normalize = normal := by
  rw [reify, normalize_reifyList, Finset.toList_toFinset]

end NF

/-- Evaluation in the normal-form model, under its generators, is normalization. -/
theorem Term.eval_normalForm (term : Term Const Var Hom) :
    letI := NF.algebra (Const := Const) (Var := Var) (Hom := Hom)
    term.eval (fun c => ({([], Particle.const c)} : NF Const Var Hom))
      (fun v => ({([], Particle.var v)} : NF Const Var Hom)) = term.normalize := by
  let _ := NF.algebra (Const := Const) (Var := Var) (Hom := Hom)
  induction term with
  | zero => rfl
  | const => rfl
  | var => rfl
  | add _ _ ih₁ ih₂ =>
      change _ ∪ _ = _ ∪ _
      rw [ih₁, ih₂]
  | hom name _ ih =>
      change NF.prepend name _ = NF.prepend name _
      rw [ih]

end DecidableLabels

end ACUIhE.ACUIh
