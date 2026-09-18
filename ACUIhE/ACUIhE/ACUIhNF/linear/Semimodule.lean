import ACUIhE.ACUIhNF.Definition
import ACUIhE.ACUIhNF.linear.Semiring
import Mathlib.Algebra.Module.Defs

/-!
# The semimodule of ACUIh normal forms

The coefficient action concatenates each scalar word with each normal-form
word, retaining its particle. The additive monoid and `Module` structures
are explicit values, so importing this module does not install union as
global addition on finsets. Mathlib's `Module` over a `Semiring` is a
semimodule in the usual terminology.
-/

namespace ACUIhE.ACUIh.Linear

universe u v w

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Apply a finite set of homomorphism words to a normal form. -/
def act (coefficient : WordPolynomial Hom) (normal : NF Const Var Hom) : NF Const Var Hom :=
  Finset.image₂ (fun word summand => (word ++ summand.1, summand.2)) coefficient.words normal

/-- Membership describes the action without choosing any enumeration. -/
theorem mem_act (coefficient : WordPolynomial Hom) (normal : NF Const Var Hom)
    (summand : Summand Const Var Hom) :
    summand ∈ act coefficient normal ↔
      ∃ word ∈ coefficient.words, ∃ body ∈ normal,
        (word ++ body.1, body.2) = summand :=
  Finset.mem_image₂

@[simp] theorem act_zero (normal : NF Const Var Hom) : act (0 : WordPolynomial Hom) normal = ∅ :=
  Finset.image₂_empty_left

@[simp] theorem act_empty (coefficient : WordPolynomial Hom) :
    act coefficient (∅ : NF Const Var Hom) = ∅ := Finset.image₂_empty_right

@[simp] theorem act_one (normal : NF Const Var Hom) : act (1 : WordPolynomial Hom) normal = normal := by
  simp [act]

theorem act_add (left right : WordPolynomial Hom) (normal : NF Const Var Hom) :
    act (left + right) normal = act left normal ∪ act right normal :=
  Finset.image₂_union_left

theorem act_union (coefficient : WordPolynomial Hom) (left right : NF Const Var Hom) :
    act coefficient (left ∪ right) = act coefficient left ∪ act coefficient right :=
  Finset.image₂_union_right

/-- Scalar multiplication is compatible with concatenation of coefficient words. -/
theorem act_mul (left right : WordPolynomial Hom) (normal : NF Const Var Hom) :
    act (left * right) normal = act left (act right normal) := by
  apply Finset.image₂_assoc
  intro leftWord rightWord summand
  exact congrArg (fun word => (word, summand.2))
    (List.append_assoc leftWord rightWord summand.1)

/-- Union and the empty set give the additive monoid of normal forms. -/
@[instance_reducible] def normalFormAddCommMonoid : AddCommMonoid (NF Const Var Hom) := by
  letI : Zero (NF Const Var Hom) := ⟨∅⟩
  letI : Add (NF Const Var Hom) := ⟨(· ∪ ·)⟩
  exact
    { add_assoc := Finset.union_assoc
      zero_add := Finset.empty_union
      add_zero := Finset.union_empty
      add_comm := Finset.union_comm
      nsmul := nsmulRec }

attribute [local instance] normalFormAddCommMonoid

/-- Install locally after `normalFormAddCommMonoid` to use standard semimodule notation and laws. -/
@[instance_reducible] def normalFormModule : Module (WordPolynomial Hom) (NF Const Var Hom) where
  smul := act
  one_smul := act_one
  mul_smul := act_mul
  smul_add := act_union
  smul_zero := act_empty
  add_smul := act_add
  zero_smul := act_zero

/-- The action of one named generator is the existing normal-form homomorphism. -/
@[simp] theorem act_generator (name : Hom) (normal : NF Const Var Hom) :
    act (WordPolynomial.generator name) normal = NF.prepend name normal := by
  simp only [act, WordPolynomial.generator, WordPolynomial.monomial_words,
    Finset.image₂_singleton_left, NF.prepend, Finset.map_eq_image]
  rfl

/-- A word beginning with a name first acts by its tail and then by that name. -/
theorem act_monomial_cons (name : Hom) (word : List Hom) (normal : NF Const Var Hom) :
    act (WordPolynomial.monomial (name :: word)) normal =
      NF.prepend name (act (WordPolynomial.monomial word) normal) := by
  rw [← act_generator, ← act_mul]
  simp only [WordPolynomial.generator, WordPolynomial.monomial_mul, List.singleton_append]

/-- One step of finite-set induction on the coefficient, allowing repeated words. -/
theorem act_insert (word : List Hom) (words : Finset (List Hom)) (normal : NF Const Var Hom) :
    act ⟨insert word words⟩ normal =
      act (WordPolynomial.monomial word) normal ∪ act ⟨words⟩ normal := by
  simp only [act, WordPolynomial.monomial_words, Finset.image₂_insert_left,
    Finset.image₂_singleton_left]

/-- Word application in the raw syntax agrees with scalar action after normalization. -/
theorem normalize_reifyWord (word : List Hom) (term : Term Const Var Hom) :
    (reifyWord word term).normalize = act (WordPolynomial.monomial word) term.normalize := by
  induction word with
  | nil => simp only [reifyWord, WordPolynomial.monomial_nil, act_one]
  | cons name word ih =>
      simp only [reifyWord, Term.normalize, act_monomial_cons, ih]

end ACUIhE.ACUIh.Linear
