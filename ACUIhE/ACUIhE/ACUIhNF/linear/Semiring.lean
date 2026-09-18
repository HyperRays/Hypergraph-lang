import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.NAry

/-!
# The ACUIh coefficient semiring

Coefficients are finite sets of words of homomorphism names. Addition is
union and multiplication is concatenation of every pair of words. Zero is
the empty set; one is the singleton containing the empty word. A dedicated
type keeps these operations separate from other arithmetic on finsets.
-/

namespace ACUIhE.ACUIh.Linear

universe w

/-- A noncommutative polynomial in homomorphism names with Boolean coefficients. -/
@[ext] structure WordPolynomial (Hom : Type w) where
  words : Finset (List Hom)
  deriving DecidableEq

namespace WordPolynomial

variable {Hom : Type w}

instance : Zero (WordPolynomial Hom) := ⟨⟨∅⟩⟩
instance : One (WordPolynomial Hom) := ⟨⟨{[]}⟩⟩

/-- A single homomorphism word with coefficient one. -/
def monomial (word : List Hom) : WordPolynomial Hom := ⟨{word}⟩

/-- The coefficient representing one application of a named homomorphism. -/
def generator (name : Hom) : WordPolynomial Hom := monomial [name]

@[simp] theorem zero_words : (0 : WordPolynomial Hom).words = ∅ := rfl
@[simp] theorem one_words : (1 : WordPolynomial Hom).words = {[]} := rfl
@[simp] theorem monomial_words (word : List Hom) : (monomial word).words = {word} := rfl
@[simp] theorem monomial_nil : monomial ([] : List Hom) = 1 := rfl

variable [DecidableEq Hom]

instance : Add (WordPolynomial Hom) := ⟨fun p q => ⟨p.words ∪ q.words⟩⟩
instance : Mul (WordPolynomial Hom) :=
  ⟨fun p q => ⟨Finset.image₂ List.append p.words q.words⟩⟩

@[simp] theorem add_words (p q : WordPolynomial Hom) :
    (p + q).words = p.words ∪ q.words := rfl

@[simp] theorem mul_words (p q : WordPolynomial Hom) :
    (p * q).words = Finset.image₂ List.append p.words q.words := rfl

/-- The finite-word-set semiring; no commutativity of multiplication is assumed. -/
instance : Semiring (WordPolynomial Hom) where
  add_assoc p q r := by
    apply WordPolynomial.ext
    exact Finset.union_assoc _ _ _
  zero_add p := by
    apply WordPolynomial.ext
    exact Finset.empty_union _
  add_zero p := by
    apply WordPolynomial.ext
    exact Finset.union_empty _
  add_comm p q := by
    apply WordPolynomial.ext
    exact Finset.union_comm _ _
  mul_assoc p q r := by
    apply WordPolynomial.ext
    exact Finset.image₂_assoc List.append_assoc
  zero_mul p := by
    apply WordPolynomial.ext
    exact Finset.image₂_empty_left
  mul_zero p := by
    apply WordPolynomial.ext
    exact Finset.image₂_empty_right
  one_mul p := by
    apply WordPolynomial.ext
    simp
  mul_one p := by
    apply WordPolynomial.ext
    simp
  left_distrib p q r := by
    apply WordPolynomial.ext
    exact Finset.image₂_union_right
  right_distrib p q r := by
    apply WordPolynomial.ext
    exact Finset.image₂_union_left
  natCast n := if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ n := by
    cases n <;> apply WordPolynomial.ext <;> simp
  nsmul := nsmulRec

/-- Addition, rather than multiplication, is the idempotent operation. -/
@[simp] theorem add_self (p : WordPolynomial Hom) : p + p = p := by
  apply WordPolynomial.ext
  exact Finset.union_self _

/-- Multiplication concatenates words with the left factor outermost. -/
@[simp] theorem monomial_mul (left right : List Hom) :
    monomial left * monomial right = monomial (left ++ right) := by
  apply WordPolynomial.ext
  exact Finset.image₂_singleton

omit [DecidableEq Hom] in
theorem monomial_injective : Function.Injective (monomial (Hom := Hom)) := by
  intro left right equality
  have words := congrArg WordPolynomial.words equality
  simpa using words

/-- Distinct names witness that multiplication need not commute. -/
theorem generators_not_commute {left right : Hom} (different : left ≠ right) :
    generator left * generator right ≠ generator right * generator left := by
  intro equality
  have words := monomial_injective (by simpa only [generator, monomial_mul] using equality)
  exact different (List.cons.inj words).1

end WordPolynomial

end ACUIhE.ACUIh.Linear
