import ACUIhE.ACUIhNF.linear.Semimodule
import ACUIhE.ACUIhNF.Soundness

/-!
# Interpretation of the coefficient action

Words act by composition of the named homomorphisms. Finite word sets act
by joining those results. Interpreting scalar action on normal forms agrees
with this operation in every ACUIh algebra, in any carrier universe.
-/

namespace ACUIhE.ACUIh.Linear

universe u v w x

variable {Hom : Type w} {α : Type x} [ACUIh Hom α]

/-- Interpret a homomorphism word with its head acting outermost. -/
def evalWord : List Hom → α → α
  | [], a => a
  | name :: word, a => H name (evalWord word a)

@[simp] theorem evalWord_nil (a : α) : evalWord ([] : List Hom) a = a := rfl

@[simp] theorem evalWord_cons (name : Hom) (word : List Hom) (a : α) :
    evalWord (name :: word) a = H name (evalWord word a) := rfl

/-- Concatenation corresponds to composition in the declared outermost-first order. -/
theorem evalWord_append (left right : List Hom) (a : α) :
    evalWord (left ++ right) a = evalWord left (evalWord right a) := by
  induction left with
  | nil => rfl
  | cons name word ih => exact congrArg (H name) ih

@[simp] theorem evalWord_zero (word : List Hom) : evalWord word (0 : α) = 0 := by
  induction word with
  | nil => rfl
  | cons name word ih =>
      rw [evalWord_cons, ih]
      exact ACUIh.hom_zero name

theorem evalWord_add (word : List Hom) (left right : α) :
    evalWord word (left + right) = evalWord word left + evalWord word right := by
  induction word with
  | nil => rfl
  | cons name word ih =>
      simp only [evalWord_cons, ih]
      exact ACUIh.hom_add name _ _

namespace WordPolynomial

local instance : Std.Commutative (fun a b : α => a + b) :=
  ⟨ACUIh.add_comm (Hom := Hom)⟩

local instance : Std.Associative (fun a b : α => a + b) :=
  ⟨ACUIh.add_assoc (Hom := Hom)⟩

local instance : Std.IdempotentOp (fun a b : α => a + b) :=
  ⟨ACUIh.add_idem (Hom := Hom)⟩

/-- Apply every word in a coefficient to an argument and join the results. -/
def eval (coefficient : WordPolynomial Hom) (a : α) : α :=
  coefficient.words.fold (· + ·) 0 (fun word => evalWord word a)

@[simp] theorem eval_zero (a : α) : (0 : WordPolynomial Hom).eval a = 0 := rfl

@[simp] theorem eval_monomial (word : List Hom) (a : α) :
    (monomial word).eval a = evalWord word a := ACUIh.add_zero _

@[simp] theorem eval_one (a : α) : (1 : WordPolynomial Hom).eval a = a := ACUIh.add_zero _

@[simp] theorem eval_insert [DecidableEq Hom] (word : List Hom) (words : Finset (List Hom))
    (a : α) : (WordPolynomial.mk (insert word words)).eval a =
      evalWord word a + (WordPolynomial.mk words).eval a :=
  Finset.fold_insert_idem

end WordPolynomial

variable {Const : Type u} {Var : Type v}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Interpreting one scalar word agrees with applying that word to the interpretation. -/
theorem eval_act_monomial (interpretConst : Const → α) (interpretVar : Var → α)
    (word : List Hom) (normal : NF Const Var Hom) :
    NF.eval interpretConst interpretVar (act (WordPolynomial.monomial word) normal) =
      evalWord word (NF.eval interpretConst interpretVar normal) := by
  induction word with
  | nil => simp only [WordPolynomial.monomial_nil, act_one, evalWord_nil]
  | cons name word ih =>
      rw [act_monomial_cons, NF.eval_prepend, ih, evalWord_cons]

/-- The normal-form action preserves interpretation in every ACUIh algebra. -/
theorem eval_act (interpretConst : Const → α) (interpretVar : Var → α)
    (coefficient : WordPolynomial Hom) (normal : NF Const Var Hom) :
    NF.eval interpretConst interpretVar (act coefficient normal) =
      coefficient.eval (NF.eval interpretConst interpretVar normal) := by
  rcases coefficient with ⟨words⟩
  induction words using Finset.induction_on with
  | empty => exact NF.eval_empty interpretConst interpretVar
  | insert word words _ ih =>
      rw [act_insert, NF.eval_union, eval_act_monomial, ih, WordPolynomial.eval_insert]

/-- Scalar action on normalized syntax has the expected interpretation. -/
theorem eval_act_normalize (interpretConst : Const → α) (interpretVar : Var → α)
    (coefficient : WordPolynomial Hom) (term : Term Const Var Hom) :
    NF.eval interpretConst interpretVar (act coefficient term.normalize) =
      coefficient.eval (term.eval interpretConst interpretVar) := by
  rw [eval_act, Term.eval_normalize]

omit [DecidableEq Const] [DecidableEq Var] in
/-- Coefficient multiplication is interpreted as composition of its unary operations. -/
theorem WordPolynomial.eval_mul (left right : WordPolynomial Hom) (a : α) :
    (left * right).eval a = left.eval (right.eval a) := by
  have equality := eval_act (fun _ : Unit => a) (Empty.elim : Empty → α) left
    (act right ({([], Particle.const ())} : NF Unit Empty Hom))
  rw [← act_mul, eval_act, eval_act] at equality
  simpa only [NF.eval_singleton, Summand.reify, reifyWord, Particle.reify, Term.eval] using equality

omit [DecidableEq Const] [DecidableEq Var] in
/-- Coefficient addition is interpreted as pointwise ACUI addition. -/
theorem WordPolynomial.eval_add (left right : WordPolynomial Hom) (a : α) :
    (left + right).eval a = left.eval a + right.eval a := by
  have equality := NF.eval_union (fun _ : Unit => a) (Empty.elim : Empty → α)
    (act left ({([], Particle.const ())} : NF Unit Empty Hom))
    (act right ({([], Particle.const ())} : NF Unit Empty Hom))
  rw [← act_add, eval_act, eval_act, eval_act] at equality
  simpa only [NF.eval_singleton, Summand.reify, reifyWord, Particle.reify, Term.eval] using equality

end ACUIhE.ACUIh.Linear
