import ACUIhE.Definition

/-!
# The ACUIE fragment

ACUIE retains the ACUI operation and the injective, bottom-preserving `E`
operator from ACUIhE. Its algebra class and raw terms have no homomorphism
parameter. No distributivity or monotonicity law is imposed on `E`.
-/

namespace ACUIhE

universe u v w

/--
An associative, commutative, unital, idempotent operation with an injective
unary operator whose only additional required law is `E(0) = 0`.
Injectivity is a conditional axiom; individual models may satisfy further
identities, so an instance need not itself be a free algebra.
-/
class ACUIE (α : Type u) extends Add α, Zero α where
  free : α → α
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + 0 = a
  add_idem : ∀ a : α, a + a = a
  free_zero : free 0 = 0
  free_injective : Function.Injective free

namespace ACUIE

/-- The bottom-preserving, injective operator of an ACUIE algebra. -/
def E {α : Type u} [ACUIE α] : α → α := ACUIE.free

/-- The operator `E` preserves zero. -/
@[simp] theorem E_zero {α : Type u} [ACUIE α] : E (0 : α) = 0 :=
  ACUIE.free_zero

/-- The operator `E` is injective. -/
theorem E_injective {α : Type u} [ACUIE α] :
    Function.Injective (E (α := α)) :=
  ACUIE.free_injective

/-- The operator `E` also reflects zero. -/
@[simp] theorem E_eq_zero_iff {α : Type u} [ACUIE α] (a : α) :
    E a = 0 ↔ a = 0 := by
  constructor
  · intro equality
    exact E_injective (equality.trans E_zero.symm)
  · intro equality
    rw [equality, E_zero]

/-- Raw ACUIE terms: the ACUIhE signature without homomorphisms. -/
inductive Term (Const : Type u) (Var : Type v) : Type (max u v) where
  | zero : Term Const Var
  | const (name : Const) : Term Const Var
  | var (name : Var) : Term Const Var
  | add (left right : Term Const Var) : Term Const Var
  | free (body : Term Const Var) : Term Const Var

/-- Interpret a raw term using only an ACUIE algebra. -/
def Term.eval {Const : Type v} {Var : Type w} {α : Type u} [ACUIE α]
    (interpretConst : Const → α) (interpretVar : Var → α) :
    Term Const Var → α
  | .zero => 0
  | .const name => interpretConst name
  | .var name => interpretVar name
  | .add left right =>
      left.eval interpretConst interpretVar + right.eval interpretConst interpretVar
  | .free body => E (body.eval interpretConst interpretVar)

/-- Include an ACUIE term in the full syntax for any homomorphism-name type. -/
def Term.toACUIhE {Const : Type u} {Var : Type v} {Hom : Type w} :
    Term Const Var → _root_.ACUIhE.Term Const Var Hom
  | .zero => .zero
  | .const name => .const name
  | .var name => .var name
  | .add left right => .add left.toACUIhE right.toACUIhE
  | .free body => .free body.toACUIhE

/-- The inclusion preserves distinct raw terms. -/
theorem Term.toACUIhE_injective {Const : Type u} {Var : Type v} {Hom : Type w} :
    Function.Injective (Term.toACUIhE (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro left
  induction left with
  | zero | const | var =>
      intro right equality
      cases right <;> simp_all [Term.toACUIhE]
  | add left right leftHypothesis rightHypothesis =>
      intro other equality
      cases other with
      | add otherLeft otherRight =>
          have parts := _root_.ACUIhE.Term.add.inj equality
          exact congr (congrArg Term.add (leftHypothesis parts.1))
            (rightHypothesis parts.2)
      | zero | const | var | free => cases equality
  | free body inductionHypothesis =>
      intro other equality
      cases other with
      | free otherBody =>
          exact congrArg Term.free
            (inductionHypothesis (_root_.ACUIhE.Term.free.inj equality))
      | zero | const | var | add => cases equality

end ACUIE

end ACUIhE
