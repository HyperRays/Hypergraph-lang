import ACUIhE.Definition

/-!
# The ACUIh fragment

ACUIh retains the ACUI operation and the named homomorphisms from ACUIhE.
Its algebra class and raw terms do not require an `E` operator.
-/

namespace ACUIhE

universe u v w x

/--
An associative, commutative, unital, idempotent operation with a family of
named homomorphisms. Injectivity and commutation of the homomorphisms are
not required.
-/
class ACUIh (Hom : Type v) (α : Type u) extends Add α, Zero α where
  hom : Hom → α → α
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + 0 = a
  add_idem : ∀ a : α, a + a = a
  hom_add : ∀ (name : Hom) (a b : α),
    hom name (a + b) = hom name a + hom name b
  hom_zero : ∀ name : Hom, hom name 0 = 0

namespace ACUIh

/-- The homomorphic operator with the given name. -/
def H {Hom : Type v} {α : Type u} [ACUIh Hom α] (name : Hom) : α → α :=
  ACUIh.hom name

/-- Raw ACUIh terms: the ACUIhE signature without the free operator. -/
inductive Term (Const : Type u) (Var : Type v) (Hom : Type w) :
    Type (max (max u v) w) where
  | zero : Term Const Var Hom
  | const (name : Const) : Term Const Var Hom
  | var (name : Var) : Term Const Var Hom
  | add (left right : Term Const Var Hom) : Term Const Var Hom
  | hom (name : Hom) (body : Term Const Var Hom) : Term Const Var Hom

/-- Interpret a raw term using only an ACUIh algebra. -/
def Term.eval {Const : Type v} {Var : Type w} {Hom : Type x}
    {α : Type u} [ACUIh Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α) :
    Term Const Var Hom → α
  | .zero => 0
  | .const name => interpretConst name
  | .var name => interpretVar name
  | .add left right =>
      left.eval interpretConst interpretVar + right.eval interpretConst interpretVar
  | .hom name body => H name (body.eval interpretConst interpretVar)

/-- Include an ACUIh term in the full ACUIhE syntax. -/
def Term.toACUIhE {Const : Type u} {Var : Type v} {Hom : Type w} :
    Term Const Var Hom → _root_.ACUIhE.Term Const Var Hom
  | .zero => .zero
  | .const name => .const name
  | .var name => .var name
  | .add left right => .add left.toACUIhE right.toACUIhE
  | .hom name body => .hom name body.toACUIhE

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
      | zero | const | var | hom => cases equality
  | hom name body inductionHypothesis =>
      intro other equality
      cases other with
      | hom otherName otherBody =>
          have parts := _root_.ACUIhE.Term.hom.inj equality
          exact congr (congrArg Term.hom parts.1) (inductionHypothesis parts.2)
      | zero | const | var | add => cases equality

end ACUIh

end ACUIhE
