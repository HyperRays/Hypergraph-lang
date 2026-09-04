import ACUIHE.NormalForm.Core

/-! Ground normal forms and solved inequalities. -/

namespace ACUIHE.Solver

universe u v w

/--
An executable check that a normal form contains no variable atoms.

Groundness is recursive: a normal form containing an `E` atom is ground
exactly when the body of that atom is ground. Homomorphism paths do not affect
groundness.
-/
def NormalForm.isGround
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Bool :=
  normalForm.fold true (fun left right => left && right)
    (fun _ _ => true)
    (fun _ _ => false)
    (fun _ bodyGround => bodyGround)

/-- A normal form is ground when it contains no variable atoms. -/
def NormalForm.IsGround
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) : Prop :=
  normalForm.isGround = true

/--
An inequality of normal forms is solved when both sides are ground and the
left-hand side is below the right-hand side in the ACUI semilattice order.
-/
def IsSolvedInequality
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) : Prop :=
  left.IsGround ∧ right.IsGround ∧ Below (Hom := Hom) left right

end ACUIHE.Solver

namespace ACUIHE.Term

open Solver

universe u v w

/-- A term is ground when its computed normal form contains no variables. -/
def IsGround
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) : Prop :=
  (normalize term).IsGround

/--
A term inequality is solved when its normal forms are ground and the
left-hand normal form is below the right-hand normal form.
-/
def IsSolvedInequality
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : Term Const Var Hom) : Prop :=
  Solver.IsSolvedInequality (normalize left) (normalize right)

end ACUIHE.Term
