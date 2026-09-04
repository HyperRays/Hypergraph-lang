namespace ACUIHE

universe u v w x

/-- Raw terms in the ACUIhE signature, with explicitly named homomorphisms. -/
inductive Term (Const : Type u) (Var : Type v) (Hom : Type w) :
    Type (max (max u v) w) where
  | zero : Term Const Var Hom
  | const (name : Const) : Term Const Var Hom
  | var (name : Var) : Term Const Var Hom
  | add (left right : Term Const Var Hom) : Term Const Var Hom
  | hom (name : Hom) (body : Term Const Var Hom) : Term Const Var Hom
  | free (body : Term Const Var Hom) : Term Const Var Hom

/--
An ACUIhE algebra: an associative, commutative, unital, idempotent
operation together with a family of named homomorphic operators and a
bottom-preserving, injective, otherwise-free operator.
-/
class ACUIhE (Hom : Type v) (α : Type u) extends Add α, Zero α where
  hom : Hom → α → α
  free : α → α
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + 0 = a
  add_idem : ∀ a : α, a + a = a
  hom_add : ∀ (name : Hom) (a b : α),
    hom name (a + b) = hom name a + hom name b
  hom_zero : ∀ name : Hom, hom name 0 = 0
  free_zero : free 0 = 0
  free_injective : Function.Injective free

/-- The homomorphic operator with the given name. -/
def H {Hom : Type v} {α : Type u} [ACUIhE Hom α] (name : Hom) : α → α :=
  ACUIhE.hom name

/-- The bottom-preserving free operator `E`. -/
def E {Hom : Type v} {α : Type u} [ACUIhE Hom α] : α → α :=
  ACUIhE.free Hom

/-- The otherwise-free operator `E` is injective. -/
theorem E_injective {Hom : Type v} {α : Type u} [ACUIhE Hom α] :
    Function.Injective (E (Hom := Hom) (α := α)) :=
  ACUIhE.free_injective (Hom := Hom) (α := α)

/-- Repeated application of a unary operator. -/
def iterate {α : Type u} (f : α → α) : Nat → α → α
  | 0 => fun a => a
  | n + 1 => fun a => f (iterate f n a)

/-- `h_name^k(a)`. -/
def hPow {Hom : Type v} {α : Type u} [ACUIhE Hom α]
    (name : Hom) (k : Nat) (a : α) : α :=
  iterate (H name) k a

/-- `E^k(a)`. -/
def ePow {Hom : Type v} {α : Type u} [ACUIhE Hom α] (k : Nat) (a : α) : α :=
  iterate (E (Hom := Hom)) k a

/-- The semilattice order induced by addition: `a ≤ b` iff `a + b = b`. -/
def Below {Hom : Type v} {α : Type u} [ACUIhE Hom α] (a b : α) : Prop :=
  a + b = b

/-- The derived operator `S_h(T) = c + h(T)`. -/
def S {Hom : Type v} {α : Type u} [ACUIhE Hom α]
    (name : Hom) (c t : α) : α :=
  c + H name t

/-- Sum a finite list using the ACUI operation. -/
def sum {Hom : Type v} {α : Type u} [ACUIhE Hom α] : List α → α
  | [] => 0
  | a :: as => a + sum (Hom := Hom) as

/-- Apply the successive named homomorphisms `h₁`, `h₂`, ... to arguments. -/
def taggedArguments {Hom : Type v} {α : Type u} [ACUIhE Hom α]
    (homNames : Nat → Hom) : Nat → List α → α
  | _, [] => 0
  | index, a :: as =>
      H (homNames index) a + taggedArguments homNames (index + 1) as

/--
The family
`O_i(A₁, ..., Aₙ) = E(c_i + h₁(A₁) + ... + hₙ(Aₙ))`.

The map `homNames` supplies the name of `hₖ`; indexing starts at one.
-/
def O {ι : Type w} {Hom : Type v} {α : Type u} [ACUIhE Hom α]
    (constants : ι → α) (homNames : Nat → Hom)
    (i : ι) (arguments : List α) : α :=
  E (Hom := Hom) (constants i + taggedArguments homNames 1 arguments)

/-- Interpret a raw term in an ACUIhE algebra. -/
def Term.eval {Const : Type v} {Var : Type w} {Hom : Type x}
    {α : Type u} [ACUIhE Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α) :
    Term Const Var Hom → α
  | .zero => 0
  | .const name => interpretConst name
  | .var name => interpretVar name
  | .add left right =>
      left.eval interpretConst interpretVar + right.eval interpretConst interpretVar
  | .hom name body => H name (body.eval interpretConst interpretVar)
  | .free body => E (Hom := Hom) (body.eval interpretConst interpretVar)

end ACUIHE
