import ACUIhE.ACUIh
import ACUIhE.ACUIE
import ACUIhE.Equation.Generic

/-!
# Equality, additive inequality, and unevaluated equation objects

These definitions depend only on the algebra signatures and raw syntax.
`Term.Equal` means equality in every model of the corresponding theory;
`Term.Below a b` means `Term.Equal (.add a b) b`. The historical name
`SemanticallyEquivalent` is an alias, not a second notion of equality.

An `Equation` or `Inequality` stores two raw terms, with no groundness or
validity requirement. `Holds` concerns one interpretation; `Valid` concerns
all interpretations. Neither is raw syntactic equality of the stored objects.
Solvedness is added by `ACUIhE.Solution`, which also requires ground sides.

Each fragment specializes the objects and proof helpers from `Equation.Generic`.
The familiar constructors, projections, and theorem names remain available.
-/

namespace ACUIhE

universe u v w x

/-- The additive order on algebra elements, independent of the other operators. -/
def Below {α : Type u} [Add α] (a b : α) : Prop := a + b = b

scoped infix:50 " ≤₊ " => Below
scoped infix:50 " <=_+ " => Below

end ACUIhE

namespace ACUIhE

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- Equality valid under every interpretation in this theory, not raw syntax equality. -/
def Term.Equal (left right : Term Const Var Hom) : Prop :=
  ∀ {α : Type (max (max u v) w)} [ACUIhE Hom α]
      (interpretConst : Const → α) (interpretVar : Var → α),
    left.eval interpretConst interpretVar = right.eval interpretConst interpretVar

/-- Compatibility name for the central term equality relation. -/
abbrev SemanticallyEquivalent (left right : Term Const Var Hom) : Prop := left.Equal right

/-- Additive inequality is the equality `left + right = right`. -/
def Term.Below (left right : Term Const Var Hom) : Prop := (Term.add left right).Equal right

theorem Term.below_iff_equal_add (left right : Term Const Var Hom) :
    left.Below right ↔ (Term.add left right).Equal right := Iff.rfl

/-- An equation to be considered or solved; its sides need not already be equal. -/
abbrev Equation (Const : Type u) (Var : Type v) (Hom : Type w) := Generic.Equation (Term Const Var Hom)

/-- Compatibility constructor for the fragment-specialized object. -/
abbrev Equation.mk (left right : Term Const Var Hom) : Equation Const Var Hom :=
  Generic.Equation.mk left right

abbrev Equation.left (q : Equation Const Var Hom) : Term Const Var Hom := Generic.Equation.left q

abbrev Equation.right (q : Equation Const Var Hom) : Term Const Var Hom := Generic.Equation.right q

/-- An additive inequality to be considered or solved, with unconstrained sides. -/
abbrev Inequality (Const : Type u) (Var : Type v) (Hom : Type w) := Generic.Inequality (Term Const Var Hom)

/-- Compatibility constructor for the fragment-specialized object. -/
abbrev Inequality.mk (left right : Term Const Var Hom) : Inequality Const Var Hom :=
  Generic.Inequality.mk left right

abbrev Inequality.left (q : Inequality Const Var Hom) : Term Const Var Hom := Generic.Inequality.left q

abbrev Inequality.right (q : Inequality Const Var Hom) : Term Const Var Hom := Generic.Inequality.right q

/-- Truth of an equation in a particular model and interpretation. -/
def Equation.Holds {α : Type x} [ACUIhE Hom α] (equation : Equation Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Prop :=
  Generic.Equation.Holds (Term.eval ic iv) equation

/-- Universal validity, without requiring groundness. -/
abbrev Equation.Valid (equation : Equation Const Var Hom) : Prop :=
  Generic.Equation.Valid Term.Equal equation

/-- Truth of an inequality in a particular model and interpretation. -/
def Inequality.Holds {α : Type x} [ACUIhE Hom α] (inequality : Inequality Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Prop :=
  Generic.Inequality.Holds (· + ·) (Term.eval ic iv) inequality

/-- Universal additive validity, without requiring groundness. -/
abbrev Inequality.Valid (inequality : Inequality Const Var Hom) : Prop :=
  Generic.Inequality.Valid Term.add Term.Equal inequality

/-- Express an inequality as the equivalent equation `left + right = right`. -/
def Inequality.toEquation (inequality : Inequality Const Var Hom) : Equation Const Var Hom :=
  Generic.Inequality.toEquation Term.add inequality

@[simp] theorem Inequality.valid_toEquation (inequality : Inequality Const Var Hom) :
    inequality.toEquation.Valid ↔ inequality.Valid :=
  Generic.Inequality.valid_toEquation Term.add Term.Equal inequality

@[simp] theorem Inequality.holds_toEquation {α : Type x} [ACUIhE Hom α]
    (inequality : Inequality Const Var Hom) (ic : Const → α) (iv : Var → α) :
    inequality.toEquation.Holds ic iv ↔ inequality.Holds ic iv :=
  Generic.Inequality.holds_toEquation (fun _ _ => rfl) inequality

/-- Reverse the sides of an equation, without claiming its validity. -/
def Equation.swap (equation : Equation Const Var Hom) : Equation Const Var Hom :=
  Generic.Equation.swap equation

@[simp] theorem Equation.swap_swap (equation : Equation Const Var Hom) :
    equation.swap.swap = equation :=
  Generic.Equation.swap_swap equation

@[simp] theorem Equation.holds_swap {α : Type x} [ACUIhE Hom α]
    (equation : Equation Const Var Hom) (ic : Const → α) (iv : Var → α) :
    equation.swap.Holds ic iv ↔ equation.Holds ic iv :=
  Generic.Equation.holds_swap (Term.eval ic iv) equation

theorem Equation.Valid.holds {α : Type (max (max u v) w)} [ACUIhE Hom α]
    {equation : Equation Const Var Hom} (valid : equation.Valid) (ic : Const → α) (iv : Var → α) :
    equation.Holds ic iv :=
  Generic.Equation.Valid.holds (Equal := Term.Equal) (fun h => h ic iv) valid

theorem Inequality.Valid.holds {α : Type (max (max u v) w)} [ACUIhE Hom α]
    {inequality : Inequality Const Var Hom} (valid : inequality.Valid) (ic : Const → α) (iv : Var → α) :
    inequality.Holds ic iv :=
  Generic.Inequality.Valid.holds (Equal := Term.Equal) (add := Term.add)
    (fun h => h ic iv) (fun _ _ => rfl) valid

/-- Satisfaction in a given model is decidable when that model has decidable equality. -/
instance Equation.decidableHolds {α : Type x} [ACUIhE Hom α] [DecidableEq α]
    (equation : Equation Const Var Hom) (ic : Const → α) (iv : Var → α) :
    Decidable (equation.Holds ic iv) :=
  inferInstanceAs (Decidable (equation.left.eval ic iv = equation.right.eval ic iv))

instance Inequality.decidableHolds {α : Type x} [ACUIhE Hom α] [DecidableEq α]
    (inequality : Inequality Const Var Hom) (ic : Const → α) (iv : Var → α) :
    Decidable (inequality.Holds ic iv) :=
  inferInstanceAs (Decidable
    (inequality.left.eval ic iv + inequality.right.eval ic iv = inequality.right.eval ic iv))

end ACUIhE

namespace ACUIhE.ACUIh

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- Equality valid under every interpretation in this theory, not raw syntax equality. -/
def Term.Equal (left right : Term Const Var Hom) : Prop :=
  ∀ {α : Type (max (max u v) w)} [ACUIh Hom α]
      (interpretConst : Const → α) (interpretVar : Var → α),
    left.eval interpretConst interpretVar = right.eval interpretConst interpretVar

/-- Compatibility name for the central term equality relation. -/
abbrev SemanticallyEquivalent (left right : Term Const Var Hom) : Prop := left.Equal right

/-- Additive inequality is the equality `left + right = right`. -/
def Term.Below (left right : Term Const Var Hom) : Prop := (Term.add left right).Equal right

theorem Term.below_iff_equal_add (left right : Term Const Var Hom) :
    left.Below right ↔ (Term.add left right).Equal right := Iff.rfl

/-- An equation to be considered or solved; its sides need not already be equal. -/
abbrev Equation (Const : Type u) (Var : Type v) (Hom : Type w) := Generic.Equation (Term Const Var Hom)

/-- Compatibility constructor for the fragment-specialized object. -/
abbrev Equation.mk (left right : Term Const Var Hom) : Equation Const Var Hom :=
  Generic.Equation.mk left right

abbrev Equation.left (q : Equation Const Var Hom) : Term Const Var Hom := Generic.Equation.left q

abbrev Equation.right (q : Equation Const Var Hom) : Term Const Var Hom := Generic.Equation.right q

/-- An additive inequality to be considered or solved, with unconstrained sides. -/
abbrev Inequality (Const : Type u) (Var : Type v) (Hom : Type w) := Generic.Inequality (Term Const Var Hom)

/-- Compatibility constructor for the fragment-specialized object. -/
abbrev Inequality.mk (left right : Term Const Var Hom) : Inequality Const Var Hom :=
  Generic.Inequality.mk left right

abbrev Inequality.left (q : Inequality Const Var Hom) : Term Const Var Hom := Generic.Inequality.left q

abbrev Inequality.right (q : Inequality Const Var Hom) : Term Const Var Hom := Generic.Inequality.right q

/-- Truth of an equation in a particular model and interpretation. -/
def Equation.Holds {α : Type x} [ACUIh Hom α] (equation : Equation Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Prop :=
  Generic.Equation.Holds (Term.eval ic iv) equation

/-- Universal validity, without requiring groundness. -/
abbrev Equation.Valid (equation : Equation Const Var Hom) : Prop :=
  Generic.Equation.Valid Term.Equal equation

/-- Truth of an inequality in a particular model and interpretation. -/
def Inequality.Holds {α : Type x} [ACUIh Hom α] (inequality : Inequality Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Prop :=
  Generic.Inequality.Holds (· + ·) (Term.eval ic iv) inequality

/-- Universal additive validity, without requiring groundness. -/
abbrev Inequality.Valid (inequality : Inequality Const Var Hom) : Prop :=
  Generic.Inequality.Valid Term.add Term.Equal inequality

/-- Express an inequality as the equivalent equation `left + right = right`. -/
def Inequality.toEquation (inequality : Inequality Const Var Hom) : Equation Const Var Hom :=
  Generic.Inequality.toEquation Term.add inequality

@[simp] theorem Inequality.valid_toEquation (inequality : Inequality Const Var Hom) :
    inequality.toEquation.Valid ↔ inequality.Valid :=
  Generic.Inequality.valid_toEquation Term.add Term.Equal inequality

@[simp] theorem Inequality.holds_toEquation {α : Type x} [ACUIh Hom α]
    (inequality : Inequality Const Var Hom) (ic : Const → α) (iv : Var → α) :
    inequality.toEquation.Holds ic iv ↔ inequality.Holds ic iv :=
  Generic.Inequality.holds_toEquation (fun _ _ => rfl) inequality

/-- Reverse the sides of an equation, without claiming its validity. -/
def Equation.swap (equation : Equation Const Var Hom) : Equation Const Var Hom :=
  Generic.Equation.swap equation

@[simp] theorem Equation.swap_swap (equation : Equation Const Var Hom) :
    equation.swap.swap = equation :=
  Generic.Equation.swap_swap equation

@[simp] theorem Equation.holds_swap {α : Type x} [ACUIh Hom α]
    (equation : Equation Const Var Hom) (ic : Const → α) (iv : Var → α) :
    equation.swap.Holds ic iv ↔ equation.Holds ic iv :=
  Generic.Equation.holds_swap (Term.eval ic iv) equation

theorem Equation.Valid.holds {α : Type (max (max u v) w)} [ACUIh Hom α]
    {equation : Equation Const Var Hom} (valid : equation.Valid) (ic : Const → α) (iv : Var → α) :
    equation.Holds ic iv :=
  Generic.Equation.Valid.holds (Equal := Term.Equal) (fun h => h ic iv) valid

theorem Inequality.Valid.holds {α : Type (max (max u v) w)} [ACUIh Hom α]
    {inequality : Inequality Const Var Hom} (valid : inequality.Valid) (ic : Const → α) (iv : Var → α) :
    inequality.Holds ic iv :=
  Generic.Inequality.Valid.holds (Equal := Term.Equal) (add := Term.add)
    (fun h => h ic iv) (fun _ _ => rfl) valid

/-- Satisfaction in a given model is decidable when that model has decidable equality. -/
instance Equation.decidableHolds {α : Type x} [ACUIh Hom α] [DecidableEq α]
    (equation : Equation Const Var Hom) (ic : Const → α) (iv : Var → α) :
    Decidable (equation.Holds ic iv) :=
  inferInstanceAs (Decidable (equation.left.eval ic iv = equation.right.eval ic iv))

instance Inequality.decidableHolds {α : Type x} [ACUIh Hom α] [DecidableEq α]
    (inequality : Inequality Const Var Hom) (ic : Const → α) (iv : Var → α) :
    Decidable (inequality.Holds ic iv) :=
  inferInstanceAs (Decidable
    (inequality.left.eval ic iv + inequality.right.eval ic iv = inequality.right.eval ic iv))

end ACUIhE.ACUIh

namespace ACUIhE.ACUIE

universe u v w x

variable {Const : Type u} {Var : Type v}

/-- Equality valid under every interpretation in this theory, not raw syntax equality. -/
def Term.Equal (left right : Term Const Var) : Prop :=
  ∀ {α : Type (max u v)} [ACUIE α]
      (interpretConst : Const → α) (interpretVar : Var → α),
    left.eval interpretConst interpretVar = right.eval interpretConst interpretVar

/-- Compatibility name for the central term equality relation. -/
abbrev SemanticallyEquivalent (left right : Term Const Var) : Prop := left.Equal right

/-- Additive inequality is the equality `left + right = right`. -/
def Term.Below (left right : Term Const Var) : Prop := (Term.add left right).Equal right

theorem Term.below_iff_equal_add (left right : Term Const Var) :
    left.Below right ↔ (Term.add left right).Equal right := Iff.rfl

/-- An equation to be considered or solved; its sides need not already be equal. -/
abbrev Equation (Const : Type u) (Var : Type v) := Generic.Equation (Term Const Var)

/-- Compatibility constructor for the fragment-specialized object. -/
abbrev Equation.mk (left right : Term Const Var) : Equation Const Var :=
  Generic.Equation.mk left right

abbrev Equation.left (q : Equation Const Var) : Term Const Var := Generic.Equation.left q

abbrev Equation.right (q : Equation Const Var) : Term Const Var := Generic.Equation.right q

/-- An additive inequality to be considered or solved, with unconstrained sides. -/
abbrev Inequality (Const : Type u) (Var : Type v) := Generic.Inequality (Term Const Var)

/-- Compatibility constructor for the fragment-specialized object. -/
abbrev Inequality.mk (left right : Term Const Var) : Inequality Const Var :=
  Generic.Inequality.mk left right

abbrev Inequality.left (q : Inequality Const Var) : Term Const Var := Generic.Inequality.left q

abbrev Inequality.right (q : Inequality Const Var) : Term Const Var := Generic.Inequality.right q

/-- Truth of an equation in a particular model and interpretation. -/
def Equation.Holds {α : Type x} [ACUIE α] (equation : Equation Const Var)
    (ic : Const → α) (iv : Var → α) : Prop :=
  Generic.Equation.Holds (Term.eval ic iv) equation

/-- Universal validity, without requiring groundness. -/
abbrev Equation.Valid (equation : Equation Const Var) : Prop :=
  Generic.Equation.Valid Term.Equal equation

/-- Truth of an inequality in a particular model and interpretation. -/
def Inequality.Holds {α : Type x} [ACUIE α] (inequality : Inequality Const Var)
    (ic : Const → α) (iv : Var → α) : Prop :=
  Generic.Inequality.Holds (· + ·) (Term.eval ic iv) inequality

/-- Universal additive validity, without requiring groundness. -/
abbrev Inequality.Valid (inequality : Inequality Const Var) : Prop :=
  Generic.Inequality.Valid Term.add Term.Equal inequality

/-- Express an inequality as the equivalent equation `left + right = right`. -/
def Inequality.toEquation (inequality : Inequality Const Var) : Equation Const Var :=
  Generic.Inequality.toEquation Term.add inequality

@[simp] theorem Inequality.valid_toEquation (inequality : Inequality Const Var) :
    inequality.toEquation.Valid ↔ inequality.Valid :=
  Generic.Inequality.valid_toEquation Term.add Term.Equal inequality

@[simp] theorem Inequality.holds_toEquation {α : Type x} [ACUIE α]
    (inequality : Inequality Const Var) (ic : Const → α) (iv : Var → α) :
    inequality.toEquation.Holds ic iv ↔ inequality.Holds ic iv :=
  Generic.Inequality.holds_toEquation (fun _ _ => rfl) inequality

/-- Reverse the sides of an equation, without claiming its validity. -/
def Equation.swap (equation : Equation Const Var) : Equation Const Var :=
  Generic.Equation.swap equation

@[simp] theorem Equation.swap_swap (equation : Equation Const Var) :
    equation.swap.swap = equation :=
  Generic.Equation.swap_swap equation

@[simp] theorem Equation.holds_swap {α : Type x} [ACUIE α]
    (equation : Equation Const Var) (ic : Const → α) (iv : Var → α) :
    equation.swap.Holds ic iv ↔ equation.Holds ic iv :=
  Generic.Equation.holds_swap (Term.eval ic iv) equation

theorem Equation.Valid.holds {α : Type (max u v)} [ACUIE α]
    {equation : Equation Const Var} (valid : equation.Valid) (ic : Const → α) (iv : Var → α) :
    equation.Holds ic iv :=
  Generic.Equation.Valid.holds (Equal := Term.Equal) (fun h => h ic iv) valid

theorem Inequality.Valid.holds {α : Type (max u v)} [ACUIE α]
    {inequality : Inequality Const Var} (valid : inequality.Valid) (ic : Const → α) (iv : Var → α) :
    inequality.Holds ic iv :=
  Generic.Inequality.Valid.holds (Equal := Term.Equal) (add := Term.add)
    (fun h => h ic iv) (fun _ _ => rfl) valid

/-- Satisfaction in a given model is decidable when that model has decidable equality. -/
instance Equation.decidableHolds {α : Type x} [ACUIE α] [DecidableEq α]
    (equation : Equation Const Var) (ic : Const → α) (iv : Var → α) :
    Decidable (equation.Holds ic iv) :=
  inferInstanceAs (Decidable (equation.left.eval ic iv = equation.right.eval ic iv))

instance Inequality.decidableHolds {α : Type x} [ACUIE α] [DecidableEq α]
    (inequality : Inequality Const Var) (ic : Const → α) (iv : Var → α) :
    Decidable (inequality.Holds ic iv) :=
  inferInstanceAs (Decidable
    (inequality.left.eval ic iv + inequality.right.eval ic iv = inequality.right.eval ic iv))

end ACUIhE.ACUIE
