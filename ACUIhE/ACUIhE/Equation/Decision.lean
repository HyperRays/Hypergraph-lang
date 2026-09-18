import ACUIhE.Equation.Laws
import ACUIhE.Graph.Decision
import ACUIhE.ACUIhNF.Completeness

/-! # Certified equality, inequality, and object-validity decisions -/

namespace ACUIhE

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- The central equality relation is exactly equality of canonical representations. -/
theorem Term.equal_iff_normalize_eq (left right : Term Const Var Hom) :
    left.Equal right ↔ Graph.normalize left = Graph.normalize right :=
  (Graph.normalize_eq_iff_semanticallyEquivalent left right).symm

theorem Term.below_iff_normalize_eq (left right : Term Const Var Hom) :
    left.Below right ↔ Graph.normalize (Term.add left right) = Graph.normalize right :=
  Term.equal_iff_normalize_eq (.add left right) right

theorem Equation.valid_iff_normalize_eq (equation : Equation Const Var Hom) :
    equation.Valid ↔ Graph.normalize equation.left = Graph.normalize equation.right :=
  Term.equal_iff_normalize_eq equation.left equation.right

theorem Inequality.valid_iff_normalize_eq (inequality : Inequality Const Var Hom) :
    inequality.Valid ↔
      Graph.normalize (Term.add inequality.left inequality.right) = Graph.normalize inequality.right :=
  Term.below_iff_normalize_eq inequality.left inequality.right

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Decide validity in the full theory, rather than equality of raw syntax. -/
instance decidableSemanticallyEquivalent (left right : Term Const Var Hom) :
    Decidable (SemanticallyEquivalent left right) :=
  decidable_of_iff (Derives left right) soundness_and_completeness

instance Term.decidableBelow (left right : Term Const Var Hom) : Decidable (left.Below right) :=
  decidable_of_iff (Derives (.add left right) right) (Term.below_iff_derives left right).symm

/-- Decide validity of an equation object, not structural equality of its fields. -/
instance Equation.decidableValid (equation : Equation Const Var Hom) : Decidable equation.Valid :=
  inferInstanceAs (Decidable (equation.left.Equal equation.right))

instance Inequality.decidableValid (inequality : Inequality Const Var Hom) : Decidable inequality.Valid :=
  inferInstanceAs (Decidable (inequality.left.Below inequality.right))

/-- An executable Boolean view of universal equation validity. -/
def Equation.isValid (equation : Equation Const Var Hom) : Bool := Generic.Equation.isValid Term.Equal equation

def Inequality.isValid (inequality : Inequality Const Var Hom) : Bool := Generic.Inequality.isValid Term.add Term.Equal inequality

@[simp] theorem Equation.isValid_eq_true (equation : Equation Const Var Hom) :
    equation.isValid = true ↔ equation.Valid :=
  Generic.Equation.isValid_eq_true Term.Equal equation

@[simp] theorem Equation.isValid_eq_false (equation : Equation Const Var Hom) :
    equation.isValid = false ↔ ¬ equation.Valid :=
  Generic.Equation.isValid_eq_false Term.Equal equation

@[simp] theorem Inequality.isValid_eq_true (inequality : Inequality Const Var Hom) :
    inequality.isValid = true ↔ inequality.Valid :=
  Generic.Inequality.isValid_eq_true Term.add Term.Equal inequality

@[simp] theorem Inequality.isValid_eq_false (inequality : Inequality Const Var Hom) :
    inequality.isValid = false ↔ ¬ inequality.Valid :=
  Generic.Inequality.isValid_eq_false Term.add Term.Equal inequality

@[simp] theorem Inequality.isValid_toEquation (inequality : Inequality Const Var Hom) :
    inequality.toEquation.isValid = inequality.isValid :=
  Generic.Inequality.isValid_toEquation Term.add Term.Equal inequality

end DecidableLabels

end ACUIhE

namespace ACUIhE.ACUIh

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- ACUIh validity is decided using the fragment's own normal form. -/
instance decidableSemanticallyEquivalent (left right : Term Const Var Hom) :
    Decidable (SemanticallyEquivalent left right) :=
  decidable_of_iff (Derives left right) soundness_and_completeness

instance Term.decidableBelow (left right : Term Const Var Hom) : Decidable (left.Below right) :=
  decidable_of_iff (Derives (.add left right) right) (Term.below_iff_derives left right).symm

/-- The central equality relation is exactly equality of canonical representations. -/
theorem Term.equal_iff_normalize_eq (left right : Term Const Var Hom) :
    left.Equal right ↔ left.normalize = right.normalize :=
  NF.normalize_eq_iff_semanticallyEquivalent.symm

theorem Term.below_iff_normalize_eq (left right : Term Const Var Hom) :
    left.Below right ↔ (Term.add left right).normalize = right.normalize :=
  Term.equal_iff_normalize_eq (.add left right) right

theorem Equation.valid_iff_normalize_eq (equation : Equation Const Var Hom) :
    equation.Valid ↔ equation.left.normalize = equation.right.normalize :=
  Term.equal_iff_normalize_eq equation.left equation.right

theorem Inequality.valid_iff_normalize_eq (inequality : Inequality Const Var Hom) :
    inequality.Valid ↔
      (Term.add inequality.left inequality.right).normalize = inequality.right.normalize :=
  Term.below_iff_normalize_eq inequality.left inequality.right

/-- Decide validity of an equation object, not structural equality of its fields. -/
instance Equation.decidableValid (equation : Equation Const Var Hom) : Decidable equation.Valid :=
  inferInstanceAs (Decidable (equation.left.Equal equation.right))

instance Inequality.decidableValid (inequality : Inequality Const Var Hom) : Decidable inequality.Valid :=
  inferInstanceAs (Decidable (inequality.left.Below inequality.right))

/-- An executable Boolean view of universal equation validity. -/
def Equation.isValid (equation : Equation Const Var Hom) : Bool := Generic.Equation.isValid Term.Equal equation

def Inequality.isValid (inequality : Inequality Const Var Hom) : Bool := Generic.Inequality.isValid Term.add Term.Equal inequality

@[simp] theorem Equation.isValid_eq_true (equation : Equation Const Var Hom) :
    equation.isValid = true ↔ equation.Valid :=
  Generic.Equation.isValid_eq_true Term.Equal equation

@[simp] theorem Equation.isValid_eq_false (equation : Equation Const Var Hom) :
    equation.isValid = false ↔ ¬ equation.Valid :=
  Generic.Equation.isValid_eq_false Term.Equal equation

@[simp] theorem Inequality.isValid_eq_true (inequality : Inequality Const Var Hom) :
    inequality.isValid = true ↔ inequality.Valid :=
  Generic.Inequality.isValid_eq_true Term.add Term.Equal inequality

@[simp] theorem Inequality.isValid_eq_false (inequality : Inequality Const Var Hom) :
    inequality.isValid = false ↔ ¬ inequality.Valid :=
  Generic.Inequality.isValid_eq_false Term.add Term.Equal inequality

@[simp] theorem Inequality.isValid_toEquation (inequality : Inequality Const Var Hom) :
    inequality.toEquation.isValid = inequality.isValid :=
  Generic.Inequality.isValid_toEquation Term.add Term.Equal inequality

end DecidableLabels

end ACUIhE.ACUIh

namespace ACUIhE.ACUIE

universe u v w x

variable {Const : Type u} {Var : Type v}

/-- Canonical graphs decide ACUIE equality through a semantically faithful embedding. -/
theorem semanticallyEquivalent_iff_normalize_eq (left right : Term Const Var) :
    SemanticallyEquivalent left right ↔
      Graph.normalize (left.toACUIhE (Hom := Empty)) = Graph.normalize right.toACUIhE :=
  (semanticallyEquivalent_iff_toACUIhE left right).trans
    (Graph.normalize_eq_iff_semanticallyEquivalent _ _).symm

/-- The central equality relation is exactly equality of canonical representations. -/
theorem Term.equal_iff_normalize_eq (left right : Term Const Var) :
    left.Equal right ↔ Graph.normalize (left.toACUIhE (Hom := Empty)) = Graph.normalize (right.toACUIhE (Hom := Empty)) :=
  semanticallyEquivalent_iff_normalize_eq left right

theorem Term.below_iff_normalize_eq (left right : Term Const Var) :
    left.Below right ↔ Graph.normalize ((Term.add left right).toACUIhE (Hom := Empty)) = Graph.normalize (right.toACUIhE (Hom := Empty)) :=
  Term.equal_iff_normalize_eq (.add left right) right

theorem Equation.valid_iff_normalize_eq (equation : Equation Const Var) :
    equation.Valid ↔ Graph.normalize (equation.left.toACUIhE (Hom := Empty)) = Graph.normalize (equation.right.toACUIhE (Hom := Empty)) :=
  Term.equal_iff_normalize_eq equation.left equation.right

theorem Inequality.valid_iff_normalize_eq (inequality : Inequality Const Var) :
    inequality.Valid ↔
      Graph.normalize ((Term.add inequality.left inequality.right).toACUIhE (Hom := Empty)) = Graph.normalize (inequality.right.toACUIhE (Hom := Empty)) :=
  Term.below_iff_normalize_eq inequality.left inequality.right

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var]

/-- ACUIE semantic equality is decided by graphs with no homomorphism labels. -/
instance decidableSemanticallyEquivalent (left right : Term Const Var) :
    Decidable (SemanticallyEquivalent left right) :=
  decidable_of_iff
    (Graph.normalize (left.toACUIhE (Hom := Empty)) = Graph.normalize right.toACUIhE)
    (semanticallyEquivalent_iff_normalize_eq left right).symm

instance Term.decidableBelow (left right : Term Const Var) : Decidable (left.Below right) :=
  decidable_of_iff (SemanticallyEquivalent (.add left right) right)
    (Term.below_iff_semanticallyEquivalent left right).symm

/-- Decide validity of an equation object, not structural equality of its fields. -/
instance Equation.decidableValid (equation : Equation Const Var) : Decidable equation.Valid :=
  inferInstanceAs (Decidable (equation.left.Equal equation.right))

instance Inequality.decidableValid (inequality : Inequality Const Var) : Decidable inequality.Valid :=
  inferInstanceAs (Decidable (inequality.left.Below inequality.right))

/-- An executable Boolean view of universal equation validity. -/
def Equation.isValid (equation : Equation Const Var) : Bool := Generic.Equation.isValid Term.Equal equation

def Inequality.isValid (inequality : Inequality Const Var) : Bool := Generic.Inequality.isValid Term.add Term.Equal inequality

@[simp] theorem Equation.isValid_eq_true (equation : Equation Const Var) :
    equation.isValid = true ↔ equation.Valid :=
  Generic.Equation.isValid_eq_true Term.Equal equation

@[simp] theorem Equation.isValid_eq_false (equation : Equation Const Var) :
    equation.isValid = false ↔ ¬ equation.Valid :=
  Generic.Equation.isValid_eq_false Term.Equal equation

@[simp] theorem Inequality.isValid_eq_true (inequality : Inequality Const Var) :
    inequality.isValid = true ↔ inequality.Valid :=
  Generic.Inequality.isValid_eq_true Term.add Term.Equal inequality

@[simp] theorem Inequality.isValid_eq_false (inequality : Inequality Const Var) :
    inequality.isValid = false ↔ ¬ inequality.Valid :=
  Generic.Inequality.isValid_eq_false Term.add Term.Equal inequality

@[simp] theorem Inequality.isValid_toEquation (inequality : Inequality Const Var) :
    inequality.toEquation.isValid = inequality.isValid :=
  Generic.Inequality.isValid_toEquation Term.add Term.Equal inequality

end DecidableLabels

end ACUIhE.ACUIE
