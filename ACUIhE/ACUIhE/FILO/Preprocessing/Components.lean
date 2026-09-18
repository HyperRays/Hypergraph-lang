import ACUIhE.FILO.Preprocessing.Language
import ACUIhE.FILO.Preprocessing.Flat

/-!
# Decomposition-variable semantics (§4.4)

Components are named derivatives and constant parts of original variables.
Their interpretation includes both directions of the decreasing rule. It is
not an unconstrained assignment to newly introduced variables.
-/

namespace ACUIhE.FILO.Components

open ACUIh.Linear

universe v w

inductive Variable (Var : Type v) (Hom : Type w) where
  | base : Var → Variable Var Hom
  | role : Hom → Variable Var Hom → Variable Var Hom
  | constant : Variable Var Hom → Variable Var Hom
  deriving DecidableEq

abbrev Atom (Var : Type v) (Hom : Type w) := Flat.Atom Unit (Variable Var Hom)

abbrev Expression (Var : Type v) (Hom : Type w) := List (Atom Var Hom)

abbrev Goal (Var : Type v) (Hom : Type w) := List (Generic.Inequality (Expression Var Hom))

variable {Var : Type v} {Hom : Type w} [DecidableEq Hom]

def interpret (iv : Column Var Hom) : Variable Var Hom → WordPolynomial Hom
  | .base v => iv v
  | .role r x => Language.derivative r (interpret iv x)
  | .constant x => Language.constantPart (interpret iv x)

def atomValue (iv : Column Var Hom) : Atom Var Hom → WordPolynomial Hom
  | .const _ => 1
  | .var x => interpret iv x

def value (iv : Column Var Hom) (ps : Expression Var Hom) : WordPolynomial Hom :=
  (ps.map (atomValue iv)).sum

def Holds (g : Goal Var Hom) (iv : Column Var Hom) : Prop :=
  ∀ q ∈ g, q.Holds (· + ·) (value iv)

@[simp] theorem value_nil (iv : Column Var Hom) : value iv [] = 0 := rfl

@[simp] theorem value_cons (iv : Column Var Hom) (p : Atom Var Hom) (ps : Expression Var Hom) :
    value iv (p :: ps) = atomValue iv p + value iv ps := rfl

@[simp] theorem value_singleton (iv : Column Var Hom) (p : Atom Var Hom) :
    value iv [p] = atomValue iv p := add_zero _

@[simp] theorem value_append (iv : Column Var Hom) (ps qs : Expression Var Hom) :
    value iv (ps ++ qs) = value iv ps + value iv qs := by simp [value]

@[simp] theorem mem_value (iv : Column Var Hom) (ps : Expression Var Hom) (word : List Hom) :
    word ∈ (value iv ps).words ↔ ∃ p ∈ ps, word ∈ (atomValue iv p).words := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [value_cons, WordPolynomial.add_words, Finset.mem_union, ih,
      List.mem_cons, exists_eq_or_imp]

theorem inequality_iff (iv : Column Var Hom) (q : Generic.Inequality (Expression Var Hom)) :
    q.Holds (· + ·) (value iv) ↔ (value iv q.left).words ⊆ (value iv q.right).words := by
  constructor
  · intro h
    exact Finset.union_eq_right.mp (congrArg WordPolynomial.words h)
  · intro h
    exact WordPolynomial.ext (Finset.union_eq_right.mpr h)

theorem interpret_supported (roles : Finset Hom) (iv : Column Var Hom)
    (supported : ∀ v, Language.Supported roles (iv v)) (x : Variable Var Hom) :
    Language.Supported roles (interpret iv x) := by
  induction x with
  | base v => exact supported v
  | role r x ih => exact Language.derivative_supported ih r
  | constant x _ => exact Language.constantPart_supported roles _

def derivative (r : Hom) : Atom Var Hom → Option (Atom Var Hom)
  | .const _ => none
  | .var x => some (.var (.role r x))

def derivatives (r : Hom) (ps : Expression Var Hom) : Expression Var Hom :=
  ps.filterMap (derivative r)

@[simp] theorem value_derivatives (iv : Column Var Hom) (r : Hom) (ps : Expression Var Hom) :
    value iv (derivatives r ps) = Language.derivative r (value iv ps) := by
  induction ps with
  | nil => exact (Language.derivative_zero r).symm
  | cons p ps ih =>
    cases p with
    | const c =>
      change value iv (derivatives r ps) = Language.derivative r (1 + value iv ps)
      rw [Language.derivative_add, Language.derivative_one, zero_add, ih]
    | var x =>
      change Language.derivative r (interpret iv x) + value iv (derivatives r ps) =
        Language.derivative r (interpret iv x + value iv ps)
      rw [Language.derivative_add, ih]

/-- Figure 2.3's expansion of a variable requirement into its components. -/
def splitVariable (roles : List Hom) (available : Expression Var Hom) (x : Variable Var Hom) : Goal Var Hom :=
  ⟨[.var (.constant x)], available⟩ :: roles.map (fun r => ⟨[.var (.role r x)], derivatives r available⟩)

theorem splitVariable_correct (roles : List Hom) (iv : Column Var Hom)
    (available : Expression Var Hom) (x : Variable Var Hom)
    (supported : Language.Supported roles.toFinset (interpret iv x)) :
    Holds (splitVariable roles available x) iv ↔
      (interpret iv x).words ⊆ (value iv available).words := by
  simp only [Holds, splitVariable, List.forall_mem_cons, List.forall_mem_map, inequality_iff,
    value_singleton, atomValue, interpret, value_derivatives]
  rw [Language.constantPart_subset_iff, Language.subset_iff_components roles.toFinset _ _ supported]
  simp only [List.mem_toFinset]

end ACUIhE.FILO.Components
