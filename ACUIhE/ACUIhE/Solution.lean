import ACUIhE.Equation
import ACUIhE.Solution.Generic

/-!
# Groundness and solved equations

Equality, additive inequality, equation objects, and their certified decision
procedures are defined by `ACUIhE.Equation`. This module adds syntactic
groundness and solvedness: both sides must be variable-free and the asserted
relation must be valid. The existing two-term API is retained. Shared object,
solvedness, and Boolean correctness proofs are supplied by `Solution.Generic`;
only the syntactic groundness proofs and theory-specific bridges live here.
-/

namespace ACUIhE

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

namespace Term

/-- No variable occurs anywhere in the term. -/
@[simp] def IsGround : Term Const Var Hom → Prop
  | .zero => True
  | .const _ => True
  | .var _ => False
  | .add left right => left.IsGround ∧ right.IsGround
  | .hom _ body => body.IsGround
  | .free body => body.IsGround

instance decidableIsGround : (term : Term Const Var Hom) → Decidable term.IsGround
  | .zero | .const _ => isTrue True.intro
  | .var _ => isFalse id
  | .add left right => @instDecidableAnd _ _ (decidableIsGround left) (decidableIsGround right)
  | .hom _ body | .free body => decidableIsGround body

/-- Evaluating a ground term never depends on the variable interpretation. -/
theorem eval_eq_of_isGround {α : Type x} [ACUIhE Hom α]
    (interpretConst : Const → α) (first second : Var → α)
    {term : Term Const Var Hom} (ground : term.IsGround) :
    term.eval interpretConst first = term.eval interpretConst second := by
  induction term with
  | zero | const => rfl
  | var => exact False.elim ground
  | add left right ih₁ ih₂ =>
      simp only [eval]
      rw [ih₁ ground.1, ih₂ ground.2]
  | hom name body ih => exact congrArg (H name) (ih ground)
  | free body ih => exact congrArg E (ih ground)

end Term

/-- A solved equation has variable-free sides and is valid in the full ACUIhE theory. -/
abbrev Solved (left right : Term Const Var Hom) : Prop :=
  Generic.Solved Term.IsGround Term.Equal left right

@[simp] theorem solved_iff (left right : Term Const Var Hom) :
    Solved left right ↔
      left.IsGround ∧ right.IsGround ∧ left.Equal right :=
  Generic.solved_iff Term.IsGround Term.Equal left right

/-- Solvedness can be certified using the full theory's existing derivation system. -/
theorem solved_iff_derives (left right : Term Const Var Hom) :
    Solved left right ↔ left.IsGround ∧ right.IsGround ∧ Derives left right := by
  rw [solved_iff, soundness_and_completeness]

theorem Solved.of_derives {left right : Term Const Var Hom}
    (leftGround : left.IsGround) (rightGround : right.IsGround)
    (equality : Derives left right) : Solved left right :=
  ⟨leftGround, rightGround, equality.semanticallyEquivalent⟩

theorem Solved.derives {left right : Term Const Var Hom} (h : Solved left right) :
    Derives left right := completeness h.2.2

theorem Solved.symm {left right : Term Const Var Hom} (h : Solved left right) :
    Solved right left :=
  Generic.Solved.symm (Rel := Term.Equal) Term.Equal.symm h

/-- A solved equation actually holds in every ACUIhE algebra, in any carrier universe. -/
theorem Solved.sound {α : Type x} [ACUIhE Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (h : Solved left right) :
    left.eval interpretConst interpretVar = right.eval interpretConst interpretVar :=
  h.derives.sound interpretConst interpretVar

/-- The truth of a solved equation is independent of variable assignments. -/
theorem Solved.eval_iff {α : Type x} [ACUIhE Hom α]
    (interpretConst : Const → α) (first second : Var → α)
    {left right : Term Const Var Hom} (h : Solved left right) :
    left.eval interpretConst first = right.eval interpretConst first ↔
      left.eval interpretConst second = right.eval interpretConst second := by
  rw [Term.eval_eq_of_isGround interpretConst first second h.1,
    Term.eval_eq_of_isGround interpretConst first second h.2.1]

/-- A solved additive inequality has variable-free sides and a proof of `left ≤₊ right`. -/
abbrev SolvedBelow (left right : Term Const Var Hom) : Prop :=
  Generic.Solved Term.IsGround Term.Below left right

@[simp] theorem solvedBelow_iff (left right : Term Const Var Hom) :
    SolvedBelow left right ↔ left.IsGround ∧ right.IsGround ∧ left.Below right :=
  Generic.solved_iff Term.IsGround Term.Below left right

theorem solvedBelow_iff_derives (left right : Term Const Var Hom) :
    SolvedBelow left right ↔
      left.IsGround ∧ right.IsGround ∧ Derives (.add left right) right := by
  rw [solvedBelow_iff, Term.below_iff_derives]

theorem SolvedBelow.of_derives {left right : Term Const Var Hom}
    (leftGround : left.IsGround) (rightGround : right.IsGround)
    (inequality : Derives (.add left right) right) : SolvedBelow left right :=
  ⟨leftGround, rightGround, (Term.below_iff_derives left right).mpr inequality⟩

/-- Solving `left ≤₊ right` is exactly solving the equation `left + right = right`. -/
theorem solvedBelow_iff_solved_add (left right : Term Const Var Hom) :
    SolvedBelow left right ↔ Solved (.add left right) right :=
  Generic.solvedBelow_iff_solved_add Term.Equal (fun _ _ => Iff.rfl) left right

theorem SolvedBelow.sound {α : Type x} [ACUIhE Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (h : SolvedBelow left right) :
    left.eval interpretConst interpretVar ≤₊ right.eval interpretConst interpretVar :=
  Term.Below.sound interpretConst interpretVar h.2.2

/-- Full solvedness is exactly groundness together with canonical graph equality. -/
theorem solved_iff_normalize_eq (left right : Term Const Var Hom) :
    Solved left right ↔ left.IsGround ∧ right.IsGround ∧
      Graph.normalize left = Graph.normalize right := by
  rw [solved_iff_derives, ← Graph.normalize_eq_iff_derives]

theorem solvedBelow_iff_normalize_eq (left right : Term Const Var Hom) :
    SolvedBelow left right ↔ left.IsGround ∧ right.IsGround ∧
      Graph.normalize (.add left right) = Graph.normalize right := by
  rw [solvedBelow_iff_derives, ← Graph.normalize_eq_iff_derives]

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Decide the original solvedness proposition, including both groundness conditions. -/
instance decidableSolved (left right : Term Const Var Hom) : Decidable (Solved left right) :=
  inferInstanceAs (Decidable (left.IsGround ∧ right.IsGround ∧ left.Equal right))

instance decidableSolvedBelow (left right : Term Const Var Hom) : Decidable (SolvedBelow left right) :=
  inferInstanceAs (Decidable (left.IsGround ∧ right.IsGround ∧ left.Below right))

/-- Executable Boolean view of certified equation solvedness. -/
def isSolved (left right : Term Const Var Hom) : Bool :=
  Generic.isSolved Term.IsGround Term.Equal left right

/-- Executable Boolean view of certified additive-inequality solvedness. -/
def isSolvedBelow (left right : Term Const Var Hom) : Bool :=
  Generic.isSolved Term.IsGround Term.Below left right

@[simp] theorem isSolved_eq_true (left right : Term Const Var Hom) :
    isSolved left right = true ↔ Solved left right :=
  Generic.isSolved_eq_true Term.IsGround Term.Equal left right

@[simp] theorem isSolved_eq_false (left right : Term Const Var Hom) :
    isSolved left right = false ↔ ¬ Solved left right :=
  Generic.isSolved_eq_false Term.IsGround Term.Equal left right

@[simp] theorem isSolvedBelow_eq_true (left right : Term Const Var Hom) :
    isSolvedBelow left right = true ↔ SolvedBelow left right :=
  Generic.isSolved_eq_true Term.IsGround Term.Below left right

@[simp] theorem isSolvedBelow_eq_false (left right : Term Const Var Hom) :
    isSolvedBelow left right = false ↔ ¬ SolvedBelow left right :=
  Generic.isSolved_eq_false Term.IsGround Term.Below left right

end DecidableLabels

namespace ACUIh

namespace Term

/-- Groundness for the restricted ACUIh syntax. -/
@[simp] def IsGround : Term Const Var Hom → Prop
  | .zero => True
  | .const _ => True
  | .var _ => False
  | .add left right => left.IsGround ∧ right.IsGround
  | .hom _ body => body.IsGround

instance decidableIsGround : (term : Term Const Var Hom) → Decidable term.IsGround
  | .zero | .const _ => isTrue True.intro
  | .var _ => isFalse id
  | .add left right => @instDecidableAnd _ _ (decidableIsGround left) (decidableIsGround right)
  | .hom _ body => decidableIsGround body

/-- The lossless syntactic inclusion preserves and reflects groundness. -/
@[simp] theorem isGround_toACUIhE (term : Term Const Var Hom) :
    term.toACUIhE.IsGround ↔ term.IsGround := by
  induction term <;> simp_all [toACUIhE]

theorem eval_eq_of_isGround {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (first second : Var → α)
    {term : Term Const Var Hom} (ground : term.IsGround) :
    term.eval interpretConst first = term.eval interpretConst second := by
  induction term with
  | zero | const => rfl
  | var => exact False.elim ground
  | add left right ih₁ ih₂ =>
      simp only [eval]
      rw [ih₁ ground.1, ih₂ ground.2]
  | hom name body ih => exact congrArg (H name) (ih ground)

end Term

/-- A solved ACUIh equation has ground sides and an equality proof in ACUIh alone. -/
abbrev Solved (left right : Term Const Var Hom) : Prop :=
  Generic.Solved Term.IsGround Term.Equal left right

@[simp] theorem solved_iff (left right : Term Const Var Hom) :
    Solved left right ↔
      left.IsGround ∧ right.IsGround ∧ left.Equal right :=
  Generic.solved_iff Term.IsGround Term.Equal left right

theorem solved_iff_derives (left right : Term Const Var Hom) :
    Solved left right ↔ left.IsGround ∧ right.IsGround ∧ Derives left right := by
  rw [solved_iff, soundness_and_completeness]

theorem Solved.of_derives {left right : Term Const Var Hom}
    (leftGround : left.IsGround) (rightGround : right.IsGround)
    (equality : Derives left right) : Solved left right :=
  ⟨leftGround, rightGround, equality.semanticallyEquivalent⟩

theorem Solved.derives {left right : Term Const Var Hom} (h : Solved left right) :
    Derives left right := completeness h.2.2

theorem Solved.symm {left right : Term Const Var Hom} (h : Solved left right) :
    Solved right left :=
  Generic.Solved.symm (Rel := Term.Equal) Term.Equal.symm h

theorem Solved.sound {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (h : Solved left right) :
    left.eval interpretConst interpretVar = right.eval interpretConst interpretVar :=
  h.derives.sound interpretConst interpretVar

theorem Solved.eval_iff {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (first second : Var → α)
    {left right : Term Const Var Hom} (h : Solved left right) :
    left.eval interpretConst first = right.eval interpretConst first ↔
      left.eval interpretConst second = right.eval interpretConst second := by
  rw [Term.eval_eq_of_isGround interpretConst first second h.1,
    Term.eval_eq_of_isGround interpretConst first second h.2.1]

/-- A solved ACUIh inequality has ground sides and is valid in ACUIh alone. -/
abbrev SolvedBelow (left right : Term Const Var Hom) : Prop :=
  Generic.Solved Term.IsGround Term.Below left right

@[simp] theorem solvedBelow_iff (left right : Term Const Var Hom) :
    SolvedBelow left right ↔ left.IsGround ∧ right.IsGround ∧ left.Below right :=
  Generic.solved_iff Term.IsGround Term.Below left right

theorem solvedBelow_iff_derives (left right : Term Const Var Hom) :
    SolvedBelow left right ↔
      left.IsGround ∧ right.IsGround ∧ Derives (.add left right) right := by
  rw [solvedBelow_iff, Term.below_iff_derives]

theorem SolvedBelow.of_derives {left right : Term Const Var Hom}
    (leftGround : left.IsGround) (rightGround : right.IsGround)
    (inequality : Derives (.add left right) right) : SolvedBelow left right :=
  ⟨leftGround, rightGround, (Term.below_iff_derives left right).mpr inequality⟩

theorem solvedBelow_iff_solved_add (left right : Term Const Var Hom) :
    SolvedBelow left right ↔ Solved (.add left right) right :=
  Generic.solvedBelow_iff_solved_add Term.Equal (fun _ _ => Iff.rfl) left right

theorem SolvedBelow.sound {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var Hom} (h : SolvedBelow left right) :
    left.eval interpretConst interpretVar ≤₊ right.eval interpretConst interpretVar :=
  Term.Below.sound interpretConst interpretVar h.2.2

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

theorem solved_iff_normalize_eq (left right : Term Const Var Hom) :
    Solved left right ↔ left.IsGround ∧ right.IsGround ∧ left.normalize = right.normalize := by
  rw [solved_iff_derives, ← NF.normalize_eq_iff_derives]

theorem solvedBelow_iff_normalize_eq (left right : Term Const Var Hom) :
    SolvedBelow left right ↔ left.IsGround ∧ right.IsGround ∧
      (Term.add left right).normalize = right.normalize := by
  rw [solvedBelow_iff_derives, ← NF.normalize_eq_iff_derives]

instance decidableSolved (left right : Term Const Var Hom) : Decidable (Solved left right) :=
  inferInstanceAs (Decidable (left.IsGround ∧ right.IsGround ∧ left.Equal right))

instance decidableSolvedBelow (left right : Term Const Var Hom) : Decidable (SolvedBelow left right) :=
  inferInstanceAs (Decidable (left.IsGround ∧ right.IsGround ∧ left.Below right))

def isSolved (left right : Term Const Var Hom) : Bool :=
  Generic.isSolved Term.IsGround Term.Equal left right

def isSolvedBelow (left right : Term Const Var Hom) : Bool :=
  Generic.isSolved Term.IsGround Term.Below left right

@[simp] theorem isSolved_eq_true (left right : Term Const Var Hom) :
    isSolved left right = true ↔ Solved left right :=
  Generic.isSolved_eq_true Term.IsGround Term.Equal left right

@[simp] theorem isSolved_eq_false (left right : Term Const Var Hom) :
    isSolved left right = false ↔ ¬ Solved left right :=
  Generic.isSolved_eq_false Term.IsGround Term.Equal left right

@[simp] theorem isSolvedBelow_eq_true (left right : Term Const Var Hom) :
    isSolvedBelow left right = true ↔ SolvedBelow left right :=
  Generic.isSolved_eq_true Term.IsGround Term.Below left right

@[simp] theorem isSolvedBelow_eq_false (left right : Term Const Var Hom) :
    isSolvedBelow left right = false ↔ ¬ SolvedBelow left right :=
  Generic.isSolved_eq_false Term.IsGround Term.Below left right

end DecidableLabels

end ACUIh

namespace ACUIE

namespace Term

/-- Groundness for the restricted ACUIE syntax, including beneath `E`. -/
@[simp] def IsGround : Term Const Var → Prop
  | .zero => True
  | .const _ => True
  | .var _ => False
  | .add left right => left.IsGround ∧ right.IsGround
  | .free body => body.IsGround

instance decidableIsGround : (term : Term Const Var) → Decidable term.IsGround
  | .zero | .const _ => isTrue True.intro
  | .var _ => isFalse id
  | .add left right => @instDecidableAnd _ _ (decidableIsGround left) (decidableIsGround right)
  | .free body => decidableIsGround body

@[simp] theorem isGround_toACUIhE (term : Term Const Var) :
    (term.toACUIhE (Hom := Hom)).IsGround ↔ term.IsGround := by
  induction term <;> simp_all [toACUIhE]

theorem eval_eq_of_isGround {α : Type x} [ACUIE α]
    (interpretConst : Const → α) (first second : Var → α)
    {term : Term Const Var} (ground : term.IsGround) :
    term.eval interpretConst first = term.eval interpretConst second := by
  induction term with
  | zero | const => rfl
  | var => exact False.elim ground
  | add left right ih₁ ih₂ =>
      simp only [eval]
      rw [ih₁ ground.1, ih₂ ground.2]
  | free body ih => exact congrArg E (ih ground)

end Term

/-- A solved ACUIE equation has ground sides and an equality proof in ACUIE alone. -/
abbrev Solved (left right : Term Const Var) : Prop :=
  Generic.Solved Term.IsGround Term.Equal left right

@[simp] theorem solved_iff (left right : Term Const Var) :
    Solved left right ↔
      left.IsGround ∧ right.IsGround ∧ left.Equal right :=
  Generic.solved_iff Term.IsGround Term.Equal left right

theorem Solved.symm {left right : Term Const Var} (h : Solved left right) :
    Solved right left :=
  Generic.Solved.symm (Rel := Term.Equal) Term.Equal.symm h

/-- A solved equation holds under each interpretation in the defining universe. -/
theorem Solved.sound {α : Type (max u v)} [ACUIE α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var} (h : Solved left right) :
    left.eval interpretConst interpretVar = right.eval interpretConst interpretVar :=
  h.2.2 interpretConst interpretVar

theorem Solved.eval_iff {α : Type x} [ACUIE α]
    (interpretConst : Const → α) (first second : Var → α)
    {left right : Term Const Var} (h : Solved left right) :
    left.eval interpretConst first = right.eval interpretConst first ↔
      left.eval interpretConst second = right.eval interpretConst second := by
  rw [Term.eval_eq_of_isGround interpretConst first second h.1,
    Term.eval_eq_of_isGround interpretConst first second h.2.1]

/-- A solved ACUIE inequality has ground sides and is valid in ACUIE alone. -/
abbrev SolvedBelow (left right : Term Const Var) : Prop :=
  Generic.Solved Term.IsGround Term.Below left right

@[simp] theorem solvedBelow_iff (left right : Term Const Var) :
    SolvedBelow left right ↔ left.IsGround ∧ right.IsGround ∧ left.Below right :=
  Generic.solved_iff Term.IsGround Term.Below left right

theorem solvedBelow_iff_solved_add (left right : Term Const Var) :
    SolvedBelow left right ↔ Solved (.add left right) right :=
  Generic.solvedBelow_iff_solved_add Term.Equal (fun _ _ => Iff.rfl) left right

theorem SolvedBelow.sound {α : Type (max u v)} [ACUIE α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    {left right : Term Const Var} (h : SolvedBelow left right) :
    left.eval interpretConst interpretVar ≤₊ right.eval interpretConst interpretVar :=
  h.2.2 interpretConst interpretVar

theorem solved_iff_normalize_eq (left right : Term Const Var) :
    Solved left right ↔ left.IsGround ∧ right.IsGround ∧
      Graph.normalize (left.toACUIhE (Hom := Empty)) = Graph.normalize right.toACUIhE := by
  rw [solved_iff, Term.equal_iff_normalize_eq]

theorem solvedBelow_iff_normalize_eq (left right : Term Const Var) :
    SolvedBelow left right ↔ left.IsGround ∧ right.IsGround ∧
      Graph.normalize ((Term.add left right).toACUIhE (Hom := Empty)) =
        Graph.normalize right.toACUIhE := by
  rw [solvedBelow_iff, Term.below_iff_semanticallyEquivalent, semanticallyEquivalent_iff_normalize_eq]

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var]

instance decidableSolved (left right : Term Const Var) : Decidable (Solved left right) :=
  inferInstanceAs (Decidable (left.IsGround ∧ right.IsGround ∧ left.Equal right))

instance decidableSolvedBelow (left right : Term Const Var) : Decidable (SolvedBelow left right) :=
  inferInstanceAs (Decidable (left.IsGround ∧ right.IsGround ∧ left.Below right))

def isSolved (left right : Term Const Var) : Bool :=
  Generic.isSolved Term.IsGround Term.Equal left right

def isSolvedBelow (left right : Term Const Var) : Bool :=
  Generic.isSolved Term.IsGround Term.Below left right

@[simp] theorem isSolved_eq_true (left right : Term Const Var) :
    isSolved left right = true ↔ Solved left right :=
  Generic.isSolved_eq_true Term.IsGround Term.Equal left right

@[simp] theorem isSolved_eq_false (left right : Term Const Var) :
    isSolved left right = false ↔ ¬ Solved left right :=
  Generic.isSolved_eq_false Term.IsGround Term.Equal left right

@[simp] theorem isSolvedBelow_eq_true (left right : Term Const Var) :
    isSolvedBelow left right = true ↔ SolvedBelow left right :=
  Generic.isSolved_eq_true Term.IsGround Term.Below left right

@[simp] theorem isSolvedBelow_eq_false (left right : Term Const Var) :
    isSolvedBelow left right = false ↔ ¬ SolvedBelow left right :=
  Generic.isSolved_eq_false Term.IsGround Term.Below left right

end DecidableLabels

end ACUIE

end ACUIhE

namespace ACUIhE

universe u v w

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- An equation object is solved exactly when its sides are ground and it is valid. -/
abbrev Equation.Solved (equation : Equation Const Var Hom) : Prop :=
  Generic.Equation.Solved Term.IsGround Term.Equal equation

/-- An inequality object is solved exactly when its sides are ground and it is valid. -/
abbrev Inequality.Solved (inequality : Inequality Const Var Hom) : Prop :=
  Generic.Inequality.Solved Term.IsGround Term.add Term.Equal inequality

@[simp] theorem Equation.solved_iff (equation : Equation Const Var Hom) :
    equation.Solved ↔ equation.left.IsGround ∧ equation.right.IsGround ∧ equation.Valid :=
  Generic.Equation.solved_iff Term.IsGround Term.Equal equation

@[simp] theorem Inequality.solved_iff (inequality : Inequality Const Var Hom) :
    inequality.Solved ↔ inequality.left.IsGround ∧ inequality.right.IsGround ∧ inequality.Valid :=
  Generic.Inequality.solved_iff Term.IsGround Term.add Term.Equal inequality

theorem Equation.Solved.valid {equation : Equation Const Var Hom} (h : equation.Solved) :
    equation.Valid :=
  Generic.Equation.Solved.valid (Ground := Term.IsGround) (Equal := Term.Equal) h

theorem Inequality.Solved.valid {inequality : Inequality Const Var Hom} (h : inequality.Solved) :
    inequality.Valid :=
  Generic.Inequality.Solved.valid (Ground := Term.IsGround) (add := Term.add)
    (Equal := Term.Equal) h

@[simp] theorem Equation.solved_swap (equation : Equation Const Var Hom) :
    equation.swap.Solved ↔ equation.Solved :=
  Generic.Equation.solved_swap Term.IsGround Term.Equal.symm equation

/-- Replacing an inequality by its associated equation also preserves solvedness. -/
@[simp] theorem Inequality.solved_toEquation (inequality : Inequality Const Var Hom) :
    inequality.toEquation.Solved ↔ inequality.Solved :=
  Generic.Inequality.solved_toEquation Term.Equal (fun _ _ => Iff.rfl) inequality

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

instance Equation.decidableSolved (equation : Equation Const Var Hom) : Decidable equation.Solved :=
  inferInstanceAs (Decidable (_root_.ACUIhE.Solved equation.left equation.right))

instance Inequality.decidableSolved (inequality : Inequality Const Var Hom) : Decidable inequality.Solved :=
  inferInstanceAs (Decidable (_root_.ACUIhE.SolvedBelow inequality.left inequality.right))

def Equation.isSolved (equation : Equation Const Var Hom) : Bool :=
  _root_.ACUIhE.isSolved equation.left equation.right

def Inequality.isSolved (inequality : Inequality Const Var Hom) : Bool :=
  _root_.ACUIhE.isSolvedBelow inequality.left inequality.right

@[simp] theorem Equation.isSolved_eq_true (equation : Equation Const Var Hom) :
    equation.isSolved = true ↔ equation.Solved :=
  _root_.ACUIhE.isSolved_eq_true equation.left equation.right

@[simp] theorem Equation.isSolved_eq_false (equation : Equation Const Var Hom) :
    equation.isSolved = false ↔ ¬ equation.Solved :=
  _root_.ACUIhE.isSolved_eq_false equation.left equation.right

@[simp] theorem Inequality.isSolved_eq_true (inequality : Inequality Const Var Hom) :
    inequality.isSolved = true ↔ inequality.Solved :=
  _root_.ACUIhE.isSolvedBelow_eq_true inequality.left inequality.right

@[simp] theorem Inequality.isSolved_eq_false (inequality : Inequality Const Var Hom) :
    inequality.isSolved = false ↔ ¬ inequality.Solved :=
  _root_.ACUIhE.isSolvedBelow_eq_false inequality.left inequality.right

end DecidableLabels

end ACUIhE

namespace ACUIhE.ACUIh

universe u v w

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- An equation object is solved exactly when its sides are ground and it is valid. -/
abbrev Equation.Solved (equation : Equation Const Var Hom) : Prop :=
  Generic.Equation.Solved Term.IsGround Term.Equal equation

/-- An inequality object is solved exactly when its sides are ground and it is valid. -/
abbrev Inequality.Solved (inequality : Inequality Const Var Hom) : Prop :=
  Generic.Inequality.Solved Term.IsGround Term.add Term.Equal inequality

@[simp] theorem Equation.solved_iff (equation : Equation Const Var Hom) :
    equation.Solved ↔ equation.left.IsGround ∧ equation.right.IsGround ∧ equation.Valid :=
  Generic.Equation.solved_iff Term.IsGround Term.Equal equation

@[simp] theorem Inequality.solved_iff (inequality : Inequality Const Var Hom) :
    inequality.Solved ↔ inequality.left.IsGround ∧ inequality.right.IsGround ∧ inequality.Valid :=
  Generic.Inequality.solved_iff Term.IsGround Term.add Term.Equal inequality

theorem Equation.Solved.valid {equation : Equation Const Var Hom} (h : equation.Solved) :
    equation.Valid :=
  Generic.Equation.Solved.valid (Ground := Term.IsGround) (Equal := Term.Equal) h

theorem Inequality.Solved.valid {inequality : Inequality Const Var Hom} (h : inequality.Solved) :
    inequality.Valid :=
  Generic.Inequality.Solved.valid (Ground := Term.IsGround) (add := Term.add)
    (Equal := Term.Equal) h

@[simp] theorem Equation.solved_swap (equation : Equation Const Var Hom) :
    equation.swap.Solved ↔ equation.Solved :=
  Generic.Equation.solved_swap Term.IsGround Term.Equal.symm equation

/-- Replacing an inequality by its associated equation also preserves solvedness. -/
@[simp] theorem Inequality.solved_toEquation (inequality : Inequality Const Var Hom) :
    inequality.toEquation.Solved ↔ inequality.Solved :=
  Generic.Inequality.solved_toEquation Term.Equal (fun _ _ => Iff.rfl) inequality

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

instance Equation.decidableSolved (equation : Equation Const Var Hom) : Decidable equation.Solved :=
  inferInstanceAs (Decidable (_root_.ACUIhE.ACUIh.Solved equation.left equation.right))

instance Inequality.decidableSolved (inequality : Inequality Const Var Hom) : Decidable inequality.Solved :=
  inferInstanceAs (Decidable (_root_.ACUIhE.ACUIh.SolvedBelow inequality.left inequality.right))

def Equation.isSolved (equation : Equation Const Var Hom) : Bool :=
  _root_.ACUIhE.ACUIh.isSolved equation.left equation.right

def Inequality.isSolved (inequality : Inequality Const Var Hom) : Bool :=
  _root_.ACUIhE.ACUIh.isSolvedBelow inequality.left inequality.right

@[simp] theorem Equation.isSolved_eq_true (equation : Equation Const Var Hom) :
    equation.isSolved = true ↔ equation.Solved :=
  _root_.ACUIhE.ACUIh.isSolved_eq_true equation.left equation.right

@[simp] theorem Equation.isSolved_eq_false (equation : Equation Const Var Hom) :
    equation.isSolved = false ↔ ¬ equation.Solved :=
  _root_.ACUIhE.ACUIh.isSolved_eq_false equation.left equation.right

@[simp] theorem Inequality.isSolved_eq_true (inequality : Inequality Const Var Hom) :
    inequality.isSolved = true ↔ inequality.Solved :=
  _root_.ACUIhE.ACUIh.isSolvedBelow_eq_true inequality.left inequality.right

@[simp] theorem Inequality.isSolved_eq_false (inequality : Inequality Const Var Hom) :
    inequality.isSolved = false ↔ ¬ inequality.Solved :=
  _root_.ACUIhE.ACUIh.isSolvedBelow_eq_false inequality.left inequality.right

end DecidableLabels

end ACUIhE.ACUIh

namespace ACUIhE.ACUIE

universe u v w

variable {Const : Type u} {Var : Type v}

/-- An equation object is solved exactly when its sides are ground and it is valid. -/
abbrev Equation.Solved (equation : Equation Const Var) : Prop :=
  Generic.Equation.Solved Term.IsGround Term.Equal equation

/-- An inequality object is solved exactly when its sides are ground and it is valid. -/
abbrev Inequality.Solved (inequality : Inequality Const Var) : Prop :=
  Generic.Inequality.Solved Term.IsGround Term.add Term.Equal inequality

@[simp] theorem Equation.solved_iff (equation : Equation Const Var) :
    equation.Solved ↔ equation.left.IsGround ∧ equation.right.IsGround ∧ equation.Valid :=
  Generic.Equation.solved_iff Term.IsGround Term.Equal equation

@[simp] theorem Inequality.solved_iff (inequality : Inequality Const Var) :
    inequality.Solved ↔ inequality.left.IsGround ∧ inequality.right.IsGround ∧ inequality.Valid :=
  Generic.Inequality.solved_iff Term.IsGround Term.add Term.Equal inequality

theorem Equation.Solved.valid {equation : Equation Const Var} (h : equation.Solved) :
    equation.Valid :=
  Generic.Equation.Solved.valid (Ground := Term.IsGround) (Equal := Term.Equal) h

theorem Inequality.Solved.valid {inequality : Inequality Const Var} (h : inequality.Solved) :
    inequality.Valid :=
  Generic.Inequality.Solved.valid (Ground := Term.IsGround) (add := Term.add)
    (Equal := Term.Equal) h

@[simp] theorem Equation.solved_swap (equation : Equation Const Var) :
    equation.swap.Solved ↔ equation.Solved :=
  Generic.Equation.solved_swap Term.IsGround Term.Equal.symm equation

/-- Replacing an inequality by its associated equation also preserves solvedness. -/
@[simp] theorem Inequality.solved_toEquation (inequality : Inequality Const Var) :
    inequality.toEquation.Solved ↔ inequality.Solved :=
  Generic.Inequality.solved_toEquation Term.Equal (fun _ _ => Iff.rfl) inequality

section DecidableLabels

variable [DecidableEq Const] [DecidableEq Var]

instance Equation.decidableSolved (equation : Equation Const Var) : Decidable equation.Solved :=
  inferInstanceAs (Decidable (_root_.ACUIhE.ACUIE.Solved equation.left equation.right))

instance Inequality.decidableSolved (inequality : Inequality Const Var) : Decidable inequality.Solved :=
  inferInstanceAs (Decidable (_root_.ACUIhE.ACUIE.SolvedBelow inequality.left inequality.right))

def Equation.isSolved (equation : Equation Const Var) : Bool :=
  _root_.ACUIhE.ACUIE.isSolved equation.left equation.right

def Inequality.isSolved (inequality : Inequality Const Var) : Bool :=
  _root_.ACUIhE.ACUIE.isSolvedBelow inequality.left inequality.right

@[simp] theorem Equation.isSolved_eq_true (equation : Equation Const Var) :
    equation.isSolved = true ↔ equation.Solved :=
  _root_.ACUIhE.ACUIE.isSolved_eq_true equation.left equation.right

@[simp] theorem Equation.isSolved_eq_false (equation : Equation Const Var) :
    equation.isSolved = false ↔ ¬ equation.Solved :=
  _root_.ACUIhE.ACUIE.isSolved_eq_false equation.left equation.right

@[simp] theorem Inequality.isSolved_eq_true (inequality : Inequality Const Var) :
    inequality.isSolved = true ↔ inequality.Solved :=
  _root_.ACUIhE.ACUIE.isSolvedBelow_eq_true inequality.left inequality.right

@[simp] theorem Inequality.isSolved_eq_false (inequality : Inequality Const Var) :
    inequality.isSolved = false ↔ ¬ inequality.Solved :=
  _root_.ACUIhE.ACUIE.isSolvedBelow_eq_false inequality.left inequality.right

end DecidableLabels

end ACUIhE.ACUIE
