import ACUIHE

/-!
Executable examples for the complete ACUIhE search procedure.

The examples focus on the difficult part of the combined solver: opaque and
nested `E` bodies, equality classes, and cyclic dependencies. They deliberately
avoid gratuitous homomorphism depth, since exhaustive ACUIh language search is
exponential in that dimension.
-/

namespace ACUIHE.Examples

open ACUIHE.Solver
open ACUIHE.Solver.Search

inductive Constant where
  | a | b | c
  deriving DecidableEq, Repr

inductive Variable where
  | x
  deriving DecidableEq, Repr

inductive Hom where
  | h
  deriving DecidableEq, Repr

instance : FinEnum Constant :=
  FinEnum.ofList [.a, .b, .c] (by intro value; cases value <;> simp)

instance : FinEnum Variable :=
  FinEnum.ofList [.x] (by intro value; cases value; simp)

instance : FinEnum Hom :=
  FinEnum.ofList [.h] (by intro value; cases value; simp)

instance : Encodable Constant :=
  Encodable.ofEquiv (Fin (FinEnum.card Constant))
    (FinEnum.equiv : Constant ≃ Fin (FinEnum.card Constant))

instance : Encodable Variable :=
  Encodable.ofEquiv (Fin (FinEnum.card Variable))
    (FinEnum.equiv : Variable ≃ Fin (FinEnum.card Variable))

instance : Encodable Hom :=
  Encodable.ofEquiv (Fin (FinEnum.card Hom))
    (FinEnum.equiv : Hom ≃ Fin (FinEnum.card Hom))

abbrev Expression := Term Constant Variable Hom

def constant : Constant → Expression := .const

def var : Variable → Expression := .var

def e : Expression → Expression := .free

/-- ACUI sum of a list of expressions. -/
def sum : List Expression → Expression
  | [] => .zero
  | [single] => single
  | head :: second :: tail => .add head (sum (second :: tail))

/-- Raw-term counterpart of `ACUIHE.taggedArguments`. -/
def termTaggedArguments (homNames : Nat → Hom) :
    Nat → List Expression → Expression
  | _, [] => .zero
  | index, argument :: arguments =>
      .add (.hom (homNames index) argument)
        (termTaggedArguments homNames (index + 1) arguments)

/-- Syntactic form of the construction from `Definition.lean`:
`O_i(A₁, ..., Aₙ) = E(c_i + h₁(A₁) + ... + hₙ(Aₙ))`. -/
def termO {Index : Type} (constants : Index → Expression)
    (homNames : Nat → Hom) (index : Index)
    (arguments : List Expression) : Expression :=
  .free (.add (constants index)
    (termTaggedArguments homNames 1 arguments))

private theorem eval_termTaggedArguments
    {Alpha : Type} [ACUIhE Hom Alpha]
    (homNames : Nat → Hom) (start : Nat) (arguments : List Expression)
    (interpretConstant : Constant → Alpha)
    (interpretVariable : Variable → Alpha) :
    (termTaggedArguments homNames start arguments).eval
        interpretConstant interpretVariable =
      taggedArguments homNames start
        (arguments.map fun argument =>
          argument.eval interpretConstant interpretVariable) := by
  induction arguments generalizing start with
  | nil => rfl
  | cons argument arguments inductionHypothesis =>
      simp only [termTaggedArguments, Term.eval, List.map_cons,
        taggedArguments]
      rw [inductionHypothesis]

/-- Interpreting the syntactic constructor is exactly `ACUIHE.O`. -/
theorem eval_termO
    {Index Alpha : Type} [ACUIhE Hom Alpha]
    (constants : Index → Expression) (homNames : Nat → Hom)
    (index : Index) (arguments : List Expression)
    (interpretConstant : Constant → Alpha)
    (interpretVariable : Variable → Alpha) :
    (termO constants homNames index arguments).eval
        interpretConstant interpretVariable =
      O (fun selected =>
          (constants selected).eval interpretConstant interpretVariable)
        homNames index
        (arguments.map fun argument =>
          argument.eval interpretConstant interpretVariable) := by
  simp only [termO, O, Term.eval]
  rw [eval_termTaggedArguments]

structure ExampleProblem where
  title : String
  description : String
  left : Expression
  right : Expression
  expectedSatisfiable : Bool

/-- The ordinary atom forces `X` to contain `a`, while the alien atom can then
match `E(a)` only if the body `X + a` normalizes to `a`. Thus the solver has to
coordinate an outer ACUI inclusion with equality of two `E` bodies. -/
def propagationProblem : ExampleProblem :=
  { title := "Coupled E-body fixed point"
    description :=
      "Solving E(X + a) + a + b <= E(a + b) + X requires the outer inclusion and injective E-body equality to agree."
    left := sum
      [e (sum [var .x, constant .a]), constant .a, constant .b]
    right := sum
      [e (sum [constant .a, constant .b]), var .x]
    expectedSatisfiable := true }

/-- This ground lower bound contains two distinct nested `E` bodies, repeated
at the outer level so that purification must share their canonical keys. -/
def nestedProblem : ExampleProblem :=
  let inner := e (sum [constant .a, constant .b])
  let outer := e (sum [inner, constant .c])
  let nestedSeed := sum
    [outer, inner, constant .a, constant .b, constant .c]
  { title := "Shared nested-E reconstruction"
    description :=
      "The certificate must rank and reconstruct E(a + b) before E(E(a + b) + c), while reusing the inner body key."
    left := nestedSeed
    right := var .x
    expectedSatisfiable := true }

/-- A deliberately expensive instance of the `O_i` construction from
`Definition.lean`. Although there is only one alien body, its two arguments
produce nonempty homomorphism coefficients, which makes the underlying exact
finite-language search substantially larger than the root-only examples. -/
def complexProblem : ExampleProblem :=
  let homNames : Nat → Hom := fun _ => .h
  let operator := termO constant homNames .a
    [sum [constant .a, constant .b], sum [constant .b, constant .c]]
  let required := sum [operator, constant .a, constant .b, constant .c]
  { title := "O_a(a + b, b + c) reconstruction"
    description :=
      "The solver handles E(a + h(a + b) + h(b + c)) as an O_i atom. Nonempty hom coefficients make this deliberately slow."
    left := required
    right := var .x
    expectedSatisfiable := true }

/-- Any solution would have to be a finite term containing `a` and also the
strictly larger term `E(X + a)`. Repeating the requirement inside that `E`
creates an impossible finite dependency cycle. -/
def impossibleProblem : ExampleProblem :=
  { title := "Unsatisfiable cyclic E dependency"
    description :=
      "E(X + a) + b <= X would require a finite value of X to contain its own strictly larger E-image."
    left := sum [e (sum [var .x, constant .a]), constant .b]
    right := var .x
    expectedSatisfiable := false }

def constantName : Constant → String
  | .a => "a"
  | .b => "b"
  | .c => "c"

def variableName : Variable → String
  | .x => "X"

def homName : Hom → String
  | .h => "h"

def renderTerm {Var : Type}
    (renderVariable : Var → String) : Term Constant Var Hom → String
  | .zero => "0"
  | .const name => constantName name
  | .var name => renderVariable name
  | .add left right =>
      s!"({renderTerm renderVariable left} + {renderTerm renderVariable right})"
  | .hom name body =>
      s!"{homName name}({renderTerm renderVariable body})"
  | .free body => s!"E({renderTerm renderVariable body})"

def renderGroundNormalForm
    (value : NormalForm Constant (Fin 0) Hom) : String :=
  renderTerm (fun impossible => Fin.elim0 impossible) (reify value)

def solveExample (problem : ExampleProblem) : IO Unit := do
  IO.println s!"\n=== {problem.title} ==="
  IO.println problem.description
  IO.println s!"left  = {renderTerm variableName problem.left}"
  IO.println s!"right = {renderTerm variableName problem.right}"
  let left := normalize problem.left
  let right := normalize problem.right
  match solveACUIhE? left right with
  | none =>
      IO.println "result: UNSAT"
      IO.println s!"expected result matched: {!problem.expectedSatisfiable}"
  | some assignment =>
      IO.println "result: SAT"
      for name in ([.x] : List Variable) do
        IO.println s!"  {variableName name} := {renderGroundNormalForm (assignment name)}"
      let verified := checkGroundInequality
        (applyGroundAssignment assignment left)
        (applyGroundAssignment assignment right)
      IO.println s!"exact substitution check: {verified}"
      IO.println s!"expected result matched: {problem.expectedSatisfiable}"

def examples : List ExampleProblem :=
  [propagationProblem, nestedProblem, impossibleProblem, complexProblem]

end ACUIHE.Examples

def main (arguments : List String) : IO Unit := do
  IO.println "ACUIhE exhaustive solver examples"
  let selected :=
    match arguments with
    | ["propagation"] => [ACUIHE.Examples.propagationProblem]
    | ["nested"] => [ACUIHE.Examples.nestedProblem]
    | ["unsat"] => [ACUIHE.Examples.impossibleProblem]
    | ["complex"] => [ACUIHE.Examples.complexProblem]
    | _ => ACUIHE.Examples.examples
  for problem in selected do
    ACUIHE.Examples.solveExample problem
