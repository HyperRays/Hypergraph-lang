import ACUIHE.Solver.Search
import ACUIHE.Optimized

/-!
A deterministic grammar-aware fuzz worker for paired solver benchmarks.

Each invocation generates one inequality and runs exactly one solver.  The
Python driver starts the worker in a fresh process, which permits an external
per-case timeout without weakening either solver.
-/

namespace ACUIHE.Benchmarks.Fuzz

open ACUIHE.Solver

inductive Constant where
  | a | b
  deriving DecidableEq, Repr

inductive Variable where
  | x
  deriving DecidableEq, Repr

inductive Hom where
  | h
  deriving DecidableEq, Repr

instance : FinEnum Constant :=
  FinEnum.ofList [.a, .b] (by
    intro value
    cases value with
    | a => simp
    | b => simp)

instance : FinEnum Variable :=
  FinEnum.ofList [.x] (by
    intro value
    cases value with
    | x => simp)

instance : FinEnum Hom :=
  FinEnum.ofList [.h] (by
    intro value
    cases value with
    | h => simp)

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

/-- A small, platform-independent deterministic generator. -/
structure Generator where
  state : Nat

namespace Generator

def advance (state : Nat) : Nat :=
  (1664525 * state + 1013904223) % 4294967296

def choose (generator : Generator) (upper : Nat) : Nat × Generator :=
  let next := advance generator.state
  let value := if upper = 0 then 0 else next % upper
  (value, { state := next })

end Generator

/-- Generate a leaf.  Ground payloads disable the variable alternative. -/
def generateLeaf (allowVariable : Bool) (generator : Generator) :
    Expression × Generator :=
  let alternatives := if allowVariable then 4 else 3
  let (choice, next) := generator.choose alternatives
  let expression : Expression :=
    match choice with
    | 0 => .zero
    | 1 => .const .a
    | 2 => .const .b
    | _ => .var .x
  (expression, next)

/-- Generate from the full raw grammar with a maximum constructor depth.
At positive depth the distribution is 10% leaf, 45% addition, 20%
homomorphism, and 25% `E`; recursive children use the preceding depth. -/
def generateTerm : Nat → Bool → Generator → Expression × Generator
  | 0, allowVariable, generator => generateLeaf allowVariable generator
  | depth + 1, allowVariable, generator =>
      let (choice, afterChoice) := generator.choose 100
      if choice < 10 then
        generateLeaf allowVariable afterChoice
      else if choice < 55 then
        let (left, afterLeft) := generateTerm depth allowVariable afterChoice
        let (right, afterRight) := generateTerm depth allowVariable afterLeft
        (.add left right, afterRight)
      else if choice < 75 then
        let (body, afterBody) := generateTerm depth allowVariable afterChoice
        (.hom .h body, afterBody)
      else
        let (body, afterBody) := generateTerm depth allowVariable afterChoice
        (.free body, afterBody)

inductive Family where
  | random
  | satisfiableExtension
  | cyclic
  deriving DecidableEq

namespace Family

def parse? : String → Option Family
  | "random" => some .random
  | "sat" => some .satisfiableExtension
  | "cyclic" => some .cyclic
  | _ => none

end Family

structure Problem where
  left : Expression
  right : Expression

/-- Three distributions: unrestricted random pairs, guaranteed satisfiable
extensions `left ≤ left + slack`, and cyclic self-dependencies. -/
def generateProblem (family : Family) (depth seed : Nat) : Problem :=
  let initial : Generator := { state := seed + 1 }
  match family with
  | .random =>
      let (left, afterLeft) := generateTerm depth true initial
      let (right, _) := generateTerm depth true afterLeft
      { left, right }
  | .satisfiableExtension =>
      let (left, afterLeft) := generateTerm depth true initial
      let (slack, _) := generateTerm depth true afterLeft
      { left, right := .add left slack }
  | .cyclic =>
      let (payload, _) := generateTerm depth false initial
      let body := .add (.var .x) (.add (.const .a) payload)
      { left := .add (.free body) (.const .b), right := .var .x }

structure TermStatistics where
  nodes : Nat := 0
  additions : Nat := 0
  homomorphisms : Nat := 0
  eOperators : Nat := 0
  variableNodes : Nat := 0
  constantNodes : Nat := 0
  zeroNodes : Nat := 0
  depth : Nat := 0

def TermStatistics.combine (left right : TermStatistics) : TermStatistics :=
  { nodes := left.nodes + right.nodes
    additions := left.additions + right.additions
    homomorphisms := left.homomorphisms + right.homomorphisms
    eOperators := left.eOperators + right.eOperators
    variableNodes := left.variableNodes + right.variableNodes
    constantNodes := left.constantNodes + right.constantNodes
    zeroNodes := left.zeroNodes + right.zeroNodes
    depth := max left.depth right.depth }

def termStatistics : Expression → TermStatistics
  | .zero => { nodes := 1, zeroNodes := 1, depth := 1 }
  | .const _ => { nodes := 1, constantNodes := 1, depth := 1 }
  | .var _ => { nodes := 1, variableNodes := 1, depth := 1 }
  | .add left right =>
      let children := (termStatistics left).combine (termStatistics right)
      { children with
        nodes := children.nodes + 1
        additions := children.additions + 1
        depth := children.depth + 1 }
  | .hom _ body =>
      let child := termStatistics body
      { child with
        nodes := child.nodes + 1
        homomorphisms := child.homomorphisms + 1
        depth := child.depth + 1 }
  | .free body =>
      let child := termStatistics body
      { child with
        nodes := child.nodes + 1
        eOperators := child.eOperators + 1
        depth := child.depth + 1 }

def problemStatistics (problem : Problem) : TermStatistics :=
  (termStatistics problem.left).combine (termStatistics problem.right)

inductive SolverKind where
  | original
  | optimized
  | shortcut

namespace SolverKind

def parse? : String → Option SolverKind
  | "original" => some .original
  | "optimized" => some .optimized
  | "shortcut" => some .shortcut
  | _ => none

end SolverKind

def runSolver (solver : SolverKind) (problem : Problem)
    (shallowBound repetitions : Nat) : IO (Bool × Nat) := do
  let left := normalize problem.left
  let right := normalize problem.right
  let start ← IO.monoMsNow
  let mut satisfiable := false
  for _ in List.range repetitions do
    satisfiable :=
      match solver with
      | .original =>
          (ACUIHE.Solver.Search.solveACUIhE? left right).isSome
      | .optimized =>
          (ACUIHE.Optimized.Optimized.solveACUIhE?
            left right shallowBound).isSome
      | .shortcut =>
          (ACUIHE.Optimized.Shortcut.solveACUIhE?
            left right).isSome
  let elapsed ← IO.monoMsNow
  pure (satisfiable, elapsed - start)

def parseNatArgument (name value : String) : IO Nat :=
  match value.toNat? with
  | some number => pure number
  | none => throw <| IO.userError s!"invalid {name}: {value}"

def usage : String :=
  "usage: acuihe-fuzz (original|optimized|shortcut) (random|sat|cyclic) SEED DEPTH SHALLOW_BOUND REPETITIONS"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [solverText, familyText, seedText, depthText, shallowText,
      repetitionsText] =>
      let solver ← match SolverKind.parse? solverText with
        | some value => pure value
        | none => throw <| IO.userError s!"invalid solver: {solverText}"
      let family ← match Family.parse? familyText with
        | some value => pure value
        | none => throw <| IO.userError s!"invalid family: {familyText}"
      let seed ← parseNatArgument "seed" seedText
      let depth ← parseNatArgument "depth" depthText
      let shallowBound ← parseNatArgument "shallow bound" shallowText
      let repetitions ← parseNatArgument "repetitions" repetitionsText
      if repetitions = 0 then
        throw <| IO.userError "repetitions must be positive"
      let problem := generateProblem family depth seed
      let statistics := problemStatistics problem
      let (satisfiable, elapsed) ←
        runSolver solver problem shallowBound repetitions
      IO.println <|
        s!"outcome={if satisfiable then "sat" else "unsat"} " ++
        s!"elapsed_ms={elapsed} repetitions={repetitions} " ++
        s!"nodes={statistics.nodes} additions={statistics.additions} " ++
        s!"homs={statistics.homomorphisms} es={statistics.eOperators} " ++
        s!"variables={statistics.variableNodes} constants={statistics.constantNodes} " ++
        s!"zeros={statistics.zeroNodes} syntax_depth={statistics.depth}"
  | _ => throw <| IO.userError usage

end ACUIHE.Benchmarks.Fuzz

def main (arguments : List String) : IO Unit :=
  ACUIHE.Benchmarks.Fuzz.main arguments
