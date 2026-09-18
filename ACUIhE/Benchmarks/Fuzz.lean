import ACUIhE.Solver
import ACUIhE.Graph.Fold
import Lean.Data.Json

/-! Standalone measurement harness; not imported by the algebra or solver.
Input parsing and process startup are outside the timed region. The Python
supervisor supplies the wall-clock limit; it never changes a solver result.
-/

namespace Benchmarks

open ACUIhE Lean

abbrev T := Term Nat Nat Nat

structure Request where
  problem : Array (String × String)
  mode : String := "decision"
  variableCount : Nat := 2
  deriving FromJson

def parseTerm : Nat → List String → Except String (T × List String)
  | 0, _ => .error "term parser exhausted input budget"
  | _ + 1, [] => .error "missing term"
  | fuel + 1, token :: rest => do
      match token with
      | "0" => return (.zero, rest)
      | "+" =>
          let (a, rest) ← parseTerm fuel rest
          let (b, rest) ← parseTerm fuel rest
          return (.add a b, rest)
      | "e" =>
          let (a, rest) ← parseTerm fuel rest
          return (.free a, rest)
      | _ =>
          match token.splitOn ":" with
          | [tag, label] =>
              let some label := label.toNat? | throw "invalid natural label"
              match tag with
              | "c" => return (.const label, rest)
              | "v" => return (.var label, rest)
              | "h" =>
                  let (a, rest) ← parseTerm fuel rest
                  return (.hom label a, rest)
              | _ => throw "unknown constructor"
          | _ => throw "invalid token"

def parseWhole (s : String) : Except String T := do
  let tokens := s.splitOn " "
  let (t, rest) ← parseTerm tokens.length tokens
  if rest.isEmpty then return t else throw "trailing tokens"

def parseProblem (r : Request) : Except String (Solver.Problem Nat Nat Nat) :=
  r.problem.toList.mapM fun (a, b) => do
    return ⟨← parseWhole a, ← parseWhole b⟩

/-- Force the whole canonical graph through its public fold, including words.
This measures extraction plus traversal, not merely allocation of a closure. -/
def graphWeight : Graph.FoldAlgebra Nat Empty Nat Nat where
  atom word _ := word.length + 1
  edge word _ child := word.length + child + 1
  layer entries values := entries.attach.sum values

def run (r : Request) (p : Solver.Problem Nat Nat Nat) : IO Json := do
  let start ← IO.monoNanosNow
  let (answer, weight) ← if r.mode == "decision" then
    pure (Solver.isUnifiable p, 0)
  else if r.mode == "witness" then
    match Solver.solve p with
    | none => pure (false, 0)
    | some σ =>
        let mut total := 0
        for v in [:r.variableCount] do
          total := total + Graph.fold graphWeight (σ v)
        pure (true, total)
  else throw (IO.userError "mode must be decision or witness")
  let stop ← IO.monoNanosNow
  return Json.mkObj [("answer", toJson answer), ("elapsed_ns", toJson (stop - start)),
    ("graph_weight", toJson weight)]

end Benchmarks

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let line ← input.getLine
  let request ← IO.ofExcept (Lean.Json.parse line >>= Lean.fromJson? (α := Benchmarks.Request))
  let problem ← IO.ofExcept (Benchmarks.parseProblem request)
  output.putStrLn "ready"
  output.flush
  let go ← input.getLine
  unless go.trimAscii.toString == "go" do throw (IO.userError "expected go")
  let result ← Benchmarks.run request problem
  output.putStrLn result.compress
  output.flush
