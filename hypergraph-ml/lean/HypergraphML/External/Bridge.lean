import HypergraphML.External.TypeSystem
import Lean.Data.Json

/-!
# Native bridge

The C ABI is deliberately one total string-to-string function.  JSON is an
internal protocol: malformed input becomes a structured error response rather
than an exception crossing the language boundary.
-/

namespace HypergraphML.External.Bridge

open Lean
open ACUIHE
open ACUIHE.Solver
open ACUIHE.External

private def getString (json : Json) (field : String) : Except String String := do
  (← json.getObjVal? field).getStr?

private def getNat (json : Json) (field : String) : Except String Nat := do
  (← json.getObjVal? field).getNat?

private def getArray (json : Json) (field : String) : Except String (Array Json) := do
  match ← json.getObjVal? field with
  | .arr values => pure values
  | _ => throw s!"field '{field}' must be an array"

private def checkedFin (kind : String) (bound value : Nat) : Except String (Fin bound) :=
  if valid : value < bound then
    pure ⟨value, valid⟩
  else
    throw s!"{kind} index {value} is outside 0..{bound}"

private partial def decodeTerm (constantCount variableCount homCount : Nat) :
    Json → Except String (Term (Fin constantCount) (Fin variableCount) (Fin homCount))
  | json => do
      let tag ← getString json "tag"
      match tag with
      | "zero" => pure .zero
      | "const" =>
          pure <| .const (← checkedFin "constant" constantCount (← getNat json "id"))
      | "var" =>
          pure <| .var (← checkedFin "variable" variableCount (← getNat json "id"))
      | "add" =>
          pure <| .add
            (← decodeTerm constantCount variableCount homCount
              (← json.getObjVal? "left"))
            (← decodeTerm constantCount variableCount homCount
              (← json.getObjVal? "right"))
      | "hom" =>
          pure <| .hom
            (← checkedFin "homomorphism" homCount (← getNat json "id"))
            (← decodeTerm constantCount variableCount homCount
              (← json.getObjVal? "body"))
      | "free" =>
          pure <| .free
            (← decodeTerm constantCount variableCount homCount
              (← json.getObjVal? "body"))
      | unknown => throw s!"unknown term tag '{unknown}'"

private def decodeRules (constantCount homCount : Nat) (items : Array Json) :
    Except String (List (BlockReplacement (Fin constantCount) (Fin homCount))) := do
  let mut rules := []
  for item in items do
    match ← getString item "kind" with
    | "replace" =>
        let pattern ← decodeTerm constantCount 0 homCount (← item.getObjVal? "pattern")
        let replacement ← decodeTerm constantCount 0 homCount
          (← item.getObjVal? "replacement")
        rules := rules ++ [BlockReplacement.ofTerms pattern replacement]
    | "subsumption" =>
        let lower ← normalize <$> decodeTerm constantCount 0 homCount
          (← item.getObjVal? "lower")
        let upper ← normalize <$> decodeTerm constantCount 0 homCount
          (← item.getObjVal? "upper")
        rules := rules ++ [BlockReplacement.ofSubsumption lower upper]
    | kind => throw s!"unknown replacement rule kind '{kind}'"
  pure rules

private def decodeConstraints (constantCount variableCount homCount : Nat)
    (items : Array Json) : Except String
      (Array (TypeInequality (Fin constantCount) (Fin variableCount) (Fin homCount))) := do
  let mut rows := #[]
  for item in items do
    let kind ← getString item "kind"
    let left ← normalize <$> decodeTerm constantCount variableCount homCount
      (← item.getObjVal? "left")
    let right ← normalize <$> decodeTerm constantCount variableCount homCount
      (← item.getObjVal? "right")
    match kind with
    | "below" => rows := rows.push { left, right }
    | "equal" =>
        rows := rows.push { left, right }
        rows := rows.push { left := right, right := left }
    | unknown => throw s!"unknown constraint kind '{unknown}'"
  pure rows

private def encodeTerm {constantCount variableCount homCount : Nat} :
    Term (Fin constantCount) (Fin variableCount) (Fin homCount) → Json
  | .zero => Json.mkObj [("tag", "zero")]
  | .const name => Json.mkObj [("tag", "const"), ("id", name.val)]
  | .var name => Json.mkObj [("tag", "var"), ("id", name.val)]
  | .add left right => Json.mkObj
      [("tag", "add"), ("left", encodeTerm left), ("right", encodeTerm right)]
  | .hom name body => Json.mkObj
      [("tag", "hom"), ("id", name.val), ("body", encodeTerm body)]
  | .free body => Json.mkObj [("tag", "free"), ("body", encodeTerm body)]

private def success (fields : List (String × Json)) : String :=
  (Json.mkObj (("version", 1) :: fields)).compress

private def failure (message : String) : String :=
  success [("status", "error"), ("message", message)]

private def solve (request : Json) : Except String String := do
  let constantCount ← getNat request "constants"
  let variableCount ← getNat request "variables"
  let homCount ← getNat request "homomorphisms"
  let rules ← decodeRules constantCount homCount (← getArray request "rules")
  let rows ← decodeConstraints constantCount variableCount homCount
    (← getArray request "constraints")
  let system := fun row : Fin rows.size => rows[row]
  match solveInequalitySystem? rules system with
  | none => pure <| success [("status", "unsat")]
  | some assignment =>
      let values : Array Json := Array.ofFn fun index : Fin variableCount =>
        encodeTerm (reify (assignment index))
      pure <| success [("status", "sat"), ("assignment", .arr values)]

private def dispatch (request : Json) : Except String String := do
  let version ← getNat request "version"
  if version != 1 then
    throw s!"unsupported protocol version {version}"
  match ← getString request "operation" with
  | "solve" => solve request
  | operation => throw s!"unknown operation '{operation}'"

/-- Total internal bridge used by the OCaml C stub. -/
@[export hypergraphml_bridge]
def bridge (input : String) : String :=
  match Json.parse input >>= dispatch with
  | .ok response => response
  | .error message => failure message

end HypergraphML.External.Bridge
