open Hypergraph

let run source =
  match Program.run source with
  | Ok result -> result.Program.values
  | Error (Program.Parse_error error) ->
      failwith (Printf.sprintf "parse %d:%d: %s" error.line error.column error.message)
  | Error (Program.Type_errors diagnostics) ->
      failwith
        (String.concat "; "
           (List.map (fun (d : Check.diagnostic) -> d.message) diagnostics))
  | Error (Program.Evaluation_error error) -> failwith error.Value.message

let value environment name = Option.get (Value.find environment name)

let expect name expected actual =
  if not (String.equal expected actual) then
    failwith (Printf.sprintf "%s: expected %s, got %s" name expected actual)

let () =
  let environment =
    run
      {|
let a: Edge<Int,Int,EmptySet> = {1} -> {2}
let b: UndirectedEdge<Int,Int,EmptySet> = {2} <-> {3}
let g: Set<Edge<Int,Int,EmptySet>> = {a, b}
let decimals = {1.1, 1.10, 1000000000000000000000000000000.00000000000000000001}
let left: mut Set<Int> = {1, 2, 3}
left &= {2, 3, 4}
left -= {3}
let edge_left: mut Edge<Int,Int,EmptySet> = {1} -> {2}
let edge_right: Edge<Int,Int,EmptySet> = {3} -> {4}
edge_left |= edge_right
let original = {{1} -> {2}}
let copy = original
let same_identity = {original, copy}
let distinct = {{1} -> {2}}
let distinct_identity = {original, distinct}
|}
  in
  expect "coercion" "{{1} -> {2}, {2} -> {3}, {3} -> {2}}"
    (Value.to_string (value environment "g"));
  expect "exact decimals"
    "{1.1, 1000000000000000000000000000000.00000000000000000001}"
    (Value.to_string (value environment "decimals"));
  expect "set mutation" "{2}" (Value.to_string (value environment "left"));
  expect "edge surgery" "{1, 3} -> {2, 4}"
    (Value.to_string (value environment "edge_left"));
  expect "opaque copy" "{{{1} -> {2}}}"
    (Value.to_string (value environment "same_identity"));
  expect "opaque distinct" "{{{1} -> {2}}, {{1} -> {2}}}"
    (Value.to_string (value environment "distinct_identity"));

  let unequal_payloads =
    {|
let left: Edge<Int,Int,String> = {1} -["Bob"]-> {2}
let right: Edge<Int,Int,String> = {3} -["Alice"]-> {4}
let invalid = left | right
|}
  in
  match Program.run unequal_payloads with
  | Error (Program.Evaluation_error error)
    when String.equal error.message "edge side surgery requires equal payload values" -> ()
  | Error _ -> failwith "wrong unequal-payload error"
  | Ok _ -> failwith "unequal payload surgery succeeded"
