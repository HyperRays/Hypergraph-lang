open Hypergraph
open Hypergraph_analysis

let fail message = raise (Failure message)

let run source =
  match Program.run source with
  | Ok result -> result
  | Error _ -> fail "analysis input did not run"

let matrices source =
  match Incidence.matrices (run source) with
  | Ok matrices -> matrices
  | Error error -> fail (error.binding ^ ": " ^ error.message)

let find_graph name (matrices : Incidence.matrix list) =
  match List.find_opt (fun matrix -> String.equal matrix.Incidence.graph name) matrices with
  | Some matrix -> matrix
  | None -> fail ("missing graph " ^ name)

let columns (matrix : Incidence.matrix) =
  List.concat_map
    (fun (group : Incidence.group) -> group.columns)
    matrix.groups

let entry row (column : Incidence.column) =
  Option.value (List.assoc_opt row column.entries) ~default:0

let contains text fragment =
  let text_length = String.length text and fragment_length = String.length fragment in
  let rec search offset =
    offset + fragment_length <= text_length
    &&
    (String.equal (String.sub text offset fragment_length) fragment
    || search (offset + 1))
  in
  fragment_length = 0 || search 0

let test_inferred_graph () =
  let output =
    matrices
      {|
struct Person {
  name: String,
}
let alice = Person("日本")
let bob = Person("Bob")
let loop = {1} -> {1}
let link = {alice} <-["friend"]-> {bob}
let network = {loop, link}
let ordinary_empty = {}
let empty_graph: Graph<Int,Int,Bottom> = {}
|}
  in
  if List.length output <> 2 then fail "graph classification";
  let network = find_graph "network" output in
  if List.length network.vertices <> 3 then fail "vertex count";
  let network_columns = columns network in
  if List.length network_columns <> 3 then fail "undirected expansion";
  let loop = List.nth network_columns 0 in
  if entry 0 loop <> 2 then fail "self-loop coefficient";
  if not (String.equal (List.nth network_columns 1).label "link[\"friend\"].fwd") then
    fail "forward label";
  if not (String.equal (List.nth network_columns 2).label "link[\"friend\"].bwd") then
    fail "backward label";
  let empty = find_graph "empty_graph" output in
  if empty.vertices <> [] || columns empty <> [] then fail "typed empty graph";
  let text = Incidence.render_text output in
  if not (contains text "Person(\"日本\")") then fail "unicode vertex rendering";
  if not (contains text "graph empty_graph: 0 vertices x 0 columns") then
    fail "empty graph text";
  match Incidence.to_yojson output with
  | `List [ _; `Assoc fields ] -> (
      match List.assoc_opt "graph" fields with
      | Some (`String "empty_graph") -> ()
      | _ -> fail "empty graph JSON")
  | _ -> fail "matrix JSON shape"

let test_realized_coercion_and_mutation () =
  let output =
    matrices
      {|
let directed = {1} -> {2}
let undirected = {2} <-> {3}
let flattened: Set<Edge<Int,Int,Bottom>> = {directed, undirected}
let changing: mut Graph<Int,Int,Bottom> = {directed}
changing -= {directed}
|}
  in
  let flattened = find_graph "flattened" output in
  let flattened_columns = columns flattened in
  if List.length flattened_columns <> 3 then fail "coerced column count";
  if
    List.exists
      (fun (column : Incidence.column) ->
        contains column.label ".fwd" || contains column.label ".bwd")
      flattened_columns
  then fail "realized coercion was expanded twice";
  let changing = find_graph "changing" output in
  if changing.vertices <> [] || columns changing <> [] then
    fail "mutated empty graph was omitted"

let () =
  test_inferred_graph ();
  test_realized_coercion_and_mutation ()
