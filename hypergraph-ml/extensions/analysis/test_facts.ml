open Hypergraph
open Hypergraph_analysis

let fail message = raise (Failure message)

let contains text fragment =
  let text_length = String.length text and fragment_length = String.length fragment in
  let rec search offset =
    offset + fragment_length <= text_length
    &&
    (String.equal (String.sub text offset fragment_length) fragment
    || search (offset + 1))
  in
  fragment_length = 0 || search 0

let run source =
  match Program.run source with
  | Ok result -> result
  | Error _ -> fail "facts input did not run"

let schema checked =
  match Facts.schema checked with
  | Ok schema -> schema
  | Error error -> fail error.message

let facts ?tag result =
  match Facts.facts ?tag result with
  | Ok facts -> facts
  | Error error -> fail error.message

let test_schema_and_facts () =
  let result =
    run
      {|
alias Count = Int
struct Record {
  name: String,
  count: Count,
  ratio: Decimal,
}
struct Box<A> {
  value: A,
}
enum Measure {
  Count(Int),
  Exact(Decimal),
  Missing,
}
let record = Record("Alice", 123456789012345678901234567890, 1.10)
let exact = Measure::Exact(1.10)
let missing = Measure::Missing
let nothing = None
let connection = {record, missing, nothing} -[exact]-> {record}
let history = [record, missing, record]
let listed = {history} -> {record}
let graph = {connection, listed}
let copy = graph
let outer = {graph} -> {copy}
let atlas = {outer}
let empty_graph: Graph<Int,Int,Bottom> = {}
|}
  in
  let declarations = schema result.checked in
  List.iter
    (fun expected ->
      if not (contains declarations expected) then
        fail ("schema is missing " ^ expected))
    [ ".decl Record(x: id, name: symbol, count: symbol, ratio: symbol)";
      ".decl Box(x: id, value: id)";
      ".decl Measure__Count(x: id, arg0: symbol)";
      ".decl Measure__Exact(x: id, arg0: symbol)";
      ".decl Measure__Missing(x: id)";
      ".decl Option__Some(x: id, arg0: id)";
      ".decl Option__None(x: id)";
      ".decl val_list(x: id)";
      ".decl val_item(x: id, position: number, value: id)" ] ;
  let emitted = facts ~tag:"document" result in
  List.iter
    (fun expected ->
      if not (contains emitted expected) then fail ("facts are missing " ^ expected))
    [ "\"123456789012345678901234567890\"";
      "val_dec(";
      "\"11\", \"10\"";
      ", \"Alice\", \"123456789012345678901234567890\", \"11/10\").";
      "Measure__Exact(";
      ", \"11/10\").";
      "Measure__Missing(";
      "Option__None(";
      "val_list(";
      "val_item(";
      "graph(\"document:graph\").";
      "graph(\"document:copy\").";
      "graph(\"document:atlas\").";
      "graph(\"document:empty_graph\").";
      "val_graph(";
      "\"document:graph\"";
      "\"document:copy\"";
      "payload(" ] ;
  let repeated = facts ~tag:"document" result in
  if not (String.equal emitted repeated) then fail "fact IDs are not deterministic"

let expect_schema_error source fragment =
  let result = run source in
  match Facts.schema result.checked with
  | Error error when contains error.message fragment -> ()
  | Error error -> fail ("wrong schema error: " ^ error.message)
  | Ok _ -> fail "invalid query schema was accepted"

let test_collisions () =
  expect_schema_error
    {|
struct tail {
  value: Int,
}
|}
    "collides";
  expect_schema_error
    {|
struct Trouble {
  x: Int,
}
|}
    "duplicate attribute 'x'"

let () =
  test_schema_and_facts ();
  test_collisions ()
