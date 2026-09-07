open Hypergraph

let fail error =
  failwith
    (Printf.sprintf "%d:%d: %s" error.Driver.line error.column error.message)

let parse source = match Driver.parse source with Ok program -> program | Error e -> fail e

let () =
  let source =
    {|
alias Graph<T,H,P> = Set<Edge<T,H,P> + UndirectedEdge<T,H,P>>
enum Option<A> {
  Some(A),
  None,
}
struct Car<T> {
  wheels: Set<T>,
  weight: Decimal,
}
let car: Car<Int> = Car({1, 2}, 1000.000000000000000000000000000001)
let nothing = Option::None
let edge = {1} -["payload"]-> {1.10}
let reverse = {1.1} <- {1}
let undirected = {1} <-> {2}
let values: mut Set<Int> = {1, 2, 3}
values |= {4}
values &= {2, 4}
values -= {2}
|}
  in
  let program = parse source in
  if List.length program <> 12 then failwith "statement count";
  (match List.nth program 3 with
  | { Ast.it = Ast.Let (_, _, { it = Ast.Apply (_, _, [ _; decimal ]); _ }); _ } ->
      (match decimal.it with
       | Ast.Decimal value ->
           if not (Q.equal value (Q.of_string "1000.000000000000000000000000000001"))
           then failwith "decimal precision"
       | _ -> failwith "expected decimal")
  | _ -> failwith "expected constructor binding");

  let lists =
    parse
      {|
let values: List<Int + String> = [
  1,
  "one",
  1,
]
let edge = {1} -[[1, 2, 1]]-> {2}
|}
  in
  (match lists with
  | [ { Ast.it = Ast.Let (_, _, { it = Ast.List values; _ }); _ };
      { Ast.it = Ast.Let (_, _, { it = Ast.Edge (_, _, Some payload); _ }); _ } ] ->
      if List.length values <> 3 then failwith "list element count";
      (match payload.it with
       | Ast.List values when List.length values = 3 -> ()
       | _ -> failwith "expected list edge payload")
  | _ -> failwith "expected list bindings");

  match Driver.parse "let invalid = ([1]) -> {2}\n" with
  | Error error
    when String.equal error.message
           "a list cannot be the tail of an edge; this position requires a set expression" ->
      ()
  | Error error -> failwith ("wrong list-as-edge-side diagnostic: " ^ error.message)
  | Ok _ -> failwith "list was accepted as an edge side"
