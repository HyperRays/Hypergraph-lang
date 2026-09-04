open Hypergraph

let parse source =
  match Driver.parse source with
  | Ok program -> program
  | Error error ->
      failwith
        (Printf.sprintf "parse %d:%d: %s" error.line error.column error.message)

let check source =
  match Check.check (parse source) with
  | Ok checked -> checked
  | Error diagnostics ->
      failwith
        (String.concat "\n"
           (List.map
              (fun (diagnostic : Check.diagnostic) ->
                Printf.sprintf "%d:%d: %s" diagnostic.Check.loc.line
                  diagnostic.loc.column diagnostic.message)
              diagnostics))

let () =
  let checked =
    check
      {|
struct Pair<A,B> {
  first: A,
  second: B,
}
enum Maybe<A> {
  Some(A),
  None,
}
alias Vertices<T> = Set<T>
let pair: Pair<Int,String> = Pair(1, "one")
let inferred = Pair(2, "two")
let some: Maybe<Int> = Maybe::Some(3)
let none: Maybe<Int> = Maybe::None
let directed: Edge<Int,Int,Bottom> = {1} -> {2}
let undirected: UndirectedEdge<Int,Int,Bottom> = {2} <-> {3}
let graph: Graph<Int,Int,Bottom> = {directed, undirected}
let flattened: Set<Edge<Int,Int,Bottom>> = {directed, undirected}
let vertices: mut Vertices<Int> = {1, 2}
vertices |= {3}
|}
  in
  if List.length checked.Check.bindings <> 9 then failwith "binding count";
  if checked.coercions = [] then failwith "missing undirected-edge coercion";
  let inferred = Option.get (Check.find_binding checked "inferred") in
  let printed = Format.asprintf "%a" Check.pp_solved_type inferred in
  if String.length printed = 0 then failwith "empty solved type";

  let invalid =
    {|
let values: Set<Int> = {1}
values |= {2}
|}
  in
  match Check.check (parse invalid) with
  | Error [ diagnostic ] when String.equal diagnostic.message "binding 'values' is immutable" -> ()
  | Error diagnostics ->
      failwith
        ("wrong immutable diagnostic: "
        ^ String.concat "; "
            (List.map (fun (d : Check.diagnostic) -> d.message) diagnostics))
  | Ok _ -> failwith "immutable update accepted"
