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

let contains ~needle haystack =
  let needle_length = String.length needle in
  let haystack_length = String.length haystack in
  let rec search offset =
    offset + needle_length <= haystack_length
    &&
    (String.equal (String.sub haystack offset needle_length) needle
    || search (offset + 1))
  in
  needle_length = 0 || search 0

let expect_type_error source expected =
  match Check.check (parse source) with
  | Error diagnostics
    when List.exists
           (fun (diagnostic : Check.diagnostic) ->
             contains ~needle:expected diagnostic.message)
           diagnostics ->
      ()
  | Error diagnostics ->
      failwith
        ("wrong type diagnostic: "
        ^ String.concat "; "
            (List.map (fun (d : Check.diagnostic) -> d.message) diagnostics))
  | Ok _ -> failwith "invalid sum-valued program was accepted"

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
let values = {1}
values |= {2}
|}
  in
  (match Check.check (parse invalid) with
  | Error [ diagnostic ] when String.equal diagnostic.message "binding 'values' is immutable" -> ()
  | Error diagnostics ->
      failwith
        ("wrong immutable diagnostic: "
        ^ String.concat "; "
            (List.map (fun (d : Check.diagnostic) -> d.message) diagnostics))
  | Ok _ -> failwith "immutable update accepted");

  ignore
    (check
       {|
alias Values<T> = Set<T>
alias Sequence<T> = List<T>
struct Bucket<A> {
  values: Set<A>,
}
struct ListBucket<A> {
  values: List<A>,
}
let singleton: Set<Int + String> = {1}
let heterogeneous: Values<Int + String> = {1, "one"}
let widened: Set<Int + String> = {1} | {"one"}
let list_singleton: List<Int + String> = [1]
let heterogeneous_list: Sequence<Int + String> = [1, "one", 1]
let empty_list: List<Int> = []
let edge: Edge<Int + String,String,Bottom> = {1} -> {"head"}
let absent_payload: Edge<Int,Int,Int + String> = {1} -> {2}
let no_value: Option<Int + String> = None
let bucket: Bucket<Int + String> = Bucket<Int + String>({1, "one"})
let list_bucket: ListBucket<Int + String> = ListBucket<Int + String>([1, "one"])
let integer_option: Option<Int> = Some(1)
let string_option: Option<String> = Some("one")
let option_set: Set<Option<Int> + Option<String>> = {integer_option, string_option}
let option_list: List<Option<Int> + Option<String>> = [integer_option, string_option]
|});

  let preserved =
    check
      {|
let undirected = {1} <-> {2}
let values: List<UndirectedEdge<Int,Int,Bottom>> = [undirected]
|}
  in
  if preserved.coercions <> [] then failwith "list unexpectedly recorded a coercion";

  expect_type_error
    {|
let undirected = {1} <-> {2}
let impossible: List<Edge<Int,Int,Bottom>> = [undirected]
|}
    "found UndirectedEdge<Int, Int, Bottom>, expected Edge<Int, Int, Bottom>";

  expect_type_error
    {|
let left = [1]
let right = [2]
let impossible = left | right
|}
    "requires only sets or only edges";

  expect_type_error
    {|
let values: mut List<Int> = [1]
values |= values
|}
    "requires matching set or edge operands";

  expect_type_error
    {|
let impossible: Int + String = 1
|}
    "found Int, expected Int + String";

  expect_type_error
    {|
alias Scalar = Int + String
let impossible: Scalar = 1
|}
    "found Int, expected Int + String";

  expect_type_error
    {|
let narrow: Option<Int> = Some(1)
let impossible: Option<Int + String> = narrow
|}
    "found Int, expected Int + String";

  expect_type_error
    {|
struct Box<A> {
  value: A,
}
let narrow: Box<Int> = Box(1)
let impossible: Box<Int + String> = narrow
|}
    "found Int, expected Int + String";

  expect_type_error
    {|
let narrow: Edge<Int,Int,Int> = {1} -[1]-> {2}
let impossible: Edge<Int,Int,Int + String> = narrow
|}
    "found Int, expected Int + String"
