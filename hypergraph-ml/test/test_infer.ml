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
                Printf.sprintf "%d:%d: %s" diagnostic.loc.line
                  diagnostic.loc.column diagnostic.message)
              diagnostics))

let binding checked name =
  match Check.find_binding checked name with
  | Some binding -> binding
  | None -> failwith ("missing binding '" ^ name ^ "'")

let solved_type checked name =
  Format.asprintf "%a" Check.pp_solved_type (binding checked name)

let print_type ty = Format.asprintf "%a" Solver.pp_term (Types.to_solver ty)

let expect_type checked name expected =
  let actual = solved_type checked name in
  let expected = print_type expected in
  if not (String.equal actual expected) then
    failwith
      (Printf.sprintf "%s: expected inferred type %s, got %s" name expected actual)

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

let expect_whole_file_refinement () =
  let checked =
    check
      {|
enum Deferred<A> {
  Present(A),
  Missing,
}
let pending = Deferred::Missing
let pinned: Deferred<Int> = pending
|}
  in
  let pending = solved_type checked "pending" in
  let pinned = solved_type checked "pinned" in
  if not (String.equal pending pinned) then
    failwith
      (Printf.sprintf
         "later statement did not refine the earlier binding:\n  pending: %s\n  pinned:  %s"
         pending pinned);
  if not (contains ~needle:"builtin:Int" pending) then
    failwith ("whole-file inference did not retain the Int constraint: " ^ pending)

let expect_whole_file_contradiction () =
  let source =
    {|
enum Deferred<A> {
  Present(A),
  Missing,
}
let pending = Deferred::Missing
let as_int: Deferred<Int> = pending
let as_string: Deferred<String> = pending
|}
  in
  match Check.check (parse source) with
  | Error diagnostics
    when List.exists
           (fun (diagnostic : Check.diagnostic) ->
             contains ~needle:"type constraints are inconsistent" diagnostic.message)
           diagnostics ->
      ()
  | Error diagnostics ->
      failwith
        ("wrong whole-file contradiction diagnostic: "
        ^ String.concat "; "
            (List.map
               (fun (diagnostic : Check.diagnostic) -> diagnostic.message)
               diagnostics))
  | Ok _ -> failwith "contradictory constraints across statements were accepted"

let expect_annotation_free_document () =
  let source =
    {|
struct Pair<A,B> {
  first: A,
  second: B,
}
enum Wrapped<A> {
  Wrap(A),
}
enum Deferred<A> {
  Present(A),
  Missing,
}
let number = 1
let label = "one"
let pair = Pair(number, label)
let wrapped = Wrapped::Wrap(pair)
let missing = Deferred::Missing
let none = None
let numbers = {number, 2, 3}
let all_numbers = numbers | {4}
let edge = {number} -> {2}
let payload_edge = {2} -[pair]-> {3}
let maybe_pair = Some(pair)
|}
  in
  let program = parse source in
  List.iter
    (fun statement ->
      match statement.Ast.it with
      | Ast.Let (name, Some _, _) ->
          failwith ("test input unexpectedly annotates binding '" ^ name ^ "'")
      | _ -> ())
    program;
  let checked =
    match Check.check program with
    | Ok checked -> checked
    | Error diagnostics ->
        failwith
          ("annotation-free document failed inference: "
          ^ String.concat "; "
              (List.map
                 (fun (diagnostic : Check.diagnostic) -> diagnostic.message)
                 diagnostics))
  in
  let pair =
    Types.Named ("Pair", [ ("first", Types.Int); ("second", Types.String) ])
  in
  expect_type checked "number" Types.Int;
  expect_type checked "label" Types.String;
  expect_type checked "pair" pair;
  expect_type checked "wrapped" (Types.Named ("Wrapped", [ ("Wrap:0", pair) ]));
  expect_type checked "missing"
    (Types.Named
       ("Deferred", [ ("Present:0", Types.Empty); ("Missing", Types.Empty) ]));
  expect_type checked "none" (Types.Option Types.Empty);
  expect_type checked "numbers" (Types.Set Types.Int);
  expect_type checked "all_numbers" (Types.Set Types.Int);
  expect_type checked "edge"
    (Types.Edge (Types.Directed, Types.Int, Types.Int, Types.Empty));
  expect_type checked "payload_edge"
    (Types.Edge (Types.Directed, Types.Int, Types.Int, pair));
  expect_type checked "maybe_pair" (Types.Option pair)

let () =
  expect_annotation_free_document ();
  expect_whole_file_refinement ();
  expect_whole_file_contradiction ()
