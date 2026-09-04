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

let () =
  expect_whole_file_refinement ();
  expect_whole_file_contradiction ()
