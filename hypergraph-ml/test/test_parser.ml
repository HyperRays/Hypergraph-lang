open Hypergraph
open Ast
open Location

let check condition message = if not condition then failwith message

let unwrap = function
  | Ok value -> value
  | Error diagnostic -> failwith (Diagnostic.to_string diagnostic)

let parse source = unwrap (Parse.string source)
let expr source = unwrap (Parse.expression (Lexing.from_string source))
let typ source = unwrap (Parse.type_expression (Lexing.from_string source))

let rejects parser kind source =
  match parser source with
  | Ok _ -> failwith ("unexpectedly accepted: " ^ source)
  | Error diagnostic -> check (diagnostic.Diagnostic.kind = kind) "wrong error kind"

let expr_result source = Parse.expression (Lexing.from_string source)
let typ_result source = Parse.type_expression (Lexing.from_string source)

let rec type_shape (value : typ) =
  match value.value with
  | Named_type (name, arguments) -> name.value ^ "<" ^ String.concat "," (List.map type_shape arguments) ^ ">"
  | Sum_type (a, b) -> "(" ^ type_shape a ^ "+" ^ type_shape b ^ ")"

let is_name expected (value : expr) =
  match value.value with Name name -> name.value = expected | _ -> false

let test_declarations () =
  match parse {|struct myCar<T,B> { axel: T, gear: B, model_no: Int, }
                enum Option<A> { Some(A), None, }
                alias Graph<T,H,P> = Set<Edge<T,H,P> + UndirectedEdge<T,H,P>>|} with
  | [{ value = Struct car; _ }; { value = Enum option_; _ }; { value = Alias graph; _ }] ->
      check (car.name.value = "myCar") "struct name";
      check (List.map (fun (p : identifier) -> p.value) car.parameters = ["T"; "B"]) "parameters";
      check (List.map (fun f -> f.field_name.value) car.fields = ["axel"; "gear"; "model_no"]) "fields";
      check (List.map (fun v -> v.variant_name.value) option_.variants = ["Some"; "None"]) "variants";
      check (type_shape graph.body = "Set<(Edge<T<>,H<>,P<>>+UndirectedEdge<T<>,H<>,P<>>)>") "alias body"
  | _ -> failwith "declaration shapes"

let test_bindings () =
  match parse "let x = {} let a: mut Set<Int> = {1}; a |= {2} a &= {1} a -= {}" with
  | [{ value = Let x; _ }; { value = Let a; _ };
     { value = Update u; _ }; { value = Update i; _ }; { value = Update d; _ }] ->
      check (x.annotation = None && not x.mutable_) "inferred binding";
      check a.mutable_ "mut annotation";
      check (Option.map type_shape a.annotation = Some "Set<Int<>>") "typed binding";
      check ([u.operator; i.operator; d.operator] = [Union; Intersection; Difference]) "updates"
  | _ -> failwith "binding shapes"

let test_constructors () =
  match (expr {|Car(4, 1000.0)|}).value, (expr "Option::Some(1)").value,
        (expr "Option::None").value, (expr "Some(1)").value, (expr "None").value with
  | Construct (car, [{ value = Int "4"; _ }; { value = Decimal "1000.0"; _ }]),
    Variant (option_, some, Some [{ value = Int "1"; _ }]), Variant (_, none, None),
    Construct (short_some, [_]), Name short_none ->
      check ([car.value; option_.value; some.value; none.value; short_some.value; short_none.value]
             = ["Car"; "Option"; "Some"; "None"; "Some"; "None"]) "constructor names"
  | _ -> failwith "constructor shapes"

let test_collections () =
  match (expr {|{[], [1, "one", 1,], {{}},}|}).value with
  | Set [{ value = List []; _ };
         { value = List [{ value = Int "1"; _ }; { value = String "one"; _ }; { value = Int "1"; _ }]; _ };
         { value = Set [{ value = Set []; _ }]; _ }] -> ()
  | _ -> failwith "nested collection shape or list order"

let test_edges () =
  List.iter (fun (source, direction, payload) ->
    match (expr source).value with
    | Edge edge ->
        check (edge.direction = direction) ("direction: " ^ source);
        check (Option.is_some edge.payload = payload) ("payload: " ^ source);
        check (is_name "a" edge.left && is_name "b" edge.right) "written endpoint order"
    | _ -> failwith ("expected edge: " ^ source))
    ["a -> b", Forward, false; "a <- b", Backward, false; "a <-> b", Undirected, false;
     "a -[1]-> b", Forward, true; "a <-[1]- b", Backward, true; "a <-[1]-> b", Undirected, true];
  ignore (expr {|{{1}->{2}, {2}<-> {3}, {2}<-["p"]-{1}}|});
  ignore (expr {|a -[[1,2]]-> b|});
  ignore (expr {|a -[{1} -> {2}]-> b|});
  ignore (expr {|(a -> b) -> c|});
  ignore (expr {|a -> (b -> c)|});
  rejects expr_result Diagnostic.Syntax "a -> b -> c"

let test_precedence () =
  (match (expr "a | b - c & d").value with
   | Binary (Difference, { value = Binary (Union, a, b); _ },
              { value = Binary (Intersection, c, d); _ }) ->
       check (is_name "a" a && is_name "b" b && is_name "c" c && is_name "d" d) "operands"
   | _ -> failwith "operator precedence");
  (match (expr "a | b -> c - d").value with
   | Edge { left = { value = Binary (Union, _, _); _ };
            right = { value = Binary (Difference, _, _); _ }; _ } -> ()
   | _ -> failwith "arrow precedence");
  (match (expr "a-1").value with
   | Binary (Difference, _, { value = Int "1"; _ }) -> ()
   | _ -> failwith "minus without whitespace");
  (match (expr "a--1").value with
   | Binary (Difference, _, { value = Int "-1"; _ }) -> ()
   | _ -> failwith "negative operand");
  (match (expr "a - [1]").value with
   | Binary (Difference, _, { value = List [_]; _ }) -> ()
   | _ -> failwith "difference and list versus payload opener")

let test_types () =
  check (type_shape (typ "List<List<Int + String>>") = "List<List<(Int<>+String<>)>>") "nested sum";
  check (type_shape (typ "!") = type_shape (typ "Bottom")) "bottom shorthand";
  check (type_shape (typ "(Int + String) + !") = "((Int<>+String<>)+Bottom<>)") "parenthesized sum";
  check (type_shape (typ "Opaque<Set<Int>, Marker>") = "Opaque<Set<Int<>>,Marker<>>") "ordinary named types"

let test_exact_numbers () =
  let huge = String.make 200 '9' in
  (match (expr huge).value with Int actual -> check (actual = huge) "large integer" | _ -> failwith "int");
  let decimal = "-0." ^ String.make 200 '0' ^ "10" in
  (match (expr decimal).value with
   | Decimal actual -> check (actual = decimal) "exact decimal"
   | _ -> failwith "decimal");
  check ((expr "1.1").value <> (expr "1.10").value) "normalization is deferred"

let test_strings () =
  let source = {|"quote: \" slash: \\ \/ \n\r\t\b\f café"|} in
  (match (expr source).value with
   | String actual -> check (actual = "quote: \" slash: \\ / \n\r\t\b\012 café") "string escapes"
   | _ -> failwith "string");
  let value = expr source in
  check (value.loc.start.pos_cnum = 0 && value.loc.stop.pos_cnum = String.length source) "string span"

let test_locations () =
  let source = "// heading\r\n/* outer\n /* nested */ */\rlet x = \"ok\"\nlet y = 2" in
  match unwrap (Parse.string ~filename:"locations.hg" source) with
  | [{ value = Let first; loc; _ }; { value = Let second; _ }] ->
      check (loc.start.pos_fname = "locations.hg" && loc.start.pos_lnum = 4 && column loc.start = 1) "statement start";
      check (first.name.loc.start.pos_lnum = 4 && column first.name.loc.start = 5) "identifier location";
      check (column first.value.loc.start = 9 && column first.value.loc.stop = 13) "string location";
      check (loc.stop.pos_lnum = 4 && column loc.stop = 13) "statement stop";
      check (second.name.loc.start.pos_lnum = 5) "line after string"
  | _ -> failwith "location test shape"

let test_errors () =
  List.iter (rejects Parse.string Diagnostic.Syntax)
    ["let x ="; "let = 1"; "let x: = 1"; "let x: mut = 1";
     "let mut x = 1"; "struct A { x Int }"; "enum E { A(Int }";
     "alias A ="; "x = {}"; "let x = {1 2}"; "let x = [1,,2]";
     "let x = Foo::"; "let x = a -[]-> b"; "let x = a <-[1] b";
     "let x = a -[1]- b"; "let x = {1}" ^ " garbage"];
  List.iter (rejects typ_result Diagnostic.Syntax) ["Set<>"; "Int +"; "List<Int"; "Int String"];
  List.iter (rejects Parse.string Diagnostic.Lexical)
    ["let x = @"; "let x = 1foo"; "let x = 1.2foo"; "let x = 1.2.3";
     {|let x = "unterminated|}; {|let x = "trailing\|}; {|let x = "\q"|};
     "let x = \"raw\nnewline\""; "let x = \"raw\000byte\""; "/* not closed"; "/* /* */"];
  (match Parse.string ~filename:"broken.hg" "let x =\n  ]" with
   | Error diagnostic ->
       check (Diagnostic.to_string diagnostic = "broken.hg:2:3-4: syntax error: unexpected ']'") "formatted diagnostic"
   | Ok _ -> failwith "expected syntax error");
  (match Parse.string "let x =\n  \"unterminated" with
   | Error diagnostic ->
       check (diagnostic.loc.start.pos_lnum = 2 && column diagnostic.loc.start = 3) "unterminated string origin"
   | Ok _ -> failwith "expected unterminated string")

let test_syntax_only () =
  (* These require a semantic checker. The syntax front end must retain them. *)
  ignore (parse {|let value: Int + String = 1
                  let x: MissingType = Unknown(1)
                  let x = 2
                  x |= {3}
                  let edge = 1 -> 2|})

let test_refills () =
  let contents = String.make 100_000 'x' in
  let source = "/*" ^ contents ^ "*/\nlet x = \"" ^ contents ^ "\"\nlet y = 2" in
  let path = Filename.temp_file "hypergraph-parser-" ".hg" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    let output = open_out_bin path in
    Fun.protect ~finally:(fun () -> close_out_noerr output) (fun () -> output_string output source);
    match unwrap (Parse.file path) with
    | [{ value = Let { value = { value = String actual; loc }; _ }; _ }; second] ->
        check (actual = contents) "string across channel refills";
        check (loc.start.pos_lnum = 2 && column loc.start = 9) "refilled string start";
        check (loc.stop.pos_lnum = 2 && column loc.stop = 100_011) "refilled string end";
        check (second.loc.start.pos_lnum = 3) "position after refill"
    | _ -> failwith "channel parse")

let test_specification path () =
  let input = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr input) (fun () ->
    let buffer = Buffer.create 256 in
    let in_hg = ref false in
    let blocks = ref 0 in
    let line_number = ref 0 in
    let start_line = ref 0 in
    (try while true do
       let line = input_line input in
       incr line_number;
       match String.trim line with
       | "```hg" when not !in_hg ->
           in_hg := true; start_line := !line_number + 1; Buffer.clear buffer
       | "```" when !in_hg ->
           in_hg := false; incr blocks;
           let lexbuf = Lexing.from_string (Buffer.contents buffer) in
           Lexing.set_position lexbuf {
             pos_fname = path; pos_lnum = !start_line; pos_bol = 0; pos_cnum = 0 };
           ignore (unwrap (Parse.program lexbuf))
       | _ when !in_hg -> Buffer.add_string buffer line; Buffer.add_char buffer '\n'
       | _ -> ()
     done with End_of_file -> ());
    check (not !in_hg) "unclosed hg fence";
    check (!blocks > 0) "no specification examples found";
    Printf.printf "Parsed all %d hg examples from the specification.\n" !blocks)

let () =
  let tests = [
    "declarations", test_declarations;
    "bindings and updates", test_bindings;
    "constructors and Option shorthand", test_constructors;
    "collections", test_collections;
    "all six edge forms", test_edges;
    "precedence and minus", test_precedence;
    "type expressions", test_types;
    "arbitrary precision literals", test_exact_numbers;
    "strings", test_strings;
    "comments and source locations", test_locations;
    "lexical and syntax errors", test_errors;
    "semantic checking is deferred", test_syntax_only;
    "channel refills", test_refills;
    "empty program", (fun () -> check (parse "// nothing\n/* here */" = []) "empty program");
    "empty declarations", (fun () -> ignore (parse "struct Unit {} enum Void {} enum Pair<A,B> { Pair(A,B), Empty(), }"));
    "specification examples", test_specification Sys.argv.(1);
  ] in
  let failures = ref 0 in
  List.iter (fun (name, test) ->
    try test (); Printf.printf "ok: %s\n%!" name
    with exn -> incr failures; Printf.eprintf "FAIL: %s: %s\n%!" name (Printexc.to_string exn)) tests;
  if !failures > 0 then exit 1
