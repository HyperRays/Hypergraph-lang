(* Front end driver.

     main FILE            report how many statements parsed
     main --line TEXT     parse one statement, the REPL entry point
     main --repl          read statements from stdin, one per prompt

   --repl only parses. Evaluating a statement at a prompt would mean carrying
   an environment across lines, which is worth doing but is not what the flag
   claims yet. *)

let report (e : Hypergraph.Driver.error) =
  Printf.eprintf "parse error: %d:%d: %s\n" e.line e.column e.message;
  Option.iter (Printf.eprintf "  note: %s\n") e.note

let read_all path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

(* A struct body or a set may span lines, so a line that leaves a brace open
   is continued rather than rejected. Anything else is judged as written.

   Everything goes to stdout here, in order. Splitting answers across stdout
   and stderr reorders them under buffering, which in a session reads as the
   error belonging to a different statement than the one that caused it. *)
let repl () =
  let buffer = Buffer.create 64 in
  let say line = print_string line; print_newline (); flush stdout in
  let rec loop () =
    print_string (if Buffer.length buffer = 0 then "> " else "| ");
    flush stdout;
    match input_line stdin with
    | exception End_of_file -> print_newline ()
    | text ->
        Buffer.add_string buffer text;
        Buffer.add_char buffer '\n';
        let source = Buffer.contents buffer in
        if String.trim source = "" then Buffer.clear buffer
        else (
          match Hypergraph.Driver.parse_line source with
          | Ok _ ->
              say "ok";
              Buffer.clear buffer
          | Error _ when Hypergraph.Lexer.unclosed () <> None ->
              () (* not finished; keep reading *)
          | Error e ->
              say (Printf.sprintf "error %d:%d: %s" e.line e.column e.message);
              Option.iter (fun n -> say ("  note: " ^ n)) e.note;
              Buffer.clear buffer);
        loop ()
  in
  loop ()

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  match args with
  | [ "--repl" ] -> repl ()
  | "--line" :: rest -> (
      match Hypergraph.Driver.parse_line (String.concat " " rest) with
      | Ok _ -> print_endline "ok: 1 statement"
      | Error e ->
          report e;
          exit 1)
  | _ -> (
      let parse_only = List.mem "--parse" args in
      (* The plain line-oriented report, which the golden corpus pins. The
         default carries codes and a source excerpt. *)
      let plain = List.mem "--plain" args in
      let incidence = List.mem "--incidence" args in
      let incidence_json = List.mem "--incidence-json" args in
      let want_facts = List.mem "--facts" args in
      let want_schema = List.mem "--facts-schema" args in
      let rec tag_of = function
        | "--tag" :: v :: _ -> v
        | _ :: rest -> tag_of rest
        | [] -> ""
      in
      let tag = tag_of args in
      let flags =
        [ "--parse"; "--incidence"; "--incidence-json"; "--facts";
          "--facts-schema"; "--plain"; "--tag"; tag ]
      in
      let path = List.find (fun a -> not (List.mem a flags)) args in
      match Hypergraph.Driver.parse (read_all path) with
      | Ok program ->
          if parse_only then
            Printf.printf "ok: %d statements\n" (List.length program)
          else
            let out = Hypergraph.Check.check_program program in
            let errors = out.errors in
            let text =
              if plain then out.report
              else Hypergraph.Report.render out program (read_all path) path
            in
            let decls = out.declarations in
            let die e = Printf.eprintf "%s\n" e; exit 1 in
            if want_schema || want_facts then (
              (* Facts describe an evaluated program, so it must check first. *)
              if errors > 0 then (print_string text; exit 1);
              (* Schema before facts: the two together are a complete
                 single-program database in one call. *)
              (if want_schema then
                 match Hypergraph.Facts.schema out with
                 | Ok s -> print_string s
                 | Error e -> die ("facts error: " ^ e));
              if want_facts then
                match Hypergraph.Value.run program decls with
                | Error e -> die ("evaluation error: " ^ e)
                | Ok env -> (
                    match Hypergraph.Facts.facts out env tag with
                    | Ok f -> print_string f
                    | Error e -> die ("facts error: " ^ e)))
            else if incidence || incidence_json then (
              (* Drawn only if it typechecks, so a program the checker would
                 have rejected is never rendered. *)
              if errors > 0 then (print_string text; exit 1);
              match Hypergraph.Value.run program decls with
              | Ok env ->
                  let ms = Hypergraph.Incidence.matrices env in
                  if incidence_json then
                    print_endline (Hypergraph.Incidence.render_json ms);
                  if incidence then
                    print_string (Hypergraph.Incidence.render_text ms)
              | Error e ->
                  Printf.eprintf "evaluation error: %s\n" e;
                  exit 1)
            else (
              print_string text;
              if errors > 0 then exit 1)
      | Error e ->
          report e;
          exit 1)
