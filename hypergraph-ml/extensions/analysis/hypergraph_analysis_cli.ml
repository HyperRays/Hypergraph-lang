open Hypergraph
open Hypergraph_analysis

type mode = Text | Json

let read_channel channel =
  let buffer = Buffer.create 4096 in
  let chunk = Bytes.create 4096 in
  let rec read () =
    match input channel chunk 0 (Bytes.length chunk) with
    | 0 -> Buffer.contents buffer
    | count ->
        Buffer.add_subbytes buffer chunk 0 count;
        read ()
  in
  read ()

let read_file path =
  if String.equal path "-" then read_channel stdin
  else
    let channel = open_in_bin path in
    match read_channel channel with
    | source ->
        close_in channel;
        source
    | exception error ->
        close_in_noerr channel;
        raise error

let display_path path = if String.equal path "-" then "<stdin>" else path

let report path (loc : Ast.loc) category message =
  Printf.eprintf "%s:%d:%d: %s: %s\n" (display_path path) loc.line loc.column
    category message

let usage executable =
  Printf.eprintf
    "usage: %s (--incidence | --incidence-json) FILE\n       %s (--incidence | --incidence-json) -\n"
    executable executable;
  2

let parse_arguments = function
  | [ _; "--incidence"; path ] | [ _; path; "--incidence" ] ->
      Ok (Text, path)
  | [ _; "--incidence-json"; path ] | [ _; path; "--incidence-json" ] ->
      Ok (Json, path)
  | executable :: _ -> Error executable
  | [] -> Error "hypergraph_analysis_cli"

let run mode path =
  let source = read_file path in
  match Program.run source with
  | Ok result -> (
      match Incidence.matrices result with
      | Ok matrices ->
          (match mode with
          | Text -> print_string (Incidence.render_text matrices)
          | Json -> print_endline (Incidence.render_json matrices));
          0
      | Error error ->
          Printf.eprintf "%s: incidence error for '%s': %s\n" (display_path path)
            error.binding error.message;
          1)
  | Error (Program.Parse_error error) ->
      report path Ast.{ line = error.line; column = error.column } "parse error"
        error.message;
      1
  | Error (Program.Type_errors diagnostics) ->
      List.iter
        (fun (diagnostic : Check.diagnostic) ->
          report path diagnostic.loc "type error" diagnostic.message)
        diagnostics;
      1
  | Error (Program.Evaluation_error error) ->
      report path error.loc "evaluation error" error.message;
      1

let () =
  let status =
    match parse_arguments (Array.to_list Sys.argv) with
    | Error executable -> usage executable
    | Ok (mode, path) -> (
        try run mode path
        with Sys_error message ->
          Printf.eprintf "%s: %s\n" (display_path path) message;
          1)
  in
  exit status
