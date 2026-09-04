open Hypergraph

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

let print_result (result : Program.result) =
  List.iter
    (fun (binding : Check.binding) ->
      match Value.find result.values binding.name with
      | Some value -> Printf.printf "%s = %s\n" binding.name (Value.to_string value)
      | None -> failwith ("missing evaluated binding '" ^ binding.name ^ "'"))
    result.checked.bindings

let run path =
  let source = read_file path in
  match Program.run source with
  | Ok result ->
      print_result result;
      0
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

let usage executable =
  Printf.eprintf "usage: %s FILE\n       %s -\n" executable executable;
  2

let () =
  let status =
    match Array.to_list Sys.argv with
    | [ _; path ] -> (
        try run path
        with Sys_error message ->
          Printf.eprintf "%s: %s\n" (display_path path) message;
          1)
    | executable :: _ -> usage executable
    | [] -> usage "hypergraph_cli"
  in
  exit status
