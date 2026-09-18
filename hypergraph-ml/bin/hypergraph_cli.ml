open Hypergraph

let () =
  let dump_ast = ref false in
  let filename = ref None in
  let set_filename value =
    match !filename with
    | None -> filename := Some value
    | Some _ -> raise (Arg.Bad "expected at most one input file")
  in
  Arg.parse
    [ ("--ast", Arg.Set dump_ast, "Print the parsed AST as an S-expression");
      ("-", Arg.Unit (fun () -> set_filename "-"), "Read from standard input (the default)") ]
    set_filename "Usage: hypergraph_cli [--ast] [FILE|-]";
  try
    let result = match !filename with
      | None | Some "-" -> Parse.channel stdin
      | Some path -> Parse.file path
    in
    match result with
    | Ok program ->
        if !dump_ast then Format.printf "%a@." Pp.program program
        else Printf.printf "Parsed %d statement(s).\n" (List.length program)
    | Error diagnostic ->
        Format.eprintf "%a@." Diagnostic.pp diagnostic;
        exit 1
  with Sys_error message ->
    Printf.eprintf "I/O error: %s\n" message;
    exit 2
