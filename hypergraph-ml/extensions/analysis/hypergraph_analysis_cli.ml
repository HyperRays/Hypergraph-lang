open Hypergraph
open Hypergraph_analysis

type facts_request = { schema : bool; facts : bool; tag : string }

type mode =
  | Incidence_text
  | Incidence_json
  | Facts of facts_request

type options = {
  incidence : bool;
  incidence_json : bool;
  schema : bool;
  facts : bool;
  tag : string option;
  path : string option;
}

let no_options =
  { incidence = false;
    incidence_json = false;
    schema = false;
    facts = false;
    tag = None;
    path = None }

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
    "usage: %s (--incidence | --incidence-json) FILE\n       %s [--facts-schema] [--facts] [--tag TAG] FILE\n"
    executable executable;
  2

let parse_arguments arguments =
  let executable, arguments =
    match arguments with
    | executable :: arguments -> (executable, arguments)
    | [] -> ("hypergraph_analysis_cli", [])
  in
  let rec collect options = function
    | [] -> Ok options
    | "--incidence" :: rest -> collect { options with incidence = true } rest
    | "--incidence-json" :: rest ->
        collect { options with incidence_json = true } rest
    | "--facts-schema" :: rest -> collect { options with schema = true } rest
    | "--facts" :: rest -> collect { options with facts = true } rest
    | "--tag" :: tag :: rest -> collect { options with tag = Some tag } rest
    | "--tag" :: [] -> Error (executable, "--tag requires a value")
    | argument :: _ when String.length argument > 1 && argument.[0] = '-' ->
        Error (executable, "unknown option '" ^ argument ^ "'")
    | path :: rest -> (
        match options.path with
        | None -> collect { options with path = Some path } rest
        | Some _ -> Error (executable, "exactly one input file is required"))
  in
  match collect no_options arguments with
  | Error _ as error -> error
  | Ok options -> (
      match options.path with
      | None -> Error (executable, "an input file is required")
      | Some path ->
          let incidence_count =
            (if options.incidence then 1 else 0)
            + if options.incidence_json then 1 else 0
          in
          let wants_facts = options.schema || options.facts in
          if incidence_count > 1 then
            Error (executable, "--incidence and --incidence-json are mutually exclusive")
          else if incidence_count > 0 && wants_facts then
            Error (executable, "incidence and facts output modes cannot be mixed")
          else if options.tag <> None && not wants_facts then
            Error (executable, "--tag is only valid with facts output")
          else if incidence_count = 0 && not wants_facts then
            Error (executable, "select an incidence or facts output mode")
          else if options.incidence then Ok (Incidence_text, path)
          else if options.incidence_json then Ok (Incidence_json, path)
          else
            Ok
              ( Facts
                  { schema = options.schema;
                    facts = options.facts;
                    tag = Option.value options.tag ~default:"" },
                path ))

let evaluate path checked =
  match Value.run checked with
  | Ok values -> Ok Program.{ checked; values }
  | Error error ->
      report path error.loc "evaluation error" error.message;
      Error ()

let render_incidence path checked json =
  match evaluate path checked with
  | Error () -> 1
  | Ok result -> (
      match Incidence.matrices result with
      | Error error ->
          Printf.eprintf "%s: incidence error for '%s': %s\n" (display_path path)
            error.binding error.message;
          1
      | Ok matrices ->
          if json then print_endline (Incidence.render_json matrices)
          else print_string (Incidence.render_text matrices);
          0)

let render_facts path checked (request : facts_request) =
  match Facts.schema checked with
  | Error error ->
      Printf.eprintf "%s: facts error: %s\n" (display_path path) error.message;
      1
  | Ok schema ->
      if request.schema then print_string schema;
      if not request.facts then 0
      else
        match evaluate path checked with
        | Error () -> 1
        | Ok result -> (
            match Facts.facts ~tag:request.tag result with
            | Ok facts ->
                print_string facts;
                0
            | Error error ->
                Printf.eprintf "%s: facts error: %s\n" (display_path path)
                  error.message;
                1)

let run mode path =
  let source = read_file path in
  match Driver.parse source with
  | Error error ->
      report path Ast.{ line = error.line; column = error.column } "parse error"
        error.message;
      1
  | Ok program -> (
      match Check.check program with
      | Error diagnostics ->
          List.iter
            (fun (diagnostic : Check.diagnostic) ->
              report path diagnostic.loc "type error" diagnostic.message)
            diagnostics;
          1
      | Ok checked -> (
          match mode with
          | Incidence_text -> render_incidence path checked false
          | Incidence_json -> render_incidence path checked true
          | Facts request -> render_facts path checked request))

let () =
  let status =
    match parse_arguments (Array.to_list Sys.argv) with
    | Error (executable, message) ->
        Printf.eprintf "%s\n" message;
        usage executable
    | Ok (mode, path) -> (
        try run mode path
        with Sys_error message ->
          Printf.eprintf "%s: %s\n" (display_path path) message;
          1)
  in
  exit status
