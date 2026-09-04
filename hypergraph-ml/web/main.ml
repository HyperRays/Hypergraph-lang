(* The browser entry point.

   One function per output the CLI offers, each taking source text and
   returning text. Nothing here reads a file or a command line, so the same
   module serves a page, a worker, or a test harness under node.

   The Rust and Haskell pair reached the browser as TWO wasm modules with
   separate linear memories, joined by a JavaScript trampoline that copied
   bytes across the boundary in both directions. One implementation needs no
   trampoline: this is the whole of it. *)

open Js_of_ocaml

let string_of_error (e : Hypergraph.Driver.error) =
  Printf.sprintf "parse error: %d:%d: %s%s" e.line e.column e.message
    (match e.note with Some n -> "\n  note: " ^ n | None -> "")

(* Parse, check, and hand the checked program plus its declarations to [k].
   Every entry point needs that prefix, and a program that does not check is
   never evaluated, so a caller cannot draw one the checker would reject. *)
let with_checked source k =
  match Hypergraph.Driver.parse source with
  | Error e -> string_of_error e
  | Ok program -> (
      let out = Hypergraph.Check.check_program program in
      match k out program with
      | Ok text -> text
      | Error text -> text)

let report source =
  with_checked source (fun out program ->
      Ok (Hypergraph.Report.render out program source "input.hg"))

let evaluated source k =
  with_checked source (fun out program ->
      if out.errors > 0 then
        Error (Hypergraph.Report.render out program source "input.hg")
      else
        match Hypergraph.Value.run program out.declarations with
        | Error e -> Error ("evaluation error: " ^ e)
        | Ok env -> k out env)

let incidence source =
  evaluated source (fun _ env ->
      Ok (Hypergraph.Incidence.render_text (Hypergraph.Incidence.matrices env)))

let incidence_json source =
  evaluated source (fun _ env ->
      Ok (Hypergraph.Incidence.render_json (Hypergraph.Incidence.matrices env)))

let facts source tag =
  evaluated source (fun out env ->
      match Hypergraph.Facts.schema out with
      | Error e -> Error ("facts error: " ^ e)
      | Ok schema -> (
          match Hypergraph.Facts.facts out env tag with
          | Error e -> Error ("facts error: " ^ e)
          | Ok f -> Ok (schema ^ f)))

(* Non-zero when the program does not check, so a caller can branch without
   reading the prose. *)
let errors source =
  match Hypergraph.Driver.parse source with
  | Error _ -> 1
  | Ok program -> (Hypergraph.Check.check_program program).errors

let () =
  Js.export "hypergraph"
    (object%js
       method report src = Js.string (report (Js.to_string src))
       method incidence src = Js.string (incidence (Js.to_string src))
       method incidenceJson src = Js.string (incidence_json (Js.to_string src))
       method facts src tag = Js.string (facts (Js.to_string src) (Js.to_string tag))
       method errors src = errors (Js.to_string src)
    end)
