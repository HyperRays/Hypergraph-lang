(* The user-facing report: diagnostics with a code and a source excerpt, then
   what each statement bound.

   The plain line-oriented form lives in check.ml and is what the golden corpus
   pins. This one adds the excerpt and the code, which is what a reader wants
   and what a consumer reads to decide success without scraping prose. *)

open Ast

let source_line source line =
  match List.nth_opt (String.split_on_char '\n' source) (line - 1) with
  | Some l ->
      (* trailing whitespace would push the caret off *)
      let rec trim n = if n > 0 && l.[n - 1] = ' ' then trim (n - 1) else n in
      String.sub l 0 (trim (String.length l))
  | None -> ""

let diagnostic b (d : Check.diagnostic) (loc : loc option) source name =
  Buffer.add_string b (Printf.sprintf "error[%s]: %s\n" d.code d.message);
  (match loc with
   | Some l ->
       let w = String.length (string_of_int l.line) in
       let blank = String.make w ' ' in
       Buffer.add_string b
         (Printf.sprintf " --> %s:%d:%d\n%s |\n%d | %s\n%s | %s^\n" name l.line
            l.column blank l.line (source_line source l.line) blank
            (String.make (max 0 (l.column - 1)) ' '))
   | None ->
       Buffer.add_string b (Printf.sprintf " --> statement %d\n" d.statement));
  List.iter (fun n -> Buffer.add_string b ("  = note: " ^ n ^ "\n")) d.notes;
  List.iter (fun h -> Buffer.add_string b ("  = help: " ^ h ^ "\n")) d.helps

let render (out : Check.outcome) (program : program) source name =
  let b = Buffer.create 1024 in
  let loc_of i = Option.map (fun (s : stmt) -> s.loc) (List.nth_opt program (i - 1)) in
  let last =
    List.fold_left max 0
      (List.map (fun (d : Check.diagnostic) -> d.statement) out.diagnostics
      @ List.map fst out.judgments)
  in
  for statement = 1 to last do
    List.iter
      (fun (d : Check.diagnostic) ->
        if d.statement = statement then
          diagnostic b d (loc_of statement) source name)
      out.diagnostics;
    List.iter
      (fun (n, msg) ->
        if n = statement then
          Buffer.add_string b (Printf.sprintf "stmt %d: %s\n" n msg))
      out.judgments
  done;
  Buffer.add_string b
    (if out.errors = 0 then "typecheck: OK\n"
     else Printf.sprintf "typecheck: %d error(s)\n" out.errors);
  Buffer.contents b
