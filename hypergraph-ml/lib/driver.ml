(* Parse a whole program, reporting failures the way the language talks about
   itself rather than the way the parser generator does. A user who mixes set
   operators should be told the rule, not the automaton state. *)

type error = { line : int; column : int; message : string;
               note : string option }

let position (p : Lexing.position) =
  (p.pos_lnum, p.pos_cnum - p.pos_bol + 1)

(* Shared by both entry points: the same failures mean the same things
   whether a whole file or one line was read. *)
let describe_failure lexbuf = function
  | `Lexer (message, pos) ->
      let line, column = position pos in
      { line; column; message; note = None }
  | `Mixed (a, b, (at : Ast.loc)) ->
      { line = at.line; column = at.column;
        message =
          Printf.sprintf
            "cannot mix '%s' and '%s' in one chain; parenthesize to say which \
             binds first, as in (a %s b) %s c"
            (Ast.op_symbol a) (Ast.op_symbol b) (Ast.op_symbol a)
            (Ast.op_symbol b);
        note = None }
  | `Syntax ->
      let line, column = position (Lexing.lexeme_start_p lexbuf) in
      let found = Lexing.lexeme lexbuf in
      { line; column;
        message =
          (if found = "" then "unexpected end of input"
           else
             Printf.sprintf "unexpected %s"
               (if found = "\n" then "end of line" else "'" ^ found ^ "'"));
        note =
          Option.map
            (fun (c, p) ->
              let l, col = position p in
              Printf.sprintf "inside '%c' opened at %d:%d" c l col)
            (Lexer.unclosed ()) }

let of_problem (p : Validate.problem) =
  { line = p.loc.line; column = p.loc.column;
    message = p.what ^ "; " ^ p.why; note = None }

(* One statement and nothing else. The input is trimmed first, so a trailing
   newline from a prompt does not read as an empty second statement. *)
let parse_line (source : string) : (Ast.stmt, error) result =
  let lexbuf = Lexing.from_string (String.trim source) in
  Lexer.reset ();
  match Parser.line Lexer.token lexbuf with
  | stmt -> (
      match Validate.check [ stmt ] with
      | None -> Ok stmt
      | Some p -> Error (of_problem p))
  | exception Lexer.Error (m, pos) -> Error (describe_failure lexbuf (`Lexer (m, pos)))
  | exception Ast.Mixed_ops (a, b, at) -> Error (describe_failure lexbuf (`Mixed (a, b, at)))
  | exception Parser.Error -> Error (describe_failure lexbuf `Syntax)

let parse (source : string) : (Ast.program, error) result =
  let lexbuf = Lexing.from_string source in
  Lexer.reset ();
  match Parser.program Lexer.token lexbuf with
  | program -> (
      (* Restrictions the grammar cannot state without becoming ambiguous. *)
      match Validate.check program with
      | None -> Ok program
      | Some p -> Error (of_problem p))
  | exception Lexer.Error (m, pos) -> Error (describe_failure lexbuf (`Lexer (m, pos)))
  | exception Ast.Mixed_ops (a, b, at) ->
      Error (describe_failure lexbuf (`Mixed (a, b, at)))
  | exception Parser.Error -> Error (describe_failure lexbuf `Syntax)
