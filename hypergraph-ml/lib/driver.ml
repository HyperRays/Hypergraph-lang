type error = {
  line : int;
  column : int;
  message : string;
  note : string option;
}

let position (position : Lexing.position) =
  (position.pos_lnum, position.pos_cnum - position.pos_bol + 1)

let failure lexbuf = function
  | `Lexer (message, at) ->
      let line, column = position at in
      { line; column; message; note = None }
  | `Mixed (left, right, at) ->
      { line = at.Ast.line;
        column = at.column;
        message =
          Printf.sprintf
            "cannot mix '%s' and '%s' in one chain; use parentheses to make the order explicit"
            (Ast.op_symbol left) (Ast.op_symbol right);
        note = None }
  | `Syntax ->
      let line, column = position (Lexing.lexeme_start_p lexbuf) in
      let found = Lexing.lexeme lexbuf in
      { line;
        column;
        message =
          if found = "" then "unexpected end of input"
          else if found = "\n" then "unexpected end of line"
          else "unexpected '" ^ found ^ "'";
        note =
          Option.map
            (fun (delimiter, opened) ->
              let open_line, open_column = position opened in
              Printf.sprintf "inside '%c' opened at %d:%d" delimiter open_line
                open_column)
            (Lexer.unclosed ()) }

let validated program =
  match Validate.check program with
  | None -> Ok program
  | Some problem ->
      Error
        { line = problem.loc.line;
          column = problem.loc.column;
          message = problem.message;
          note = None }

let parse_with entry source =
  let lexbuf = Lexing.from_string source in
  Lexer.reset ();
  match entry Lexer.token lexbuf with
  | program -> validated program
  | exception Lexer.Error (message, at) ->
      Error (failure lexbuf (`Lexer (message, at)))
  | exception Ast.Mixed_ops (left, right, at) ->
      Error (failure lexbuf (`Mixed (left, right, at)))
  | exception Parser.Error -> Error (failure lexbuf `Syntax)

let parse source = parse_with Parser.program source

let parse_line source =
  match parse_with (fun lexer lexbuf -> [ Parser.line lexer lexbuf ]) source with
  | Ok [ statement ] -> Ok statement
  | Ok _ -> assert false
  | Error error -> Error error
