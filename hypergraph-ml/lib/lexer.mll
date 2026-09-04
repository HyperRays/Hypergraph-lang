(* Tokens.

   NEWLINE separates statements, so it is a token rather than whitespace, and
   the grammar says where else one may appear. Suppressing them inside braces
   here was simpler but wrong: it accepted '{a\n & b}', where the newline falls
   in the middle of an element, which the grammar does not allow. A newline is
   free after '{', around an element or field separating comma, and before
   '}', and nowhere else.

   Brackets are still tracked so an unclosed one can be named in an error.

   Compound operators are single tokens, so "g & = e" and "a - [v]-> b" cannot
   parse. ocamllex takes the longest match, which is what keeps '<-[' apart
   from '<-' and ']->' apart from ']-'. *)

{
open Parser

exception Error of string * Lexing.position

let error lexbuf msg = raise (Error (msg, Lexing.lexeme_start_p lexbuf))

(* Open brackets, innermost first.

   Only BRACES hold a statement open. A set literal and a struct body may span
   lines, and those are the only two places the grammar allows a newline:
   'arg_list', 'inst_args', 'type_args' and the parenthesised forms have none,
   so 'Foo(\n1)' is not a call spread over two lines, it is a statement that
   ended at the newline.

   Parentheses are still tracked, because an unclosed one is worth naming in an
   error even though it does not suppress newlines. *)
let opens : (char * Lexing.position) list ref = ref []
let reset () = opens := []


(* The outermost bracket still open, which is where the runaway began. *)
let unclosed () =
  match List.rev !opens with (c, p) :: _ -> Some (c, p) | [] -> None

let push c lexbuf = opens := (c, Lexing.lexeme_start_p lexbuf) :: !opens
let pop () = match !opens with _ :: r -> opens := r | [] -> ()

let unescape lexbuf = function
  | 'n' -> '\n' | 't' -> '\t' | 'r' -> '\r'
  | 'b' -> '\b' | 'f' -> '\012'
  | '"' -> '"' | '\'' -> '\'' | '\\' -> '\\' | '/' -> '/' | '`' -> '`'
  | c -> error lexbuf (Printf.sprintf "unknown escape '\\%c'" c)

(* Integer literals may carry '_' separators: 400_000. *)
let int_of_lexeme lexbuf s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c -> if c <> '_' then Buffer.add_char b c) s;
  match Int64.of_string_opt (Buffer.contents b) with
  | Some n -> n
  | None -> error lexbuf ("integer literal out of range: " ^ s)
}

let alpha    = ['a'-'z' 'A'-'Z']
let digit    = ['0'-'9']
let ident    = alpha (alpha | digit | '_')*
let integer  = '-'? digit (digit | '_')*
let decimal  = '-'? digit+ '.' digit+

rule token = parse
  (* A comment runs to end of line and never consumes the newline, so it
     cannot swallow a statement separator. *)
  | "//" [^ '\n']*        { token lexbuf }
  | ' '+                  { token lexbuf }
  | '\r'                  { token lexbuf }
  | '\n'                  { Lexing.new_line lexbuf; NEWLINE }

  | "let"                 { LET }
  | "struct"              { STRUCT }
  | "type"                { TYPE }

  | "&="                  { OPEQ Ast.Union }
  | "^="                  { OPEQ Ast.Inter }
  | "/="                  { OPEQ Ast.Diff }

  (* Arrows before their prefixes: '<->' before '<-', '<-[' before both,
     ']->' before ']-'. Longest match gives this for free. *)
  | "<->"                 { ARROW_LR }
  | "<-["                 { BANN_L }
  | "<-"                  { ARROW_L }
  | "->"                  { ARROW_R }
  | "-["                  { ANN_L }
  | "]->"                 { ANN_R }
  | "]-"                  { BANN_R }

  | '&'                   { OP Ast.Union }
  | '^'                   { OP Ast.Inter }
  | '/'                   { OP Ast.Diff }

  | '{'                   { push '{' lexbuf; LBRACE }
  | '}'                   { pop (); RBRACE }
  | '('                   { push '(' lexbuf; LPAREN }
  | ')'                   { pop (); RPAREN }
  | '<'                   { LT }
  | '>'                   { GT }
  | ','                   { COMMA }
  | ':'                   { COLON }
  | '='                   { EQUALS }
  | '+'                   { PLUS }
  | '_'                   { UNDERSCORE }

  | decimal as s          { DEC (float_of_string s) }
  | integer as s          { INT (int_of_lexeme lexbuf s) }
  | '#' (digit* as s)     { FRONCE (if s = "" then None else Some (int_of_string s)) }
  | ident as s            { IDENT s }

  (* 'quoted' is a separate entry point, and entering one resets lex_start_p,
     so the token would otherwise be reported at the closing quote. Keep the
     opening quote's position and put it back. *)
  | '"'                   { let start = lexbuf.Lexing.lex_start_p in
                            let s = quoted '"' start (Buffer.create 16) lexbuf in
                            lexbuf.Lexing.lex_start_p <- start; STRING s }
  | '\''                  { let start = lexbuf.Lexing.lex_start_p in
                            let s = quoted '\'' start (Buffer.create 16) lexbuf in
                            lexbuf.Lexing.lex_start_p <- start; STRING s }

  | eof                   { EOF }
  | _ as c                { error lexbuf (Printf.sprintf "unexpected character '%c'" c) }

(* Text is a denylist rather than an allowlist, so 'Zürich' and '日本' are
   writable. A newline cannot appear because it separates statements. *)
and quoted delim start buf = parse
  | '\\' (_ as c)         { Buffer.add_char buf (unescape lexbuf c);
                            quoted delim start buf lexbuf }
  | '\n'                  { raise (Error ("string literal spans a line break", start)) }
  | eof                   { raise (Error ("unterminated string literal", start)) }
  | _ as c                { if c = delim then Buffer.contents buf
                            else (Buffer.add_char buf c;
                                  quoted delim start buf lexbuf) }
