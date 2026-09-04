{
open Parser

exception Error of string * Lexing.position

let error lexbuf message = raise (Error (message, Lexing.lexeme_start_p lexbuf))

let opens : (char * Lexing.position) list ref = ref []

let reset () = opens := []

let unclosed () =
  match List.rev !opens with first :: _ -> Some first | [] -> None

let push character lexbuf =
  opens := (character, Lexing.lexeme_start_p lexbuf) :: !opens

let pop expected lexbuf =
  match !opens with
  | (actual, _) :: rest when actual = expected -> opens := rest
  | _ -> error lexbuf (Printf.sprintf "unmatched closing '%c'" expected)

let strip_separators text =
  String.to_seq text |> Seq.filter (( <> ) '_') |> String.of_seq

let integer lexbuf text =
  try Z.of_string (strip_separators text)
  with Invalid_argument _ -> error lexbuf ("invalid integer literal: " ^ text)

let decimal lexbuf text =
  try Q.of_string (strip_separators text)
  with Invalid_argument _ -> error lexbuf ("invalid decimal literal: " ^ text)

let unescape lexbuf = function
  | 'n' -> '\n'
  | 't' -> '\t'
  | 'r' -> '\r'
  | 'b' -> '\b'
  | 'f' -> '\012'
  | '"' -> '"'
  | '\'' -> '\''
  | '\\' -> '\\'
  | '/' -> '/'
  | character ->
      error lexbuf (Printf.sprintf "unknown escape '\\%c'" character)
}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let identifier = alpha (alpha | digit | '_')*
let digits = digit (digit | '_')*
let decimal_literal = digits '.' digits

rule token = parse
  | "//" [^ '\n']*       { token lexbuf }
  | [' ' '\t']+           { token lexbuf }
  | '\r'                  { token lexbuf }
  | '\n'                  { Lexing.new_line lexbuf; NEWLINE }

  | "let"                 { LET }
  | "struct"              { STRUCT }
  | "enum"                { ENUM }
  | "alias"               { ALIAS }
  | "mut"                 { MUT }

  | "|="                  { BAR_EQ }
  | "&="                  { AMP_EQ }
  | "-="                  { MINUS_EQ }
  | "::"                  { DCOLON }

  | "<->"                 { ARROW_LR }
  | "<-["                 { BANN_L }
  | "<-"                  { ARROW_L }
  | "->"                  { ARROW_R }
  | "-["                  { ANN_L }
  | "]->"                 { ANN_R }
  | "]-"                  { BANN_R }

  | '|'                   { BAR }
  | '&'                   { AMP }
  | '-'                   { MINUS }
  | '{'                   { push '{' lexbuf; LBRACE }
  | '}'                   { pop '{' lexbuf; RBRACE }
  | '('                   { push '(' lexbuf; LPAREN }
  | ')'                   { pop '(' lexbuf; RPAREN }
  | '<'                   { push '<' lexbuf; LT }
  | '>'                   { pop '<' lexbuf; GT }
  | ','                   { COMMA }
  | ':'                   { COLON }
  | '='                   { EQUALS }
  | '+'                   { PLUS }
  | '_'                   { UNDERSCORE }

  | decimal_literal as text { DECIMAL (decimal lexbuf text) }
  | digits as text          { INT (integer lexbuf text) }
  | identifier as text      { IDENT text }

  | '"'                   { let start = lexbuf.Lexing.lex_start_p in
                            let value = quoted '"' start (Buffer.create 16) lexbuf in
                            lexbuf.Lexing.lex_start_p <- start;
                            STRING value }
  | '\''                  { let start = lexbuf.Lexing.lex_start_p in
                            let value = quoted '\'' start (Buffer.create 16) lexbuf in
                            lexbuf.Lexing.lex_start_p <- start;
                            STRING value }

  | eof                   { EOF }
  | _ as character        { error lexbuf
                              (Printf.sprintf "unexpected character '%c'" character) }

and quoted delimiter start buffer = parse
  | '\\' (_ as character) { Buffer.add_char buffer (unescape lexbuf character);
                             quoted delimiter start buffer lexbuf }
  | '\n'                  { raise (Error ("string literal spans a line break", start)) }
  | eof                   { raise (Error ("unterminated string literal", start)) }
  | _ as character       { if character = delimiter then Buffer.contents buffer
                            else (Buffer.add_char buffer character;
                                  quoted delimiter start buffer lexbuf) }
