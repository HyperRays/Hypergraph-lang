{
open Parser

exception Error of Diagnostic.t

let error loc message = raise (Error { Diagnostic.kind = Lexical; loc; message })
let error_here lexbuf message = error (Location.of_lexbuf lexbuf) message

let keyword = function
  | "struct" -> STRUCT
  | "enum" -> ENUM
  | "alias" -> ALIAS
  | "let" -> LET
  | "mut" -> MUT
  | name -> IDENT name
}

let digit = ['0'-'9']
let identifier_start = ['a'-'z' 'A'-'Z' '_']
let identifier_rest = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let newline = "\r\n" | '\n' | '\r'

rule token = parse
  | [' ' '\t']+ { token lexbuf }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | "//" [^ '\n' '\r']* { token lexbuf }
  | "/*" { comment (Lexing.lexeme_start_p lexbuf) 1 lexbuf; token lexbuf }
  | identifier_start identifier_rest* as name { keyword name }
  | digit+ ('.' digit+)? identifier_start identifier_rest*
      { error_here lexbuf "a numeric literal cannot have an identifier suffix" }
  | digit+ '.' digit+ as value { DECIMAL value }
  | digit+ as value { INT value }
  | '"' {
      let start = Lexing.lexeme_start_p lexbuf in
      let value = string start (Buffer.create 32) lexbuf in
      (* Recursive string rules change the start position. Restore it so the
         parser records the whole string, even across lexbuf refills. *)
      lexbuf.Lexing.lex_start_p <- start;
      STRING value
    }
  | "<-[" { LEFT_PAYLOAD }
  | "-[" { RIGHT_PAYLOAD }
  | "<->" { BOTH_ARROW }
  | "->" { RIGHT_ARROW }
  | "<-" { LEFT_ARROW }
  | "|=" { PIPE_EQUAL }
  | "&=" { AMP_EQUAL }
  | "-=" { MINUS_EQUAL }
  | "::" { DCOLON }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '<' { LT }
  | '>' { GT }
  | ':' { COLON }
  | ',' { COMMA }
  | ';' { SEMICOLON }
  | '=' { EQUAL }
  | '+' { PLUS }
  | '!' { BANG }
  | '|' { PIPE }
  | '&' { AMP }
  | '-' { MINUS }
  | eof { EOF }
  | _ as c { error_here lexbuf (Printf.sprintf "unexpected character %C" c) }

and string start buffer = parse
  | '"' { Buffer.contents buffer }
  | "\\\"" { Buffer.add_char buffer '"'; string start buffer lexbuf }
  | "\\\\" { Buffer.add_char buffer '\\'; string start buffer lexbuf }
  | "\\/" { Buffer.add_char buffer '/'; string start buffer lexbuf }
  | "\\n" { Buffer.add_char buffer '\n'; string start buffer lexbuf }
  | "\\r" { Buffer.add_char buffer '\r'; string start buffer lexbuf }
  | "\\t" { Buffer.add_char buffer '\t'; string start buffer lexbuf }
  | "\\b" { Buffer.add_char buffer '\b'; string start buffer lexbuf }
  | "\\f" { Buffer.add_char buffer '\012'; string start buffer lexbuf }
  | '\\' newline {
      let loc = Location.of_lexbuf lexbuf in
      Lexing.new_line lexbuf;
      error loc "a string cannot contain a line continuation"
    }
  | '\\' (_ as c) { error_here lexbuf (Printf.sprintf "unknown string escape \\%c" c) }
  | newline {
      Lexing.new_line lexbuf;
      error (Location.make start (Lexing.lexeme_end_p lexbuf))
        "a string cannot contain an unescaped newline"
    }
  | [^ '"' '\\' '\000'-'\031']+ as contents
      { Buffer.add_string buffer contents; string start buffer lexbuf }
  | eof | '\\' eof
      { error (Location.make start (Lexing.lexeme_end_p lexbuf)) "unterminated string" }
  | _ { error_here lexbuf "a string cannot contain an unescaped control character" }

and comment start depth = parse
  | "/*" { comment start (depth + 1) lexbuf }
  | "*/" { if depth > 1 then comment start (depth - 1) lexbuf }
  | newline { Lexing.new_line lexbuf; comment start depth lexbuf }
  | eof { error (Location.make start (Lexing.lexeme_end_p lexbuf)) "unterminated block comment" }
  | _ { comment start depth lexbuf }
