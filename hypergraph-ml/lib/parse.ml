let preview text =
  if String.length text > 40 then String.sub text 0 40 ^ "..." else text

let describe_token = function
  | Parser.EOF -> "end of input"
  | Parser.IDENT name -> Printf.sprintf "identifier %S" (preview name)
  | Parser.INT value -> Printf.sprintf "integer %S" (preview value)
  | Parser.DECIMAL value -> Printf.sprintf "decimal %S" (preview value)
  | Parser.STRING value -> Printf.sprintf "string %S" (preview value)
  | STRUCT -> "'struct'" | ENUM -> "'enum'" | ALIAS -> "'alias'"
  | LET -> "'let'" | MUT -> "'mut'"
  | LBRACE -> "'{'" | RBRACE -> "'}'" | LBRACKET -> "'['" | RBRACKET -> "']'"
  | LPAREN -> "'('" | RPAREN -> "')'" | LT -> "'<'" | GT -> "'>'"
  | COLON -> "':'" | COMMA -> "','" | SEMICOLON -> "';'" | EQUAL -> "'='"
  | DCOLON -> "'::'" | PLUS -> "'+'" | BANG -> "'!'"
  | PIPE -> "'|'" | AMP -> "'&'" | MINUS -> "'-'"
  | PIPE_EQUAL -> "'|='" | AMP_EQUAL -> "'&='" | MINUS_EQUAL -> "'-='"
  | RIGHT_ARROW -> "'->'" | LEFT_ARROW -> "'<-'" | BOTH_ARROW -> "'<->'"
  | RIGHT_PAYLOAD -> "'-['" | LEFT_PAYLOAD -> "'<-['"

let run parser lexbuf =
  let last_token = ref Parser.EOF in
  let token lexbuf =
    let token = Lexer.token lexbuf in
    last_token := token;
    token
  in
  try Ok (parser token lexbuf) with
  | Lexer.Error diagnostic -> Error diagnostic
  | Parser.Error ->
      Error {
        Diagnostic.kind = Syntax;
        loc = Location.of_lexbuf lexbuf;
        message = "unexpected " ^ describe_token !last_token;
      }

let program lexbuf = run Parser.program lexbuf
let expression lexbuf = run Parser.expression lexbuf
let type_expression lexbuf = run Parser.type_expression lexbuf

let with_filename filename lexbuf =
  Lexing.set_filename lexbuf filename;
  lexbuf

let string ?(filename = "<string>") source =
  program (with_filename filename (Lexing.from_string source))

let channel ?(filename = "<stdin>") input =
  program (with_filename filename (Lexing.from_channel input))

let file filename =
  let input = open_in_bin filename in
  Fun.protect ~finally:(fun () -> close_in_noerr input)
    (fun () -> channel ~filename input)
