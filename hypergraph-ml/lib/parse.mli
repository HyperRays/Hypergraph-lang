(** Syntax-only entry points. Locations use one-based lines and byte columns,
    with an exclusive end position. Files and channels are read as bytes. *)
val program : Lexing.lexbuf -> (Ast.program, Diagnostic.t) result
val expression : Lexing.lexbuf -> (Ast.expr, Diagnostic.t) result
val type_expression : Lexing.lexbuf -> (Ast.typ, Diagnostic.t) result

val string : ?filename:string -> string -> (Ast.program, Diagnostic.t) result
val channel : ?filename:string -> in_channel -> (Ast.program, Diagnostic.t) result

(** Closes the file on both success and failure. I/O errors raise [Sys_error]. *)
val file : string -> (Ast.program, Diagnostic.t) result
