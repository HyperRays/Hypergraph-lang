(* A small JSON writer.

   All that survives of the scaffolding that emitted the AST in the Rust
   parser's shape for cross-checking. The incidence matrices are still offered
   as JSON, for a consumer that wants the numbers rather than the picture, so
   the writer itself stays. *)

let buf_add_escaped b s =
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\t' -> Buffer.add_string b "\\t"
      | '\r' -> Buffer.add_string b "\\r"
      | '\b' -> Buffer.add_string b "\\b"
      | '\012' -> Buffer.add_string b "\\f"
      | c when Char.code c < 0x20 ->
          Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s

type t =
  | Null
  | Bool of bool
  | Num of string           (* already rendered, so int64 and float agree *)
  | Str of string
  | List of t list
  | Obj of (string * t) list

let rec write b = function
  | Null -> Buffer.add_string b "null"
  | Bool v -> Buffer.add_string b (if v then "true" else "false")
  | Num s -> Buffer.add_string b s
  | Str s -> Buffer.add_char b '"'; buf_add_escaped b s; Buffer.add_char b '"'
  | List xs ->
      Buffer.add_char b '[';
      List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; write b x) xs;
      Buffer.add_char b ']'
  | Obj kvs ->
      let kvs = List.sort (fun (a, _) (c, _) -> compare a c) kvs in
      Buffer.add_char b '{';
      List.iteri
        (fun i (k, v) ->
          if i > 0 then Buffer.add_char b ',';
          Buffer.add_char b '"'; buf_add_escaped b k;
          Buffer.add_string b "\":"; write b v)
        kvs;
      Buffer.add_char b '}'

let to_string j =
  let b = Buffer.create 256 in
  write b j;
  Buffer.contents b
