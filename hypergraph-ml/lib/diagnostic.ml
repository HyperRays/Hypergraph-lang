type kind = Lexical | Syntax

type t = {
  kind : kind;
  loc : Location.t;
  message : string;
}

let pp formatter { kind; loc; message } =
  let label = match kind with Lexical -> "lexical" | Syntax -> "syntax" in
  Format.fprintf formatter "%a: %s error: %s" Location.pp loc label message

let to_string diagnostic = Format.asprintf "%a" pp diagnostic
