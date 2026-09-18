type t = {
  start : Lexing.position;
  stop : Lexing.position;
}

type 'a located = {
  value : 'a;
  loc : t;
}

let make start stop = { start; stop }
let located start stop value = { value; loc = make start stop }
let of_lexbuf lexbuf = make (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf)
let column position = position.Lexing.pos_cnum - position.Lexing.pos_bol + 1

let pp formatter { start; stop } =
  let filename = if start.pos_fname = "" then "<input>" else start.pos_fname in
  if start.pos_lnum = stop.pos_lnum then
    Format.fprintf formatter "%s:%d:%d-%d" filename start.pos_lnum
      (column start) (column stop)
  else
    Format.fprintf formatter "%s:%d:%d-%d:%d" filename start.pos_lnum
      (column start) stop.pos_lnum (column stop)
