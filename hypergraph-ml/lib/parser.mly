(* Grammar.

   Menhir is LR(1), so the ordering discipline the PEG grammar documented is
   gone. 'a set, or an edge whose tail is that set' needs no rule about which
   alternative to try first: the parser reads the set and then shifts on the
   arrow if one is there. Ambiguities are conflicts at build time rather than
   comments asking the next reader to keep the alternatives in order.

   Two restrictions are left to validate.ml because stating them here makes
   the grammar ambiguous. A set operand and an edge side are set expressions,
   and 'op=' takes only a set or an edge, but '(x)' can reduce either way and
   no lookahead settles which. A mixed operator chain parses for a different
   reason, so the error can name the operators. *)

%{
open Ast

(* Every node records where it starts, so a diagnostic can point at the
   operand it means. *)
let loc_of (p : Lexing.position) : loc =
  { line = p.pos_lnum; column = p.pos_cnum - p.pos_bol + 1 }

let mk p it = { it; loc = loc_of p }

(* '&' '^' '/' chain, but only one kind per chain. The clashing operator's
   own position is what the reader needs, so each link carries it. *)
let chain p first rest =
  match rest with
  | [] -> first
  | (op, _, _) :: _ ->
      List.iter
        (fun (o, at, _) -> if o <> op then raise (Mixed_ops (op, o, at)))
        rest;
      mk p (Op (op, first :: List.map (fun (_, _, a) -> a) rest))

(* 'Edge(t, h)' and 'Edge(t, h, p)' are the constructor spelling of an arrow,
   but only when the sides are set expressions, since that is what the arrow
   form takes. 'Edge(5, {2})' is therefore a struct initialiser naming a struct
   called Edge, which the checker then rejects for its own reasons. Arity alone
   is not enough to tell the two apart. *)
let application p name targs args =
  mk p
    (match (name, targs, args) with
     | "Edge", None, [ t; h ] when set_shaped t && set_shaped h ->
         Edge (t, h, None)
     | "Edge", None, [ t; h; q ] when set_shaped t && set_shaped h ->
         Edge (t, h, Some q)
     | _ -> Init (name, targs, args))
%}

%token <int64>            INT
%token <float>            DEC
%token <string>           STRING
%token <string>           IDENT
%token <int option>       FRONCE
%token <Ast.setop>        OP OPEQ
%token LET STRUCT TYPE
%token LBRACE RBRACE LPAREN RPAREN LT GT
%token COMMA COLON EQUALS PLUS UNDERSCORE
%token ARROW_R ARROW_L ARROW_LR
%token ANN_L ANN_R BANN_L BANN_R
%token NEWLINE EOF

%start <Ast.program> program
%start <Ast.stmt> line

%%

(* A statement ends at a newline or at end of input, so two statements cannot
   share a line. Blank lines are free. *)
program: nls; xs = stmts; EOF { xs }

(* One statement and nothing else, for a REPL or anything else that reads a
   single line. A struct body may still span lines, since the grammar allows
   newlines there; what this refuses is a SECOND statement, which is the whole
   difference from 'program'. *)
line: nls; s = stmt; nls; EOF { s }

stmts:
  |                                  { [] }
  | s = stmt; r = after_stmt         { s :: r }

after_stmt:
  |                                  { [] }
  | nls_1; r = stmts                 { r }

nls:   list(NEWLINE)                 { () }
nls_1: nonempty_list(NEWLINE)        { () }

stmt:
  | LET; n = IDENT; t = option(annot); EQUALS; v = rhs
      { mk $startpos (SLet (n, t, v)) }
  | n = IDENT; op = OPEQ; v = rhs
      { mk $startpos (SExt (n, op, v)) }
  | STRUCT; n = IDENT; ps = loption(params); LBRACE; nls; fs = fields; RBRACE
      { mk $startpos (SStruct (n, ps, fs)) }
  | TYPE; n = IDENT; ps = loption(params); EQUALS; b = tsum
      { mk $startpos (SType (n, ps, b)) }

annot:  COLON; t = tsum                                  { t }
params: LT; ps = separated_nonempty_list(COMMA, IDENT); GT { ps }

(* A newline is free around a separating comma and before the closing brace,
   which is what lets a struct body span lines. It is not free inside a field. *)
fields:
  |                                                      { [] }
  | f = field; r = fields_tail                           { f :: r }

fields_tail:
  | nls                                                  { [] }
  | nls; COMMA; nls                                      { [] }
  | nls; COMMA; nls; f = field; r = fields_tail          { f :: r }

field: n = IDENT; COLON; t = tsum   { { fname = n; ftype = t } }

(* Types are a sum of applications of atoms, where application distributes
   over '+': F (A + B) = F A + F B. *)
tsum:  ts = separated_nonempty_list(PLUS, tapp)          { TSyn ts }
tapp:  xs = nonempty_list(tatom)                         { TApp xs }

tatom:
  | n = IDENT                                            { AName n }
  | n = IDENT; LT; args = separated_nonempty_list(COMMA, tsum); GT
                                                         { AArgs (n, args) }
  | LPAREN; t = tsum; RPAREN                             { make_group t }

(* Values. An edge's sides are set expressions, so an arrow following a set is
   a shift and nothing has to be tried twice. *)
rhs:
  | t = sexpr; ARROW_R; h = sexpr        { mk $startpos (Edge (t, h, None)) }
  | h = sexpr; ARROW_L; t = sexpr        { mk $startpos (Edge (t, h, None)) }
  | a = sexpr; ARROW_LR; b = sexpr       { mk $startpos (UEdge (a, b, None)) }
  | t = sexpr; ANN_L;  p = rhs; ANN_R;  h = sexpr
      { mk $startpos (Edge (t, h, Some p)) }
  | h = sexpr; BANN_L; p = rhs; BANN_R; t = sexpr
      { mk $startpos (Edge (t, h, Some p)) }
  | a = sexpr; BANN_L; p = rhs; ANN_R;  b = sexpr
      { mk $startpos (UEdge (a, b, Some p)) }
  | v = value                                            { v }

value:
  | n = INT                                              { mk $startpos (Int n) }
  | d = DEC                                              { mk $startpos (Dec d) }
  | s = STRING                                           { mk $startpos (Str s) }
  | f = FRONCE                                           { mk $startpos (Fronce f) }
  | n = IDENT; ts = option(inst); LPAREN; args = args; RPAREN
                                                { application $startpos n ts args }
  | s = sexpr                                            { s }

inst: LT; xs = separated_nonempty_list(COMMA, iarg); GT  { xs }
iarg:
  | t = tsum                                             { Some t }
  | UNDERSCORE                                           { None }

args:
  |                                                      { [] }
  | v = rhs                                              { [v] }
  | v = rhs; COMMA; vs = args                            { v :: vs }

sexpr: a = satom; r = list(chained)                      { chain $startpos a r }
chained: op = OP; a = satom                     { (op, loc_of $startpos, a) }

satom:
  | LBRACE; nls; es = elems; RBRACE              { mk $startpos (make_set es) }
  | n = IDENT                                    { mk $startpos (Ref n) }
  | LPAREN; v = rhs; RPAREN                      { v }

(* Same rule as struct fields: newlines around the comma, not within an
   element, so '{a\n & b}' is not one set spread over two lines. *)
elems:
  |                                                      { [] }
  | v = rhs; r = elems_tail                              { v :: r }

elems_tail:
  | nls                                                  { [] }
  | nls; COMMA; nls                                      { [] }
  | nls; COMMA; nls; v = rhs; r = elems_tail             { v :: r }
