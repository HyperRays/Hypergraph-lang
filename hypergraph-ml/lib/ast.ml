(* The abstract syntax, as types.

   In the Rust and Haskell implementation this was a JSON contract described
   by 127 lines of comment in two files, each asking the reader to keep it in
   sync with the other by hand. Here the parser builds these constructors and
   the checker matches on them, so there is nothing to keep in sync. *)

type loc = { line : int; column : int }

(* Everything the parser builds carries where it was written, so a diagnostic
   can point at the operand it means rather than at the statement containing
   it. Types are not located yet: the checker reports them by statement and a
   coarse path, so nothing needs finer than that today. *)
type 'a located = { it : 'a; loc : loc }

let nowhere = { line = 0; column = 0 }
let at loc it = { it; loc }

type setop = Union | Inter | Diff

(* A value expression. Sets are unordered and duplicate-free by construction,
   but that is the evaluator's business; the parser records what was written.

   Edge and UEdge carry an optional payload, written 'a -[v]-> b'. UEdge keeps
   its sides in written order because orientation is part of its identity: as
   an element '{1} <-> {2}' and '{2} <-> {1}' are two values, while as an
   operand of a set op both dissolve to the same two directed halves. *)
type node = nodekind located

and nodekind =
  | Int of int64
  | Dec of float
  | Str of string
  | Ref of string
  | Fronce of int option          (* '#' mints, '#N' pins *)
  | Set of node list
  | Op of setop * node list
  | Edge of node * node * node option
  | UEdge of node * node * node option
  | Init of string * targ list option * node list

(* An explicit type argument at an instantiation. None is a '_' hole left to
   inference, so 'Pair<Int, _>(1, 2)' is [Some Int; None]. *)
and targ = tsyn option

(* Type SYNTAX, exactly as written. A sum of applications of atoms, where the
   application distributes over '+': F (A + B) = F A + F B. Whether a given sum
   is usable in a given position is a judgment, made in typecheck.ml, not here. *)
and tsyn = TSyn of tapp list
and tapp = TApp of tatom list                (* juxtaposition, e.g. 'mut Set<Int>' *)
and tatom =
  | AName of string                          (* Int, Graph, a struct name, 'mut' *)
  | AArgs of string * tsyn list              (* Set<Int>, Assoc<Int, String> *)
  | AGroup of tsyn                           (* '(...)', leaves no other trace *)

type field = { fname : string; ftype : tsyn }

type stmt = stmtkind located

and stmtkind =
  | SLet of string * tsyn option * node
  | SExt of string * setop * node            (* 'g &= ...', dispatch is semantic *)
  | SStruct of string * string list * field list
  | SType of string * string list * tsyn     (* 'type X<P> = T', transparent *)

type program = stmt list

let op_symbol = function Union -> "&" | Inter -> "^" | Diff -> "/"

(* Set-shaped as the grammar means it in 'set_atom': a literal set, a name
   that may refer to one, or a chain of them. '(...)' leaves no trace, so a
   parenthesised set expression is already one of these. *)
let set_shaped n =
  match n.it with Set _ | Ref _ | Op _ -> true | _ -> false

(* '(...)' around a type leaves no trace when it holds a single atom, so
   '(Ca)' and 'Ca' are the same written type. A group survives only when it
   carries structure the parentheses are needed for, a sum or a juxtaposition,
   as in '(A + B)' or '(mut Set<Int>)'. *)
let make_group (TSyn apps as t) =
  match apps with [ TApp [ atom ] ] -> atom | _ -> AGroup t

(* A written set of edges nested directly inside another set splices into it,
   so '{{a -> b, c -> d}}' holds two elements rather than one. A set of edges
   is a graph, and a graph written inline has no name to be identified by, so
   there is nothing for the extra layer to mean. A NAMED graph is a reference
   rather than a literal and never splices, which is what keeps '{g1, e}' at
   two elements.

   This is the one desugaring the parser performs, beyond '(...)' leaving no
   trace. *)
let is_edge_set n =
  match n.it with
  | Set (_ :: _ as elems) ->
      List.for_all
        (fun e -> match e.it with Edge _ | UEdge _ -> true | _ -> false)
        elems
  | _ -> false

let make_set elems =
  Set
    (List.concat_map
       (fun e -> match e.it with Set inner when is_edge_set e -> inner | _ -> [ e ])
       elems)

(* Raised by the parser when one chain mixes '&', '^' and '/'. The grammar
   accepts the chain so this can name the operators and point at the one that
   clashed, rather than describing which alternative failed. *)
exception Mixed_ops of setop * setop * loc
