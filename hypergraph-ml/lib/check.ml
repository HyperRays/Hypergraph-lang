(* The checker: inference over values, struct instantiation, and the judgment
   each statement earns.

   A statement is checked against an environment and returns its errors and the
   environment the next statement sees. Nothing here reads syntax: 'interp' has
   already turned every written type into a type. *)

open Ast
open Types
open Interp

(* Haskell's list operations on types, which need the structural equality
   'equal' rather than OCaml's polymorphic one. *)
let nub xs =
  List.rev
    (List.fold_left
       (fun acc x -> if List.exists (equal x) acc then acc else x :: acc)
       [] xs)

let intersect xs ys = List.filter (fun x -> List.exists (equal x) ys) xs

(* Haskell's zipWith stops at the shorter list. List.map2 raises instead, and
   guarding by length and skipping is not the same thing: a struct applied to
   too few arguments still has its common prefix checked, so skipping loses a
   real field-type error. *)
let rec zip_with f a b =
  match (a, b) with x :: xs, y :: ys -> f x y :: zip_with f xs ys | _ -> []

(* Removes the FIRST occurrence of each y, as Haskell's (\\) does. *)
let difference xs ys =
  List.fold_left
    (fun acc y ->
      let rec drop = function
        | [] -> []
        | x :: rest -> if equal x y then rest else x :: drop rest
      in
      drop acc)
    xs ys

let counts xs =
  List.sort_uniq compare xs
  |> List.map (fun x -> (x, List.length (List.filter (( = ) x) xs)))

let param_list = function
  | [] -> ""
  | ps -> "<" ^ String.concat ", " ps ^ ">"

(* Shared by every parameter-binding definition, type and struct alike. *)
let param_checks owner params =
  let dups = List.filter_map (fun (p, n) -> if n > 1 then Some p else None)
      (counts params) in
  (if dups = [] then []
   else [ "duplicate type parameter(s) in " ^ owner ^ ": " ^ String.concat " " dups ])
  @ List.filter_map
      (fun p ->
        if List.mem p builtin_names then
          Some ("type parameter '" ^ p ^ "' shadows the built-in type '" ^ p ^ "'")
        else None)
      params

(* -- parameters in a type --------------------------------------------------- *)

let rec occurs_param p = function
  | TParam q -> p = q
  | TSet cs -> List.exists (occurs_param p) cs
  | TEdge (Some t) | TUndirectedEdge (Some t) -> occurs_param p t
  | TStruct (_, args) -> List.exists (List.exists (occurs_param p)) args
  | _ -> false

let rec has_param = function
  | TParam _ -> true
  | TSet cs -> List.exists has_param cs
  | TEdge (Some t) | TUndirectedEdge (Some t) -> has_param t
  | TStruct (_, args) -> List.exists (List.exists has_param) args
  | _ -> false

(* -- inference evidence ----------------------------------------------------- *)

(* Match a rigid field pattern against a ground argument type. Tolerant by
   design, so a shape mismatch yields no evidence and acceptance is decided
   afterwards by the ordinary sub check on the instantiated field. The empty
   set type is the unit of evidence, sitting below every set type, so it pins
   nothing.

   Routed through arg_canon so inference and annotation build the same
   argument: a value's type is always already merged, since '{1, "one"}' is one
   Set<Int> + Set<String>, so without distributing here it could never match an
   argument written in the distributed spelling. *)
let rec solve pat ground =
  match (pat, ground) with
  | TParam p, g ->
      if equal g (TSet []) || equal g TUnknown then [] else [ (p, arg_canon [ g ]) ]
  | TSet cs, TSet gs ->
      let is_bare_param = function TParam _ -> true | _ -> false in
      let bare, rest = List.partition is_bare_param cs in
      let concrete = List.filter (fun c -> not (has_param c)) rest in
      let nested = List.filter has_param rest in
      let remainder = arg_canon (difference gs concrete) in
      let nested_ev =
        List.concat_map (fun p -> List.concat_map (fun g -> solve p g) gs) nested
      in
      nested_ev
      @ (match bare with
        | [ TParam p ] when remainder <> [] -> [ (p, remainder) ]
        | _ -> [])
  | TEdge (Some p), TEdge (Some g) -> solve p g
  | TUndirectedEdge (Some p), TUndirectedEdge (Some g) -> solve p g
  | TStruct (n, pargs), TStruct (n', gargs) when n = n' ->
      let solve_arg pat g =
        match pat with
        | [ TParam p ] when g <> [] && not (List.equal equal g [ TSet [] ]) ->
            [ (p, g) ]
        | _ -> List.concat_map (fun pp -> List.concat_map (solve pp) g) pat
      in
      List.concat (List.map2 solve_arg pargs gargs)
  | _ -> []

(* -- the minting discipline ------------------------------------------------- *)

(* A minted token can only introduce a new value and never match an existing
   one, since it is guaranteed unequal to everything that exists. Positions
   whose whole purpose is matching reject it. *)
let rec mints_fronce (n : node) =
  match n.it with
  | Fronce None -> true
  | Set ns | Op (_, ns) | Init (_, _, ns) -> List.exists mints_fronce ns
  | Edge (a, b, ann) | UEdge (a, b, ann) ->
      List.exists mints_fronce (a :: b :: Option.to_list ann)
  | _ -> false

let mint_match_err ctx =
  [ ctx ^ " mints a token with '#', which can never match an existing value — \
           pin it (#N) or bind the value to a name first" ]

(* -- inference -------------------------------------------------------------- *)

(* A name not yet bound, for suggestions: the base with the first free numeric
   suffix, since bindings are single-assignment and the base itself is taken. *)
let fresh_name env base =
  let rec go i =
    let n = base ^ string_of_int i in
    if SMap.mem n env.vars then go (i + 1) else n
  in
  go 1

(* Vertex sets: edge-valued components are not vertices, though graph names
   are. *)
let side_errs lbl = function
  | TUnknown -> []
  | TUndirectedEdge _ ->
      [ lbl ^ " of an edge must be a vertex set, but contains edges" ]
  | TSet cs ->
      let is_bare_edge = function
        | TEdge _ | TUndirectedEdge _ -> true
        | _ -> false
      in
      if List.exists is_bare_edge cs then
        [ lbl ^ " of an edge must be a vertex set, but contains edges" ]
      else []
  | other ->
      [ lbl ^ " of an edge: found type " ^ pretty other
        ^ ", needed a set of vertices" ]

let rec infer env (n : node) =
  match n.it with
  | Int _ -> ([], TInt)
  | Dec _ -> ([], TDec)
  | Str _ -> ([], TStr)
  | Fronce _ -> ([], TFronce)
  | Ref name -> (
      match SMap.find_opt name env.vars with
      | Some (_, t) -> ([], t) (* reading a binding decays mut *)
      | None -> ([ "undefined variable " ^ name ], TUnknown))
  | Set elems ->
      let results = List.map (infer_elem env) elems in
      (List.concat_map fst results, canon (List.map snd results))
  | Op (op, operands) -> infer_op env op operands
  | Edge (t, h, ann) ->
      let te, tt = infer env t in
      let he, ht = infer env h in
      let ae, ann_ty = infer_ann env ann in
      ( te @ he @ ae @ side_errs "tail" tt @ side_errs "head" ht,
        TEdge ann_ty )
  | UEdge (a, b, ann) ->
      let ae, at = infer env a in
      let be, bt = infer env b in
      let ne, ann_ty = infer_ann env ann in
      ( ae @ be @ ne @ side_errs "side" at @ side_errs "side" bt,
        TUndirectedEdge ann_ty )
  | Init (s, targs, args) -> infer_init env s targs args

and infer_op env op operands =
  let results = List.map (infer env) operands in
  let errs = List.concat_map fst results and tys = List.map snd results in
  (* subsumption: a uedge IS a two-edge set, payload preserved *)
  let as_set = function
    | TSet cs -> Some cs
    | TUndirectedEdge ann -> Some [ TEdge ann ]
    | TUnknown -> Some []
    | _ -> None
  in
  let sym = op_symbol op in
  (* '^' matches in every operand; '/' matches in the subtrahends. *)
  let match_pos =
    match op with
    | Inter -> operands
    | Diff -> ( match operands with [] -> [] | _ :: rest -> rest)
    | Union -> []
  in
  let mint_errs =
    if List.exists mints_fronce match_pos then
      mint_match_err ("operand of '" ^ sym ^ "'")
    else []
  in
  let op_errs =
    mint_errs
    @ List.filter_map
        (fun t ->
          if as_set t = None then
            Some
              ("operand of '" ^ sym ^ "': found type " ^ pretty t
             ^ ", needed a set type")
          else None)
        tys
  in
  let compss = List.filter_map as_set tys in
  let comps =
    match (compss, op) with
    | [], _ -> []
    | c :: cs, Union -> List.fold_left (fun a b -> nub (a @ b)) c cs
    | c :: cs, Inter -> List.fold_left intersect c cs
    | c :: _, Diff -> c (* the left operand's components *)
  in
  (errs @ op_errs, canon comps)

(* The payload of an edge literal: any value type except graphs, since edge
   equality includes the payload and comparison never descends into a graph. *)
and infer_ann env = function
  | None -> ([], None)
  | Some n ->
      let es, t = infer env n in
      let poison =
        if mentions_graph env [] t || is_graph_set t then
          [ "an edge payload cannot contain graphs (found type " ^ pretty t ^ ")" ]
        else []
      in
      (es @ poison, Some t)

(* One set element: its component type, plus the nominal discipline. A
   graph-typed element must be a name bound non-mut, since identity is the name
   and the binding freezes the value. Struct values reaching into graphs would
   need deep comparison, so they are not elements either. *)
and infer_elem env (node : node) =
  let errs, t = infer env node in
  let checks =
    if is_graph_set t then
      match node.it with
      | Ref n -> (
          match SMap.find_opt n env.vars with
          | Some (true, _) ->
              [ "mut Graph " ^ n ^ " cannot be a set element; snapshot it \
                 first: let " ^ fresh_name env n ^ ": Graph = " ^ n ]
          | _ -> [])
      | _ ->
          [ "an anonymous graph value cannot be a set element; bind it to a \
             name with let first" ]
    else
      match t with
      | TStruct _ when mentions_graph env [] t ->
          [ "a struct value containing graphs cannot be a set element" ]
      | _ -> []
  in
  (errs @ checks, embed t)

(* Struct init: solve the instantiation, then verify. Explicit arguments and
   '_' holes come first, and every hole is solved from unification evidence,
   bottom-up only, the same as an unannotated let. With the solution complete,
   fields instantiate and the ordinary ground sub check runs. Solving never
   consults subtyping. *)
and infer_init env s targs args =
  let results = List.map (infer env) args in
  let errs = List.concat_map fst results in
  let arg_tys = List.map snd results in
  match SMap.find_opt s env.structs with
  | None ->
      if List.mem s env.invalid_structs then
        ( errs
          @ [ "cannot use struct " ^ s ^ " because its definition was invalid" ],
          TUnknown )
      else (errs @ [ "unknown struct " ^ s ], TUnknown)
  | Some (params, fields) ->
      let arity =
        if List.length fields <> List.length args then
          [ Printf.sprintf "struct %s expects %d argument(s), got %d" s
              (List.length fields) (List.length args) ]
        else []
      in
      let texpl_errs, expl =
        match targs with
        | None -> ([], List.map (fun _ -> None) params)
        | Some ts ->
            if List.length ts <> List.length params then
              ( [ Printf.sprintf "struct %s expects %d type argument(s), got %d"
                    s (List.length params) (List.length ts) ],
                List.map (fun _ -> None) params )
            else
              let one = function
                | None -> ([], None) (* '_' hole *)
                | Some syn ->
                    let es, a = interp_arg env syn in
                    (es, Some a)
              in
              let rs = List.map one ts in
              (List.concat_map fst rs, List.map snd rs)
      in
      let evidence =
        List.concat (zip_with (fun (_, ft) at -> solve ft at) fields arg_tys)
      in
      let solve_one (p, given) =
        match given with
        | Some a -> ([], (p, a))
        | None -> (
            let found =
              nub_args (List.filter_map (fun (q, a) -> if q = p then Some a else None)
                          evidence)
            in
            match found with
            | [ a ] -> ([], (p, a))
            | [] ->
                ( [ "cannot infer type parameter '" ^ p ^ "' of struct " ^ s
                    ^ " — write " ^ s ^ "<...>(...)" ],
                  (p, [ TUnknown ]) )
            | as_ ->
                ( [ "conflicting types for parameter '" ^ p ^ "' of struct " ^ s
                    ^ ": " ^ String.concat " vs " (List.map pretty_arg as_) ],
                  (p, [ TUnknown ]) ))
      in
      let solved = List.map solve_one (List.combine params expl) in
      let solve_errs = List.concat_map fst solved in
      let su =
        List.fold_left (fun m (p, a) -> SMap.add p a m) SMap.empty
          (List.map snd solved)
      in
      let instd = List.map (fun (fn, ft) -> (fn, inst_ty env su ft)) fields in
      let inst_errs = List.concat_map (fun (_, (es, _)) -> es) instd in
      let check_arg (fn, ft) at =
        if sub at ft then []
        else
          [ "field " ^ fn ^ " of " ^ s ^ ": found type " ^ pretty at
            ^ ", needed type " ^ pretty ft ]
      in
      let field_errs =
        List.concat
          (zip_with (fun (fn, (_, t)) at -> check_arg (fn, t) at) instd arg_tys)
      in
      ( errs @ arity @ texpl_errs @ solve_errs @ inst_errs @ field_errs,
        TStruct (s, List.map (fun (_, (_, a)) -> a) solved) )

and nub_args xs =
  List.rev
    (List.fold_left
       (fun acc x ->
         if List.exists (fun y -> List.equal equal x y) acc then acc else x :: acc)
       [] xs)

(* -- op= dispatch ----------------------------------------------------------- *)

let dispatch name op lhs rhs =
  let ops = op_symbol op ^ "=" in
  match (lhs, rhs) with
  | TUnknown, _ | _, TUnknown -> []
  | TSet cs, _ -> (
      let invariant shown r =
        if sub r (TSet cs) then []
        else
          [ "'" ^ ops ^ "' on " ^ name ^ ": found type " ^ pretty shown
            ^ ", needed type " ^ pretty (TSet cs)
            ^ " (op= is invariant — it cannot widen a binding's type)" ]
      in
      match rhs with
      (* A bare edge on the RHS: suggest '{...}'-wrapping only when the braced
         set would fit. Otherwise the honest problem is the binding's
         components, and the hint would walk the user into invariance. *)
      | TEdge ann ->
          if sub (TSet [ rhs ]) (TSet cs) then
            [ "'" ^ ops ^ "' on " ^ name ^ ": found type " ^ pretty rhs
              ^ ", needed type " ^ pretty (TSet cs) ^ " — write a single edge as {...}" ]
          else
            [ "'" ^ ops ^ "' on " ^ name ^ ": found type " ^ pretty rhs
              ^ ", needed type " ^ pretty (TSet cs)
              ^ " — wrapping it as {...} would not help (op= is invariant); \
                 declare " ^ name ^ " with Set<" ^ pretty rhs
              ^ "> among its components"
              ^ (match ann with Some _ -> ", or drop the payload" | None -> "") ]
      | TUndirectedEdge ann -> invariant rhs (TSet [ TEdge ann ])
      | TSet _ -> invariant rhs rhs
      | other ->
          [ "'" ^ ops ^ "' on " ^ name ^ ": found type " ^ pretty other
            ^ ", needed type " ^ pretty (TSet cs) ])
  (* Side surgery: the RHS must be a plain edge of the same orientation, since
     surgery edits sides and never payloads. *)
  | TEdge _, TEdge None -> []
  | TEdge _, TEdge (Some _) ->
      [ "'" ^ ops ^ "' on " ^ name ^ ": the RHS of side surgery must be a plain \
         Edge, found " ^ pretty rhs ^ " (surgery never edits payloads)" ]
  | TEdge _, other ->
      [ "'" ^ ops ^ "' on " ^ name ^ ": found type " ^ pretty other
        ^ ", needed type Edge" ]
  | TUndirectedEdge _, TUndirectedEdge None -> []
  | TUndirectedEdge _, TUndirectedEdge (Some _) ->
      [ "'" ^ ops ^ "' on " ^ name ^ ": the RHS of side surgery must be a plain \
         UndirectedEdge, found " ^ pretty rhs ^ " (surgery never edits payloads)" ]
  | TUndirectedEdge _, other ->
      [ "'" ^ ops ^ "' on " ^ name ^ ": found type " ^ pretty other
        ^ ", needed type UndirectedEdge" ]
  | other, _ ->
      [ "'" ^ ops ^ "' cannot apply to " ^ name ^ " of type " ^ pretty other ]

(* -- statements ------------------------------------------------------------- *)

let check_stmt env (stmt : stmt) =
  match stmt.it with
  (* A struct definition is checked here with its parameters rigid, exactly
     like an alias body. A parameter no field mentions can never be inferred
     nor affect a value, so it is rejected: the phantom idiom is deliberately
     unsupported, because erasure would defeat it. *)
  | SStruct (n, params, fields) ->
      let env_r = { env with rigids = params } in
      let interp_field (f : field) =
        let es, is_mut, ty = interp_binding env_r f.ftype in
        ( es @ (if is_mut then [ "'mut' is not allowed in struct fields" ] else []),
          (f.fname, ty) )
      in
      let results = List.map interp_field fields in
      let field_tys = List.map snd results in
      let ty_errs = List.concat_map fst results in
      let dups =
        List.filter_map (fun (f, c) -> if c > 1 then Some f else None)
          (counts (List.map fst field_tys))
      in
      let dup_err =
        if dups = [] then []
        else [ "duplicate field(s) in struct " ^ n ^ ": " ^ String.concat " " dups ]
      in
      let redef_err =
        if SMap.mem n env.structs then [ "struct " ^ n ^ " redefined" ] else []
      in
      let alias_err =
        if SMap.mem n env.aliases then
          [ "struct " ^ n ^ " collides with type alias " ^ n ]
        else []
      in
      let unused =
        List.filter_map
          (fun p ->
            if List.exists (fun (_, t) -> occurs_param p t) field_tys then None
            else
              Some ("type parameter '" ^ p ^ "' of struct " ^ n
                   ^ " is never used by a field"))
          params
      in
      let errs =
        ty_errs @ dup_err @ redef_err @ alias_err @ param_checks n params @ unused
      in
      let env' =
        if errs = [] then
          { env with
            structs = SMap.add n (params, field_tys) env.structs;
            invalid_structs = List.filter (( <> ) n) env.invalid_structs }
        else if SMap.mem n env.structs then
          (* Do not poison a valid earlier definition when this was merely a
             rejected redefinition. *)
          env
        else { env with invalid_structs = n :: env.invalid_structs }
      in
      (errs, env')
  (* A type alias is checked at its definition with parameters rigid. Unknown
     names, arity misuse and 'mut' in the body reject it atomically, so a use
     site can then only fail through its arguments. No merge judgment runs
     here, because whether a sum is usable is a question about position. *)
  | SType (n, params, body) ->
      let name_errs =
        if List.mem n builtin_names then
          [ "type '" ^ n ^ "' is built-in and cannot be redefined" ]
        else if SMap.mem n env.aliases then [ "type alias " ^ n ^ " redefined" ]
        else if SMap.mem n env.structs then [ "'" ^ n ^ "' is already a struct" ]
        else []
      in
      let mut_err =
        if syn_mentions_mut body then
          [ "'mut' cannot appear in a type alias — mut is binding-position syntax" ]
        else []
      in
      let body_errs =
        if mut_err = [] then
          fst (interp_apps { env with rigids = params } Element body)
        else mut_err
      in
      let errs = name_errs @ param_checks n params @ body_errs in
      if errs = [] then
        ([], { env with aliases = SMap.add n (params, body) env.aliases })
      else (errs, env)
  | SLet (n, _, v) when SMap.mem n env.vars ->
      (* Single-assignment: names are permanent identities. The value is still
         inferred for its own errors, and the old binding stays. *)
      let verrs, _ = infer env v in
      ( ( n ^ " is already defined — bindings are single-assignment (mutate a \
            mut binding with &= ^= /=, or choose a new name)" )
        :: verrs,
        env )
  | SLet (n, ann, v) ->
      let verrs, vt = infer env v in
      let aerrs, is_mut, at =
        match ann with
        | None -> ([], false, TUnknown)
        | Some syn -> interp_binding env syn
      in
      let ann_err =
        match ann with
        | Some _ when (not (equal at TUnknown)) && not (sub vt at) ->
            [ "declared " ^ n ^ ": " ^ pretty at ^ ", but found type " ^ pretty vt ]
        | _ -> []
      in
      let final = if equal at TUnknown then vt else at in
      ( verrs @ aerrs @ ann_err,
        { env with vars = SMap.add n (is_mut, final) env.vars } )
  | SExt (n, op, rhs) -> (
      let ierrs, rt = infer env rhs in
      let rerrs =
        (if (op = Inter || op = Diff) && mints_fronce rhs then
           mint_match_err ("the RHS of '" ^ op_symbol op ^ "='")
         else [])
        @ ierrs
      in
      match SMap.find_opt n env.vars with
      | None -> (("assignment to undefined variable " ^ n) :: rerrs, env)
      | Some (is_mut, t) ->
          let mut_err =
            if (not is_mut) && not (equal t TUnknown) then
              [ n ^ " is not mut — declare it 'let " ^ n ^ ": mut ...' to use "
                ^ op_symbol op ^ "=" ]
            else []
          in
          (* The binding's type is fixed at declaration: op= never retypes. *)
          (mut_err @ rerrs @ dispatch n op t rt, env))

(* -- the report ------------------------------------------------------------- *)

let var_report env n =
  Option.map
    (fun (is_mut, t) -> n ^ " : " ^ (if is_mut then "mut " else "") ^ pretty t)
    (SMap.find_opt n env.vars)

(* What a statement bound, with its declared or inferred type. *)
let binding_report env (stmt : stmt) =
  match stmt.it with
  | SLet (n, _, _) | SExt (n, _, _) -> var_report env n
  | SStruct (n, _, _) -> (
      match SMap.find_opt n env.structs with
      | Some (ps, []) -> Some ("struct " ^ n ^ param_list ps ^ " {}")
      | Some (ps, fields) ->
          Some
            ("struct " ^ n ^ param_list ps ^ " { "
            ^ String.concat ", "
                (List.map (fun (f, t) -> f ^ ": " ^ pretty t) fields)
            ^ " }")
      | None -> None)
  (* A rejected redefinition reports the surviving definition, mirroring how
     redefined lets report the old binding. *)
  | SType (n, _, _) -> (
      match SMap.find_opt n env.aliases with
      | Some (ps, body) ->
          Some ("type " ^ n ^ param_list ps ^ " = " ^ pretty_syn body)
      | None -> None)

(* What each statement declared, for the evaluator. A 'let' with an annotation
   that interpreted to something records (mut, type); everything else records
   nothing.

   The Rust evaluator re-derives this from the written syntax, in 55 lines that
   carry their own alias table and a cycle guard, because the checker's answer
   only ever crossed the boundary as prose. Here it is the checker's answer. *)
type declaration = (bool * ty) option

(* A diagnostic carries a CODE naming the rule, so prose can improve without
   breaking a consumer. Classification is deliberately conservative, and the
   rules needing AST context inspect the statement here rather than trying to
   recover intent from a rendered string. *)
type diagnostic = {
  code : string;
  message : string;
  statement : int;
  notes : string list;
  helps : string list;
}

let contains hay needle =
  let n = String.length needle and h = String.length hay in
  let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
  n = 0 || go 0

let starts_with hay p =
  String.length hay >= String.length p && String.sub hay 0 (String.length p) = p

(* An anonymous set of edges splices into its parent, so a Set<Graph>
   annotation over one is a mismatch worth explaining rather than merely
   reporting. *)
let anonymous_graph_mismatch (stmt : stmt) message =
  match stmt.it with
  | SLet (_, _, { it = Set elems; _ }) ->
      List.exists
        (fun (e : node) -> match e.it with Edge _ | UEdge _ -> true | _ -> false)
        elems
      && contains message "Set<Graph>"
      && (contains message "Set<Edge" || contains message "Set<UndirectedEdge>")
  | _ -> false

let anonymous_graph_help (stmt : stmt) =
  match stmt.it with
  | SLet (n, _, _) ->
      "bind the inner graph first, then use its name: let inner: Graph = ...;        let " ^ n ^ ": Set<Graph> = {inner}"
  | _ -> "bind the inner graph first, then use its name"

let diagnostic_meta stmt message =
  if anonymous_graph_mismatch stmt message then
    ( "T014",
      [ "anonymous sets of edges are flattened into their parent set" ],
      [ anonymous_graph_help stmt ] )
  else if contains message " is already defined" then ("T001", [], [])
  else if contains message "op= is invariant" then ("T021", [], [])
  else if starts_with message "cannot infer type parameter" then ("T031", [], [])
  else if contains message "because its definition was invalid" then
    ( "T032",
      [ "fix the earlier struct definition before using this constructor" ],
      [] )
  else if
    starts_with message "type parameter '"
    && contains message "is never used by a field"
  then ("T030", [], [])
  else if starts_with message "declared " then ("T010", [], [])
  else if starts_with message "unknown " then ("T040", [], [])
  else ("T000", [], [])

(* Where inside a statement a diagnostic points, for a consumer that wants to
   locate it without re-parsing. *)
let stmt_path (stmt : stmt) =
  match stmt.it with
  | SLet _ -> "/value"
  | SExt _ -> "/rhs"
  | SStruct _ -> "/fields"
  | SType _ -> "/body"

type checked = { number : int; errors : string list; binding : string option }

(* Everything a consumer downstream of checking needs. The evaluator reads
   'declarations' to know when a binding coerced; the facts emitter reads
   'structs' for the RESOLVED field types, so a field declared through a type
   alias is still known to be a Decimal. *)
type outcome = {
  report : string;
  errors : int;
  declarations : declaration list;
  structs : (string list * (string * ty) list) SMap.t;
  diagnostics : diagnostic list;
  judgments : (int * string) list;
}


let declaration_of env (stmt : stmt) : declaration =
  match stmt.it with
  | SLet (_, Some syn, _) ->
      let _, is_mut, ty = interp_binding env syn in
      if equal ty TUnknown then None else Some (is_mut, ty)
  | _ -> None

let check_program (program : program) =
  let rows, error_count, final, decls =
    List.fold_left
      (fun (out, n, env, ds) (i, stmt) ->
        (* The declaration is read in the environment the statement is checked
           in, since an alias defined earlier must already be in scope. *)
        let d = declaration_of env stmt in
        let errs, env' = check_stmt env stmt in
        ( out @ [ { number = i; errors = errs; binding = binding_report env' stmt } ],
          n + List.length errs,
          env',
          ds @ [ d ] ))
      ([], 0, empty_env, [])
      (List.mapi (fun i s -> (i + 1, s)) program)
  in
  let render row =
    List.map (fun e -> Printf.sprintf "stmt %d: error: %s" row.number e) row.errors
    @ (match row.binding with
      | Some r -> [ Printf.sprintf "stmt %d: %s" row.number r ]
      | None -> [])
  in
  let summary =
    if error_count = 0 then "typecheck: OK"
    else Printf.sprintf "typecheck: %d error(s)" error_count
  in
  let diagnostics =
    List.concat
      (List.map2
         (fun row (stmt : stmt) ->
           List.map
             (fun m ->
               let code, notes, helps = diagnostic_meta stmt m in
               { code; message = m; statement = row.number; notes; helps })
             row.errors)
         rows program)
  in
  let judgments =
    List.filter_map
      (fun row -> Option.map (fun b -> (row.number, b)) row.binding)
      rows
  in
  { report = String.concat "\n" (List.concat_map render rows @ [ summary ]) ^ "\n";
    errors = error_count;
    declarations = decls;
    structs = final.structs;
    diagnostics;
    judgments }
