(* Type-syntax interpretation.

   The parser delivers pure shape. 'Set<Int + String>' arrives as an atom named
   Set applied to a sum of two atoms, with no opinion about whether Set is a
   set, Int a scalar, or mut a type at all. Every judgment about the WORDS is
   made here.

   An annotation becomes (mutness, type) plus whatever went wrong. Context
   matters in one respect: 'mut' is binding-position syntax and may not appear
   under a constructor. *)

open Ast
open Types

module SMap = Map.Make (String)

type ctx = Binding | Element

type env = {
  vars : (bool * ty) SMap.t;
  (* params and field types, interpreted once at the definition with the
     params rigid; instantiation substitutes into these *)
  structs : (string list * (string * ty) list) SMap.t;
  aliases : (string list * tsyn) SMap.t;
  rigids : string list;  (* parameters in scope while a definition is checked *)
  (* Rejected definitions stay as poisoned names, so a later use can point at
     the bad definition rather than pretend the struct was never mentioned. *)
  invalid_structs : string list;
}

(* Exactly one spelling each, never redefinable and never usable as a type
   parameter. *)
let builtin_names =
  [ "Int"; "Decimal"; "String"; "Fronce"; "Edge"; "UndirectedEdge"; "Graph";
    "Set"; "mut" ]

(* 'Graph<T>' is an inbuilt alias for the payload-carrying graph type, defined
   through the same mechanism as a user 'type' statement. Bare 'Graph' stays
   primitive, since its meaning recurses through the nominal graph component
   and no transparent alias can express that. *)
let builtin_aliases =
  let tv = TSyn [ TApp [ AName "T" ] ] in
  SMap.singleton "Graph"
    ( [ "T" ],
      TSyn
        [ TApp
            [ AArgs
                ( "Set",
                  [ TSyn
                      [ TApp [ AArgs ("Edge", [ tv ]) ];
                        TApp [ AArgs ("UndirectedEdge", [ tv ]) ] ] ] ) ] ] )

let empty_env =
  { vars = SMap.empty; structs = SMap.empty; aliases = builtin_aliases;
    rigids = []; invalid_structs = [] }

(* Does a type mention graphs anywhere? Used for mut poisoning and for whether
   a struct value may be a set element. Recurses through struct fields, and
   through instantiation arguments directly: every parameter occurs in some
   field, since unused ones are rejected at the definition, so a
   graph-mentioning argument always reaches a field. *)
let rec mentions_graph env seen = function
  | TGraph -> true
  | TSet cs -> List.exists (mentions_graph env seen) cs
  | TStruct (s, args) ->
      (not (List.mem s seen))
      && (List.exists (List.exists (mentions_graph env (s :: seen))) args
         ||
         match SMap.find_opt s env.structs with
         | Some (_, fields) ->
             List.exists (fun (_, t) -> mentions_graph env (s :: seen) t) fields
         | None -> false)
  | _ -> false

(* -- alias syntax machinery ------------------------------------------------- *)

(* Simultaneous substitution of parameters into an alias body, purely
   syntactically. All parameters go at once, because substituting one at a time
   could capture a use-site name that happens to spell a later parameter. Each
   argument lands as a group, and a trivial single-atom argument stays bare. A
   parameter used as a constructor, 'P<...>', is not substituted: parameters
   are first-order and the definition-site check rejects it. *)
let subst_syn_all m syn =
  let arg_atom = function TSyn [ TApp [ a ] ] -> a | s -> AGroup s in
  let rec go_syn (TSyn apps) = TSyn (List.map go_app apps)
  and go_app (TApp atoms) = TApp (List.map go_atom atoms)
  and go_atom a =
    match a with
    | AName n -> ( match SMap.find_opt n m with Some s -> arg_atom s | None -> a)
    | AArgs (n, args) -> AArgs (n, List.map go_syn args)
    | AGroup s -> AGroup (go_syn s)
  in
  go_syn syn

(* 'mut' anywhere in an alias body, rejected at the definition. It is
   binding-position syntax and an alias must not smuggle it past that. *)
let rec syn_mentions_mut (TSyn apps) =
  List.exists (fun (TApp atoms) -> List.exists atom_mentions_mut atoms) apps

and atom_mentions_mut = function
  | AName n -> n = "mut"
  | AArgs (_, args) -> List.exists syn_mentions_mut args
  | AGroup s -> syn_mentions_mut s

(* Type syntax back in source spelling, for the typedef report line. *)
let rec pretty_syn (TSyn apps) = String.concat " + " (List.map pretty_app apps)

and pretty_app (TApp atoms) = String.concat " " (List.map pretty_atom atoms)

and pretty_atom = function
  | AName n -> n
  | AArgs (n, args) ->
      n ^ "<" ^ String.concat ", " (List.map pretty_syn args) ^ ">"
  | AGroup s -> "(" ^ pretty_syn s ^ ")"

(* -- merging a sum ---------------------------------------------------------- *)

(* A sum of set types describes one heterogeneous set, so the components union.
   Scalars cannot be summed at all. *)
let merge_summands ts =
  let is_set = function TSet _ -> true | _ -> false in
  match ts with
  | [ t ] -> ([], t)
  | _ when List.exists (fun t -> equal t TUnknown) ts -> ([], TUnknown)
  | _ when List.for_all is_set ts ->
      ([], canon (List.concat_map (function TSet cs -> cs | _ -> []) ts))
  | _ ->
      ( List.filter_map
          (fun t ->
            if is_set t then None
            else
              Some ("only set types can be summed; '" ^ pretty t ^ "' is not a set"))
          ts,
        TUnknown )

(* -- interpretation --------------------------------------------------------- *)

let word_of = function
  | AName n -> n
  | AArgs (n, _) -> n ^ "<...>"
  | AGroup _ -> "(...)"

let strip_mut = function
  | AName "mut" :: (_ :: _ as rest) -> (true, rest)
  | atoms -> (false, atoms)

let rec interp_apps env ctx (TSyn apps) =
  let results = List.map (go_app env ctx) apps in
  (List.concat_map fst results, List.concat_map snd results)

and go_app env ctx (TApp atoms) =
  let is_mut, rest = strip_mut atoms in
  let pos_err =
    if is_mut && ctx = Element then
      [ "'mut' cannot appear under a type constructor" ]
    else []
  in
  let marked = is_mut && ctx = Binding in
  match rest with
  | [] -> (pos_err @ [ "'mut' must be followed by a type" ], [ (marked, TUnknown) ])
  | [ AGroup s ] ->
      (* A group distributes: 'mut (A + B)' marks every component. *)
      let es, comps = interp_apps env ctx s in
      let dbl =
        if marked && List.exists fst comps then [ "duplicate 'mut'" ] else []
      in
      (pos_err @ es @ dbl, List.map (fun (m, t) -> (marked || m, t)) comps)
  | [ AName n ] when n <> "Graph" && SMap.mem n env.aliases ->
      alias_ref env ctx pos_err marked n (SMap.find n env.aliases) None
  | [ AArgs (n, args) ] when SMap.mem n env.aliases ->
      alias_ref env ctx pos_err marked n (SMap.find n env.aliases) (Some args)
  | [ atom ] ->
      let es, t = atom_ty env atom in
      (pos_err @ es, [ (marked, t) ])
  | more ->
      ( pos_err
        @ [ "types cannot be juxtaposed: '"
            ^ String.concat " " (List.map word_of more)
            ^ "' has no meaning" ],
        [ (marked, TUnknown) ] )

(* Expand an alias use: arity-check, substitute all arguments at once, then
   interpret the instantiated body. Definition-site checking proved the body,
   so anything surfacing here is caused by the arguments. The alias is dropped
   from the table it passes down as a pure backstop, since a body that resolved
   at its definition cannot reference itself. *)
and alias_ref env ctx pre marked n (ps, body) margs =
  let args = Option.value margs ~default:[] in
  if List.length ps <> List.length args then
    ( pre
      @ [ Printf.sprintf "type alias '%s' expects %d type argument(s), got %d" n
            (List.length ps) (List.length args) ],
      [ (marked, TUnknown) ] )
  else
    let subst =
      List.fold_left2 (fun m p a -> SMap.add p a m) SMap.empty ps args
    in
    let env' = { env with aliases = SMap.remove n env.aliases } in
    let es, comps = interp_apps env' ctx (subst_syn_all subst body) in
    (pre @ es, List.map (fun (m, t) -> (marked || m, t)) comps)

(* Exactly one case-sensitive name per type. What the checker prints is the
   only spelling it accepts. *)
and atom_ty env = function
  | AName "Int" -> ([], TInt)
  | AName "Decimal" -> ([], TDec)
  | AName "String" -> ([], TStr)
  | AName "Fronce" -> ([], TFronce)
  | AName "Edge" -> ([], TEdge None)
  | AName "UndirectedEdge" -> ([], TUndirectedEdge None)
  | AName "Graph" -> ([], TSet [ TEdge None; TUndirectedEdge None; TGraph ])
  | AName "Set" -> ([ "'Set' requires element parameters: Set<...>" ], TUnknown)
  | AName "mut" -> ([ "'mut' is not a type by itself" ], TUnknown)
  | AName w when List.mem w env.rigids -> ([], TParam w)
  | AName w when SMap.mem w env.structs ->
      let ps, _ = SMap.find w env.structs in
      if ps = [] then ([], TStruct (w, []))
      else
        ( [ Printf.sprintf "struct '%s' expects %d type argument(s), got 0" w
              (List.length ps) ],
          TUnknown )
  | AName w when List.mem w env.invalid_structs ->
      ([ "cannot use struct " ^ w ^ " because its definition was invalid" ], TUnknown)
  | AName w -> ([ "unknown type '" ^ w ^ "'" ], TUnknown)
  (* Distribute before embedding: 'embed' abstracts a graph-shaped element to
     the nominal Graph, and a summand only looks graph-shaped once it stands
     alone. 'Set<Edge>' is a graph, 'Set<Edge + Int>' is not, so embedding
     first would judge graph-ness of the merged sum instead. *)
  | AArgs ("Set", [ s ]) ->
      let es, comps = interp_apps env Element s in
      ( es,
        canon
          (List.map embed (List.concat_map (fun (_, t) -> distribute t) comps)) )
  (* Edge<T> and UndirectedEdge<T> carry one payload type, with set sums
     merging as usual. A payload must not mention graphs, because edge equality
     includes it and comparison never descends into a graph. A rigid parameter
     mentions nothing, so that obligation is discharged at each instantiation
     when the body is reinterpreted. *)
  | AArgs ((("Edge" | "UndirectedEdge") as w), [ s ]) ->
      let es, comps = interp_apps env Element s in
      let mes, t = merge_summands (List.map snd comps) in
      let poison =
        if mentions_graph env [] t || is_graph_set t then
          [ "edge payload type '" ^ pretty t
            ^ "' cannot mention graphs (graph identity is nominal)" ]
        else []
      in
      let mk = if w = "Edge" then fun a -> TEdge a else fun a -> TUndirectedEdge a in
      (es @ mes @ poison, mk (Some t))
  | AArgs ((("Set" | "Edge" | "UndirectedEdge") as w), args) ->
      ( [ Printf.sprintf "'%s' takes exactly one type argument, got %d" w
            (List.length args) ],
        TUnknown )
  | AArgs (w, _) when List.mem w env.rigids ->
      ( [ "type parameter '" ^ w
          ^ "' cannot take type arguments (parameters are first-order)" ],
        TUnknown )
  (* An instantiated generic struct in type position: interpret the arguments,
     substitute into the fields so argument-caused errors surface here, and
     keep the nominal identity. *)
  | AArgs (w, args) when SMap.mem w env.structs ->
      let ps, flds = SMap.find w env.structs in
      if List.length ps <> List.length args then
        ( [ Printf.sprintf "struct '%s' expects %d type argument(s), got %d" w
              (List.length ps) (List.length args) ],
          TUnknown )
      else
        let rs = List.map (interp_arg env) args in
        let aerrs = List.concat_map fst rs in
        let targs = List.map snd rs in
        let su = List.fold_left2 (fun m p a -> SMap.add p a m) SMap.empty ps targs in
        let ierrs = List.concat_map (fun (_, t) -> fst (inst_ty env su t)) flds in
        (aerrs @ ierrs, TStruct (w, targs))
  | AArgs (w, _) when List.mem w env.invalid_structs ->
      ([ "cannot use struct " ^ w ^ " because its definition was invalid" ], TUnknown)
  (* A name that resolves to nothing is unknown however it was written, so
     'Nonesuch<Int>' reports the same missing name that bare 'Nonesuch' does.
     "takes no type parameters" would assert the name exists, sending the
     reader after a definition that was never there. *)
  | AArgs (w, _) when List.mem w builtin_names ->
      ([ "type '" ^ w ^ "' takes no type parameters" ], TUnknown)
  | AArgs (w, _) -> ([ "unknown type '" ^ w ^ "'" ], TUnknown)
  | AGroup _ -> ([ "misplaced type group" ], TUnknown) (* go_app handles groups *)

(* One type argument: a component sum, canonicalised but left as a list. *)
and interp_arg env s =
  let es, comps = interp_apps env Element s in
  (es, arg_canon (List.map snd comps))

(* Substitute an instantiation into a rigid field type, positionally. Among Set
   components a parameter splices its sum, each component embedding as usual.
   In payload or direct position the sum must merge to one type, so a scalar
   sum there is an argument-caused error. Poison obligations are re-checked
   here, since the definition proved the body only for rigid parameters. *)
and inst_ty env su t =
  let rec go = function
    | TSet cs ->
        let piece c =
          match c with
          | TParam p when SMap.mem p su -> ([], List.map embed (SMap.find p su))
          | c ->
              let es, c' = go c in
              (es, [ embed c' ])
        in
        let results = List.map piece cs in
        (List.concat_map fst results, canon (List.concat_map snd results))
    | TEdge ann -> edge (fun a -> TEdge a) ann
    | TUndirectedEdge ann -> edge (fun a -> TUndirectedEdge a) ann
    | TStruct (n, args) ->
        let sub1 arg =
          let piece c =
            match c with
            | TParam p when SMap.mem p su -> ([], SMap.find p su)
            | c ->
                let es, c' = go c in
                (es, [ c' ])
          in
          let results = List.map piece arg in
          (List.concat_map fst results, arg_canon (List.concat_map snd results))
        in
        let results = List.map sub1 args in
        (List.concat_map fst results, TStruct (n, List.map snd results))
    | TParam p when SMap.mem p su -> merge_summands (SMap.find p su)
    | t -> ([], t)
  and edge mk ann =
    match ann with
    | None -> ([], mk None)
    | Some t ->
        let es, t' =
          match t with
          | TParam p when SMap.mem p su -> merge_summands (SMap.find p su)
          | _ -> go t
        in
        let poison =
          if mentions_graph env [] t' || is_graph_set t' then
            [ "edge payload type '" ^ pretty t'
              ^ "' cannot mention graphs (graph identity is nominal)" ]
          else []
        in
        (es @ poison, mk (Some t'))
  in
  go t

(* -- a binding annotation --------------------------------------------------- *)

(* Merge the sum into one type. 'mut' must be uniform across the summands, so
   write 'mut (A + B)', and it passes the poisoning judgment component-wise. *)
let interp_binding env syn =
  let errs, comps = interp_apps env Binding syn in
  let muts = List.map fst comps and tys = List.map snd comps in
  let is_mut = List.exists Fun.id muts in
  let mix_err =
    if is_mut && not (List.for_all Fun.id muts) && List.length comps > 1 then
      [ "'mut' applies to only part of the sum — write 'mut (...)' around the \
         whole type" ]
    else []
  in
  (* 'mut Graph' sugar: a mutable graph is the flat graph type, because a
     mutable collection of graphs is ill-formed. *)
  let full_graph = TSet [ TEdge None; TUndirectedEdge None; TGraph ] in
  let sugared =
    List.map
      (fun t ->
        if is_mut && equal t full_graph then TSet [ TEdge None; TUndirectedEdge None ]
        else t)
      tys
  in
  let merge_errs, ty = merge_summands sugared in
  let poison =
    if is_mut then
      match ty with
      | TSet cs ->
          List.filter_map
            (fun c ->
              if mentions_graph env [] c then
                Some
                  ("mut " ^ pretty ty ^ " is ill-formed: component '" ^ pretty c
                 ^ "' contains graphs (graph identity is nominal; mutable \
                    collections of graphs are not allowed)")
              else None)
            cs
      | _ -> []
    else []
  in
  (errs @ mix_err @ merge_errs @ poison, is_mut, ty)
