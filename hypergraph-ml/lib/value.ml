(* Evaluation: a checked program becomes values.

   Types have erased by the time anything here runs, with one exception noted
   at 'run'. Every dispatch below is on a runtime constructor. *)

open Ast

type value =
  | VInt of int64
  | VDec of float
  | VStr of string
  | VFronce of fronce
  | VSet of elem list
  | VEdge of value * value * value option
  | VUEdge of value * value * value option
  | VStruct of string * value list

(* Two DISJOINT namespaces. The marker is provenance, not meaning: the only
   content a token carries is its index, and only a pinned index is the
   author's to choose. Keeping the spaces apart is what makes minting
   order-independent, since an auto index can never collide with a pinned one
   however the program is ordered. *)
and fronce = Auto of int | User of int

(* An element carries the NAME it was written as, when it was written as one.
   For graph-valued elements that name IS the identity; elsewhere it becomes
   the column label. *)
and elem = { label : string option; v : value }

(* A graph value: a non-empty set whose elements are all edge-shaped, where a
   nested set counts only if it is NAMED and itself graph-valued. The emptiness
   condition is what keeps '{}' from being a graph, so empty graphs compare
   structurally and are all equal. *)
let rec is_graph_val = function
  | VSet (_ :: _ as elems) ->
      List.for_all
        (fun e ->
          match e.v with
          | VEdge _ | VUEdge _ -> true
          | VSet _ -> e.label <> None && is_graph_val e.v
          | _ -> false)
        elems
  | _ -> false

(* -- identity --------------------------------------------------------------- *)

(* Structural equality that bottoms out at the graph boundary: graph-valued
   NAMED elements compare by name alone. An empty set is not graph-valued, so
   empty graphs miss this tier and compare structurally, where they are all
   equal whatever they were named. *)
let rec elems_eq a b =
  match (a.label, b.label) with
  | Some la, Some lb when is_graph_val a.v && is_graph_val b.v -> la = lb
  | _ -> vals_eq a.v b.v

(* Payloads are part of edge structure, so edges differing only in annotation
   are DIFFERENT edges. That is what makes parallel edges representable. *)
and anns_eq a b =
  match (a, b) with
  | None, None -> true
  | Some x, Some y -> vals_eq x y
  | _ -> false

and vals_eq a b =
  match (a, b) with
  | VInt x, VInt y -> x = y
  | VDec x, VDec y -> x = y
  | VStr x, VStr y -> x = y
  | VFronce x, VFronce y -> x = y
  (* Struct fields are POSITIONAL, so they zip: City("Zurich", 400000) means
     name-then-pop and the order is part of the value. *)
  | VStruct (n, xs), VStruct (m, ys) ->
      n = m && List.length xs = List.length ys && List.for_all2 vals_eq xs ys
  (* Sets are UNORDERED, so they must NOT zip: a list's order here is insertion
     order, an artifact of how the value was written. Length plus one-way
     containment is sound only because every set is duplicate-free by
     construction, at push_unique's every call site; without that, [a,a,b] and
     [a,b,b] would compare equal. *)
  | VSet xs, VSet ys ->
      List.length xs = List.length ys
      && List.for_all (fun x -> List.exists (elems_eq x) ys) xs
  | VEdge (t1, h1, a1), VEdge (t2, h2, a2) ->
      vals_eq t1 t2 && vals_eq h1 h2 && anns_eq a1 a2
  (* Sides compare POSITIONALLY, deliberately: orientation is part of an
     undirected edge's identity, so '{1} <-> {2}' and '{2} <-> {1}' are
     different values and a set holding both keeps both. Sameness across
     spellings is expressed in the one place it belongs, in as_elems: a uedge
     used as an OPERAND dissolves into its two directed halves, where
     orientation cannot survive. *)
  | VUEdge (a1, b1, n1), VUEdge (a2, b2, n2) ->
      vals_eq a1 a2 && vals_eq b1 b2 && anns_eq n1 n2
  | _ -> false

(* -- display ---------------------------------------------------------------- *)

(* Rust's Debug for str, which is what the display form has always been:
   quotes and backslash escaped, the usual control characters named, and
   anything else below space as '\u{..}'. Printable non-ASCII is left alone. *)
let quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\t' -> Buffer.add_string b "\\t"
      | '\r' -> Buffer.add_string b "\\r"
      | c when Char.code c < 0x20 || Char.code c = 0x7f ->
          Buffer.add_string b (Printf.sprintf "\\u{%x}" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

(* Shortest form that round-trips, matching how Rust renders a float. *)
let float_repr f =
  let rec shortest p =
    if p > 17 then Printf.sprintf "%.17g" f
    else
      let s = Printf.sprintf "%.*g" p f in
      if float_of_string s = f then s else shortest (p + 1)
  in
  shortest 1

let rec canon_elem e =
  match (e.label, is_graph_val e.v) with Some l, true -> l | _ -> canon e.v

and canon = function
  | VInt i -> Int64.to_string i
  (* Integral decimals keep their point: display must not conflate 100.0 with
     the integer 100. *)
  | VDec d when Float.is_integer d -> Printf.sprintf "%.1f" d
  | VDec d -> float_repr d
  | VStr s -> quote s
  (* '%' cannot occur in a source name, so a rendered token can never collide
     with a named graph when canonical text is used as a row key. *)
  | VFronce (Auto n) -> Printf.sprintf "%%a%d" n
  | VFronce (User n) -> Printf.sprintf "%%u%d" n
  | VStruct (name, args) ->
      name ^ "(" ^ String.concat ", " (List.map canon args) ^ ")"
  | VSet elems -> "{" ^ String.concat ", " (List.map canon_elem elems) ^ "}"
  | VEdge (t, h, None) -> "(" ^ canon t ^ " -> " ^ canon h ^ ")"
  | VEdge (t, h, Some v) ->
      "(" ^ canon t ^ " -[" ^ canon v ^ "]-> " ^ canon h ^ ")"
  | VUEdge (a, b, None) -> "(" ^ canon a ^ " <-> " ^ canon b ^ ")"
  | VUEdge (a, b, Some v) ->
      "(" ^ canon a ^ " <-[" ^ canon v ^ "]-> " ^ canon b ^ ")"

(* -- sets ------------------------------------------------------------------- *)

let push_unique elems e =
  if List.exists (fun x -> elems_eq x e) elems then elems else elems @ [ e ]

(* A value usable as a set of elements: sets themselves, and undirected edges
   through the UndirectedEdge <: Set<Edge> subsumption, where an annotated
   uedge dissolves into two annotated directed halves carrying the same
   payload.

   A self-loop's two halves ARE the same edge, so the pair goes in through
   push_unique. Set equality's one-way containment is sound only while every
   set is duplicate-free, and this is the one construction site that could
   otherwise hand back a duplicate. *)
let as_elems = function
  | VSet elems -> Some elems
  | VUEdge (a, b, ann) ->
      Some
        (List.fold_left
           (fun out (t, h) -> push_unique out { label = None; v = VEdge (t, h, ann) })
           [] [ (a, b); (b, a) ])
  | _ -> None

let apply_set_op op acc rhs =
  match op with
  | Union -> List.fold_left push_unique acc rhs
  | Inter -> List.filter (fun e -> List.exists (fun r -> elems_eq r e) rhs) acc
  | Diff -> List.filter (fun e -> not (List.exists (fun r -> elems_eq r e) rhs)) acc

(* Side surgery for op= on an edge: both sides must be sets. *)
let side_op op l r =
  match (l, r) with
  | VSet a, VSet b -> Ok (VSet (apply_set_op op a b))
  | _ -> Error (Printf.sprintf "'%s=' side is not a set" (op_symbol op))

(* -- the minting discipline ------------------------------------------------- *)

(* A minted token can only INTRODUCE a value and never match one, since it is
   guaranteed unequal to everything that exists. This is the defensive twin of
   the checker's rule. *)
let rec mints_fronce (n : node) =
  match n.it with
  | Fronce None -> true
  | Set ns | Op (_, ns) | Init (_, _, ns) -> List.exists mints_fronce ns
  | Edge (a, b, ann) | UEdge (a, b, ann) ->
      List.exists mints_fronce (a :: b :: Option.to_list ann)
  | _ -> false

let mint_match_err ctx =
  ctx ^ " mints a token with '#', which can never match an existing value — \
         pin it (#N) or bind the value to a name first"

type mint = {
  mutable pins : int list;  (* '#N' indices INTRODUCED so far *)
  mutable next : int;       (* next auto index, its own space *)
}

type env = {
  mutable vars : (string * value) list;  (* first-binding order preserved *)
  fronces : mint;
  (* Depth of matching context: '^' operands, '/' subtrahends, and the RHS of
     '^=' and '/='. There a pinned token is a REFERENCE to an existing edge
     rather than an introduction, so it neither registers for uniqueness nor
     may it name a token never introduced. *)
  mutable matching : int;
}

let fronce env pinned =
  if env.matching > 0 then
    match pinned with
    | Some n when List.mem n env.fronces.pins -> Ok (VFronce (User n))
    | Some n ->
        Error
          (Printf.sprintf
             "fronce token #%d has not been introduced — nothing it could match" n)
    (* Unreachable: mints_fronce rejects '#' here before evaluation. *)
    | None -> Error (mint_match_err "this position")
  else
    match pinned with
    | Some n ->
        if List.mem n env.fronces.pins then
          Error
            (Printf.sprintf
               "fronce token #%d is written more than once — pinned tokens must \
                be unique" n)
        else (
          env.fronces.pins <- n :: env.fronces.pins;
          Ok (VFronce (User n)))
    | None ->
        let n = env.fronces.next in
        env.fronces.next <- n + 1;
        Ok (VFronce (Auto n))

let bind env name v =
  if List.mem_assoc name env.vars then
    env.vars <- List.map (fun (k, old) -> if k = name then (k, v) else (k, old)) env.vars
  else env.vars <- env.vars @ [ (name, v) ]

let get env name =
  match List.assoc_opt name env.vars with
  | Some v -> Ok v
  | None -> Error ("undefined variable " ^ name)

(* -- evaluation ------------------------------------------------------------- *)

let ( let* ) = Result.bind

let rec eval env (n : node) =
  match n.it with
  | Int i -> Ok (VInt i)
  | Dec d -> Ok (VDec d)
  | Str s -> Ok (VStr s)
  | Fronce f -> fronce env f
  | Ref name -> get env name
  | Set elems ->
      let* out =
        List.fold_left
          (fun acc e ->
            let* acc = acc in
            let* el = eval_elem env e in
            Ok (push_unique acc el))
          (Ok []) elems
      in
      Ok (VSet out)
  | Op (op, operands) -> eval_op env op operands
  | Edge (t, h, ann) -> eval_edge env false t h ann
  | UEdge (a, b, ann) -> eval_edge env true a b ann
  | Init (name, _, args) ->
      (* Type arguments are not read: types fully erase. *)
      let* vs =
        List.fold_left
          (fun acc a ->
            let* acc = acc in
            let* v = eval env a in
            Ok (acc @ [ v ]))
          (Ok []) args
      in
      Ok (VStruct (name, vs))

and eval_elem env (n : node) =
  (* Only a reference carries a name, and for a graph that name is identity. *)
  let label = match n.it with Ref r -> Some r | _ -> None in
  let* v = eval env n in
  Ok { label; v }

and eval_matching env node =
  env.matching <- env.matching + 1;
  let r = eval env node in
  env.matching <- env.matching - 1;
  r

and eval_op env op operands =
  let sym = op_symbol op in
  (* '^' matches in every operand; '/' matches in the subtrahends. *)
  let match_from = match op with Inter -> 0 | Diff -> 1 | Union -> max_int in
  let minting =
    List.filteri (fun i _ -> i >= match_from) operands |> List.exists mints_fronce
  in
  if minting then Error (mint_match_err ("operand of '" ^ sym ^ "'"))
  else
    let eval_at i n = if i >= match_from then eval_matching env n else eval env n in
    match operands with
    | [] -> Ok (VSet [])
    | first :: rest ->
        let* fv = eval_at 0 first in
        let* acc =
          match as_elems fv with
          | Some es -> Ok es
          | None -> Error ("operand of '" ^ sym ^ "' is not a set")
        in
        let* out =
          List.fold_left
            (fun acc (i, operand) ->
              let* acc = acc in
              let* rv = eval_at i operand in
              match as_elems rv with
              | Some es -> Ok (apply_set_op op acc es)
              | None -> Error ("operand of '" ^ sym ^ "' is not a set"))
            (Ok acc)
            (List.mapi (fun i o -> (i + 1, o)) rest)
        in
        Ok (VSet out)

and eval_edge env undirected a b ann =
  let ka, kb = if undirected then ("a", "b") else ("tail", "head") in
  let* av = eval env a in
  let* bv = eval env b in
  let* () =
    List.fold_left
      (fun acc (side, v) ->
        let* () = acc in
        match v with
        | VSet _ -> Ok ()
        | _ -> Error (side ^ " of an edge did not evaluate to a set"))
      (Ok ()) [ (ka, av); (kb, bv) ]
  in
  let* annv =
    match ann with
    | None -> Ok None
    | Some v ->
        let* x = eval env v in
        Ok (Some x)
  in
  Ok (if undirected then VUEdge (av, bv, annv) else VEdge (av, bv, annv))

(* 'g op= rhs': dispatch on g's runtime value, mirroring the checker. *)
let eval_ext env name op rhs =
  let sym = op_symbol op in
  let is_match = op = Inter || op = Diff in
  if is_match && mints_fronce rhs then
    Error (mint_match_err ("the RHS of '" ^ sym ^ "='"))
  else
    let* cur = get env name in
    let* rhs_val = if is_match then eval_matching env rhs else eval env rhs in
    match cur with
    | VSet acc -> (
        match as_elems rhs_val with
        | Some relems -> Ok (VSet (apply_set_op op acc relems))
        | None ->
            Error
              (Printf.sprintf "'%s=' on %s: the RHS did not evaluate to a set" sym name))
    (* Side surgery: the LHS keeps its payload, and the RHS must be a PLAIN
       edge, since surgery edits sides and never annotations. *)
    | VEdge (t, h, ann) -> (
        match rhs_val with
        | VEdge (rt, rh, None) ->
            let* t' = side_op op t rt in
            let* h' = side_op op h rh in
            Ok (VEdge (t', h', ann))
        | VEdge _ ->
            Error
              (Printf.sprintf
                 "'%s=' on %s: the RHS of side surgery must be a plain \
                  (unannotated) edge" sym name)
        | _ -> Error (Printf.sprintf "'%s=' on %s: the RHS is not a directed edge" sym name))
    | VUEdge (a, b, ann) -> (
        match rhs_val with
        (* Sides pair by WRITTEN order: a-with-a, b-with-b. *)
        | VUEdge (ra, rb, None) ->
            let* a' = side_op op a ra in
            let* b' = side_op op b rb in
            Ok (VUEdge (a', b', ann))
        | VUEdge _ ->
            Error
              (Printf.sprintf
                 "'%s=' on %s: the RHS of side surgery must be a plain \
                  (unannotated) edge" sym name)
        | _ ->
            Error
              (Printf.sprintf "'%s=' on %s: the RHS is not an undirected edge" sym name))
    | _ -> Error (Printf.sprintf "'%s=' cannot apply to the value of %s" sym name)

(* -- running a program ------------------------------------------------------ *)

(* The coercive view, made real.

   Types otherwise erase completely and every dispatch above is on a runtime
   constructor. The one exception is UndirectedEdge <: Set<Edge>, which the
   checker may use to accept 'let g: mut Set<Edge> = a <-> b'. If nothing in
   the value recorded that the coercion happened, a later 'g &= ...' would
   dispatch on the stored uedge and perform side surgery where the checker had
   selected set mutation.

   Storing the realised set at the binding closes it: every later op= finds a
   set and takes the branch the checker chose. The Rust evaluator re-derives
   "was this declared mut and set-shaped?" from the written syntax, in 55 lines
   with their own alias table and a cycle guard. Here the checker's own answer
   arrives as the declaration. *)
let run (program : program) (declarations : (bool * Types.ty) option list) =
  let env = { vars = []; fronces = { pins = []; next = 0 }; matching = 0 } in
  let decl_of i = try List.nth declarations i with _ -> None in
  let rec go i = function
    | [] -> Ok env
    | (stmt : stmt) :: rest -> (
        match stmt.it with
        (* Definitions carry no runtime value: types fully erase. *)
        | SStruct _ | SType _ -> go (i + 1) rest
        | SLet (name, _, value) ->
            let* v = eval env value in
            let v =
              match (v, decl_of i) with
              | VUEdge _, Some (true, ty) when Types.is_graph_set ty ->
                  VSet (Option.get (as_elems v))
              | _ -> v
            in
            bind env name v;
            go (i + 1) rest
        | SExt (name, op, rhs) ->
            let* v = eval_ext env name op rhs in
            bind env name v;
            go (i + 1) rest)
  in
  go 0 program
