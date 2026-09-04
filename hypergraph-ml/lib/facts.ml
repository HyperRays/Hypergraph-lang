(* The evaluated hypergraph as typed relations, in Soufflé syntax.

   The incidence matrix already IS a relation, since a column is one row of
   "this edge touches that vertex". What this adds is that the STRUCTURES cross
   too: a query joins on values that were never flattened to display text.

   The schema is not fixed here. A program's own struct definitions become
   typed relations, so 'struct I { n: Int, op: String, args: String }' yields

     .decl I(x: id, n: number, op: symbol, args: symbol)

   and every I-payload one row of it. A program's type declarations are its
   query vocabulary.

   Identity: every value is interned by its CANONICAL FORM, the same identity
   elems_eq decides, so two edges carrying equal payloads reference one payload
   id and a vertex shared by two graphs is one value with two vertex() facts.
   Ids are opaque symbols, and the display text survives only in show(), as
   provenance for reports rather than a parsing surface.

   Two kinds of id share the one 'id' type: a graph keeps its SOURCE NAME so a
   dump stays readable, while values and edges get minted ones. The '%' makes
   those namespaces disjoint by construction, since no source name can carry
   the sigil.

   Numbers are emitted as written. Soufflé's default number domain is 32-bit
   signed, so an Int outside it fails loudly at Soufflé's parser rather than
   silently here. *)

open Value
module SMap = Interp.SMap

let base_decls =
  {|// hypergraph facts — base relations (see hypergraph-ml/lib/facts.ml)
.type id <: symbol
.decl graph(g: id)                      // a drawn graph variable
.decl graph_name(g: id, name: symbol)   // its source name, tag stripped
.decl graph_tag(g: id, tag: symbol)     // --tag of the emitting program ("" if none)
.decl vertex(g: id, v: id)              // v is a row of g
.decl edge(g: id, e: id)                // e is a column of g
.decl group(g: id, grp: symbol, e: id)  // atlas grouping, by group label
.decl tail(e: id, v: id)                // incidence -1 (2 emits both)
.decl head(e: id, v: id)                // incidence +1 (2 emits both)
.decl payload(e: id, p: id)             // the edge's '-[p]->' annotation
.decl show(x: id, text: symbol)         // display form — provenance, not a parsing surface
.decl val_int(x: id, n: number)
.decl val_str(x: id, s: symbol)
.decl val_dec(x: id, d: float)
.decl val_fronce(x: id, t: symbol)      // "%aN" minted / "%uN" pinned
.decl val_set(x: id)
.decl val_elem(x: id, m: id)            // set membership
.decl val_graph(x: id, g: id)           // a named graph used as a value
.decl val_edge(x: id, t: id, h: id)     // an edge used as a value (sides are sets)
.decl val_uedge(x: id, a: id, b: id)
.decl val_ann(x: id, p: id)             // payload of an edge-valued value
.decl val_struct(x: id, name: symbol)   // fallback for structs without a usable .decl
.decl val_arg(x: id, i: number, m: id)
|}

(* How one struct field lands in its relation: inline for the scalar types the
   language and Soufflé share, an id reference for everything else.

   Read off the RESOLVED type rather than the written syntax, so a field
   declared through 'type M = Decimal' is still a float column. *)
type col = Num | Sym | Float | Ref

let col_of (t : Types.ty) =
  match t with Types.TInt -> Num | Types.TStr -> Sym | Types.TDec -> Float | _ -> Ref

let souffle = function
  | Num -> "number"
  | Sym -> "symbol"
  | Float -> "float"
  | Ref -> "id"

(* A struct relation shares the namespace with the base relations, so a program
   is free to name a struct 'tail' and its facts would land in the incidence
   relation. Refused rather than renamed: a silently prefixed relation is a
   schema the query author has to discover. *)
let reserved name =
  String.split_on_char '\n' base_decls
  |> List.exists (fun l ->
         match String.index_opt l '(' with
         | Some i when String.length l > 6 && String.sub l 0 6 = ".decl " ->
             String.sub l 6 (i - 6) = name
         | _ -> false)

let struct_defs (out : Check.outcome) =
  SMap.bindings out.structs
  |> List.map (fun (name, (_, fields)) -> (name, fields))

let ( let* ) = Result.bind

(* The .decl block: base relations plus one typed relation per struct. *)
let schema (out : Check.outcome) =
  let defs = struct_defs out in
  match List.find_opt (fun (n, _) -> reserved n) defs with
  | Some (n, _) ->
      Error (n ^ " collides with a base fact relation — rename the struct")
  | None ->
      let b = Buffer.create 2048 in
      Buffer.add_string b base_decls;
      List.iter
        (fun (name, fields) ->
          Buffer.add_string b (Printf.sprintf ".decl %s(x: id" name);
          List.iter
            (fun (f, t) ->
              Buffer.add_string b (Printf.sprintf ", %s: %s" f (souffle (col_of t))))
            fields;
          Buffer.add_string b ")\n")
        defs;
      Ok (Buffer.contents b)

(* Soufflé string literals use C-style escapes. The language's own strings
   already decoded theirs, so control characters are real bytes here and must
   not break the line-oriented output. *)
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
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

(* Decimals keep their point, the same rule as canon: Soufflé reads a bare
   integer literal as a number rather than a float. *)
let float_lit d =
  if Float.is_integer d then Printf.sprintf "%.1f" d else float_repr d

type emitter = {
  defs : (string * (string * Types.ty) list) list;
  tag : string;
  (* canonical form -> interned id. Graph-name keys are prefixed so a graph
     identity stays explicitly namespaced from ordinary values. *)
  ids : (string, string) Hashtbl.t;
  next : (string, int) Hashtbl.t;
  values : Buffer.t;
}

let tagged em name = if em.tag = "" then name else em.tag ^ ":" ^ name

(* '%' is the one character a source name cannot contain, so a minted id never
   collides with a graph's. *)
let fresh em prefix =
  let n = Option.value (Hashtbl.find_opt em.next prefix) ~default:0 in
  Hashtbl.replace em.next prefix (n + 1);
  tagged em (Printf.sprintf "%%%s%d" prefix n)

let line em s = Buffer.add_string em.values (s ^ "\n")

(* Intern a value; on first sight, emit its structure facts. *)
let rec value_id em v =
  let key = canon v in
  match Hashtbl.find_opt em.ids key with
  | Some id -> id
  | None ->
      let id = fresh em "v" in
      Hashtbl.replace em.ids key id;
      line em (Printf.sprintf "show(%s, %s)." (quote id) (quote key));
      (match v with
       | VInt n -> line em (Printf.sprintf "val_int(%s, %Ld)." (quote id) n)
       | VDec d -> line em (Printf.sprintf "val_dec(%s, %s)." (quote id) (float_lit d))
       | VStr s -> line em (Printf.sprintf "val_str(%s, %s)." (quote id) (quote s))
       | VFronce f ->
           let t = match f with Auto n -> Printf.sprintf "%%a%d" n
                              | User n -> Printf.sprintf "%%u%d" n in
           line em (Printf.sprintf "val_fronce(%s, %s)." (quote id) (quote t))
       | VStruct (name, args) -> struct_facts em id name args
       | VSet elems ->
           line em (Printf.sprintf "val_set(%s)." (quote id));
           List.iter
             (fun e ->
               let m = elem_id em e in
               line em (Printf.sprintf "val_elem(%s, %s)." (quote id) (quote m)))
             elems
       | VEdge (t, h, ann) | VUEdge (t, h, ann) ->
           let rel = match v with VEdge _ -> "val_edge" | _ -> "val_uedge" in
           let ti = value_id em t and hi = value_id em h in
           line em
             (Printf.sprintf "%s(%s, %s, %s)." rel (quote id) (quote ti) (quote hi));
           Option.iter
             (fun p ->
               let pi = value_id em p in
               line em (Printf.sprintf "val_ann(%s, %s)." (quote id) (quote pi)))
             ann);
      id

(* A struct value lands in its own typed relation when its definition is known
   and the value fits it. Otherwise, for an undefined struct or an arity that
   drifted, it degrades to the generic encoding rather than lying. *)
and struct_facts em id name args =
  let fits =
    match List.assoc_opt name em.defs with
    | Some fields ->
        List.length fields = List.length args
        && List.for_all2
             (fun (_, t) a ->
               match (col_of t, a) with
               | Num, VInt _ | Sym, VStr _ | Float, VDec _ | Ref, _ -> true
               | _ -> false)
             fields args
    | None -> false
  in
  if not fits then (
    line em (Printf.sprintf "val_struct(%s, %s)." (quote id) (quote name));
    List.iteri
      (fun i a ->
        let m = value_id em a in
        line em (Printf.sprintf "val_arg(%s, %d, %s)." (quote id) i (quote m)))
      args)
  else
    let fields = List.assoc name em.defs in
    let cols =
      List.map2
        (fun (_, t) a ->
          match (col_of t, a) with
          | Num, VInt n -> Printf.sprintf ", %Ld" n
          | Sym, VStr s -> ", " ^ quote s
          | Float, VDec d -> ", " ^ float_lit d
          | Ref, a -> ", " ^ quote (value_id em a)
          | _ -> assert false (* guarded by 'fits' *))
        fields args
    in
    line em (Printf.sprintf "%s(%s%s)." name (quote id) (String.concat "" cols))

(* A set element whose name IS its identity, a named graph, interns by that
   name and links to the graph entity; everything else is its value. *)
and elem_id em (e : elem) =
  match (e.label, is_graph_val e.v) with
  | Some name, true -> (
      let key = "g:" ^ name in
      match Hashtbl.find_opt em.ids key with
      | Some id -> id
      | None ->
          let id = fresh em "v" in
          Hashtbl.replace em.ids key id;
          let gid = tagged em name in
          line em (Printf.sprintf "show(%s, %s)." (quote id) (quote name));
          line em (Printf.sprintf "val_graph(%s, %s)." (quote id) (quote gid));
          id)
  | _ -> value_id em e.v

(* Ground facts for a program's drawn graphs. 'tag' distinguishes this
   program's ids inside a concatenated multi-program database. *)
let facts (out : Check.outcome) env tag =
  let defs = struct_defs out in
  match List.find_opt (fun (n, _) -> reserved n) defs with
  | Some (n, _) ->
      Error (n ^ " collides with a base fact relation — rename the struct")
  | None ->
      let em =
        { defs; tag; ids = Hashtbl.create 256; next = Hashtbl.create 4;
          values = Buffer.create 4096 }
      in
      let topo = Buffer.create 4096 in
      let put s = Buffer.add_string topo (s ^ "\n") in
      List.iter
        (fun (s : Incidence.shaped) ->
          let gid = tagged em s.graph in
          put (Printf.sprintf "graph(%s)." (quote gid));
          put (Printf.sprintf "graph_name(%s, %s)." (quote gid) (quote s.graph));
          put (Printf.sprintf "graph_tag(%s, %s)." (quote gid) (quote tag));
          put (Printf.sprintf "show(%s, %s)." (quote gid) (quote s.graph));
          List.iter
            (fun e ->
              let vid = elem_id em e in
              put (Printf.sprintf "vertex(%s, %s)." (quote gid) (quote vid)))
            s.vertices;
          List.iter
            (fun (g : Incidence.shaped_group) ->
              List.iter
                (fun (col : Incidence.shaped_column) ->
                  let eid = fresh em "e" in
                  (* The composed display label: the group label prefixes the
                     column's unless it is already there. *)
                  let label =
                    let gl = g.glabel and cl = col.clabel in
                    if
                      String.length cl >= String.length gl
                      && String.sub cl 0 (String.length gl) = gl
                    then cl
                    else gl ^ "." ^ cl
                  in
                  put (Printf.sprintf "edge(%s, %s)." (quote gid) (quote eid));
                  put
                    (Printf.sprintf "group(%s, %s, %s)." (quote gid)
                       (quote g.glabel) (quote eid));
                  put (Printf.sprintf "show(%s, %s)." (quote eid) (quote label));
                  List.iter
                    (fun (rel, side) ->
                      match side with
                      | VSet es ->
                          List.iter
                            (fun e ->
                              let vid = elem_id em e in
                              put
                                (Printf.sprintf "%s(%s, %s)." rel (quote eid)
                                   (quote vid)))
                            es
                      | _ -> ())
                    [ ("tail", col.tail); ("head", col.head) ];
                  Option.iter
                    (fun p ->
                      let pid = value_id em p in
                      put (Printf.sprintf "payload(%s, %s)." (quote eid) (quote pid)))
                    col.ann)
                g.columns)
            s.groups)
        (Incidence.shaped_matrices env);
      Ok (Buffer.contents em.values ^ Buffer.contents topo)
