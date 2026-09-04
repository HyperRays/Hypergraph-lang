(* Incidence matrices: an evaluated graph value, shaped into columns and rows.

   Shaping is kept apart from rendering. A shaped column still holds its sides
   and payload as VALUES, which is what lets the facts emitter read them
   without parsing display text back apart. *)

open Value

(* A column after evaluation but before rendering. 'label' is the full display
   label, provenance plus '[payload]', computed here because an undirected
   pair's '.fwd' and '.bwd' suffix attaches OUTSIDE the payload bracket and
   could not be recomposed later. *)
type shaped_column = {
  clabel : string;
  tail : value;
  head : value;
  ann : value option;
}

type shaped_group = { glabel : string; columns : shaped_column list }

(* One graph variable, evaluated and shaped: columns grouped by provenance,
   vertices in first-appearance order and indexed by CANONICAL FORM, which is
   the same identity elems_eq decides. *)
type shaped = {
  graph : string;
  vertices : elem list;
  index : (string, int) Hashtbl.t;
  groups : shaped_group list;
}

(* A column's display label: the provenance label, a binding-name path, plus
   the edge's own payload in brackets. The bracket is semantic content, part of
   the edge, where the bare label is only provenance. *)
let ann_label label = function
  | Some v -> Printf.sprintf "%s[%s]" label (canon v)
  | None -> label

(* Flatten an element into labelled columns: an edge is one, an undirected edge
   is two, and a nested set contributes its members with dotted labels. *)
let rec elem_columns label v out =
  match v with
  | VEdge (t, h, ann) ->
      Some (out @ [ { clabel = ann_label label ann; tail = t; head = h; ann } ])
  | VUEdge (a, b, ann) ->
      let base = ann_label label ann in
      Some
        (out
        @ List.map
            (fun (suffix, tail, head) ->
              { clabel = base ^ suffix; tail; head; ann })
            [ (".fwd", a, b); (".bwd", b, a) ])
  | VSet inner ->
      List.fold_left
        (fun acc (i, e) ->
          match acc with
          | None -> None
          | Some out ->
              let l =
                Printf.sprintf "%s.%s" label
                  (match e.label with Some n -> n | None -> Printf.sprintf "#%d" i)
              in
              elem_columns l e.v out)
        (Some out)
        (List.mapi (fun i e -> (i, e)) inner)
  | _ -> None

let shape graph elems =
  if elems = [] then None
  else
    (* Top-level elements become the column groups. *)
    let groups =
      List.fold_left
        (fun acc (i, e) ->
          match acc with
          | None -> None
          | Some gs -> (
              let label =
                match e.label with Some n -> n | None -> Printf.sprintf "#%d" i
              in
              match e.v with
              | VEdge _ | VUEdge _ -> (
                  match elem_columns label e.v [] with
                  | Some cols -> Some (gs @ [ { glabel = label; columns = cols } ])
                  | None -> None)
              | VSet inner -> (
                  let cols =
                    List.fold_left
                      (fun acc (j, m) ->
                        match acc with
                        | None -> None
                        | Some out ->
                            let l =
                              Printf.sprintf "%s.%s" label
                                (match m.label with
                                 | Some n -> n
                                 | None -> Printf.sprintf "#%d" j)
                            in
                            elem_columns l m.v out)
                      (Some [])
                      (List.mapi (fun j m -> (j, m)) inner)
                  in
                  match cols with
                  | Some cols -> Some (gs @ [ { glabel = label; columns = cols } ])
                  | None -> None)
              | _ -> None))
        (Some [])
        (List.mapi (fun i e -> (i, e)) elems)
    in
    match groups with
    | None -> None
    (* Nothing to draw: every member turned out to be an empty graph. This is
       the guard at the top applied ONE LEVEL DOWN, so the same emptiness does
       not get filtered at one depth and emitted at the next. It drops the
       MATRIX and never an individual group, because a group contributing no
       columns beside one that does is worth keeping: 'e[0]' in the header is
       how the rendering says "e is a member, and it is empty". Membership and
       column count are different facts. *)
    | Some gs when List.for_all (fun g -> g.columns = []) gs -> None
    | Some gs ->
        (* Vertex rows in first-appearance order, tails before heads per
           column, deduplicated and indexed by canonical form. canon_elem
           mirrors elems_eq tier for tier, so the map agrees with the
           equality. *)
        let index = Hashtbl.create 64 in
        let vertices = ref [] in
        let count = ref 0 in
        List.iter
          (fun g ->
            List.iter
              (fun col ->
                List.iter
                  (fun side ->
                    match side with
                    | VSet es ->
                        List.iter
                          (fun e ->
                            let k = canon_elem e in
                            if not (Hashtbl.mem index k) then (
                              Hashtbl.add index k !count;
                              incr count;
                              vertices := e :: !vertices))
                          es
                    | _ -> ())
                  [ col.tail; col.head ])
              g.columns)
          gs;
        Some { graph; vertices = List.rev !vertices; index; groups = gs }

(* -- the rendered matrix ---------------------------------------------------- *)

type column = {
  label : string;
  (* SPARSE cells: (row, -1 | +1 | 2), sorted by row, absent rows are 0.
     Incidence columns touch a handful of rows however many vertices the graph
     has, so a dense row wastes quadratic space. *)
  entries : (int * int) list;
}

type group = { label : string; columns : column list }
type matrix = { graph : string; vertices : string list; groups : group list }

let to_matrix (s : shaped) =
  let column col =
    (* Tail marks first, so a row on both sides becomes 2. *)
    let cells = Hashtbl.create 8 in
    let order = ref [] in
    let put k v =
      if Hashtbl.mem cells k then Hashtbl.replace cells k v
      else (
        Hashtbl.add cells k v;
        order := k :: !order)
    in
    (match col.tail with
     | VSet es -> List.iter (fun e -> put (Hashtbl.find s.index (canon_elem e)) (-1)) es
     | _ -> ());
    (match col.head with
     | VSet es ->
         List.iter
           (fun e ->
             let k = Hashtbl.find s.index (canon_elem e) in
             if Hashtbl.mem cells k then Hashtbl.replace cells k 2 else put k 1)
           es
     | _ -> ());
    { label = col.clabel;
      entries =
        List.sort_uniq compare (List.map (fun k -> (k, Hashtbl.find cells k)) !order) }
  in
  { graph = s.graph;
    vertices = List.map canon_elem s.vertices;
    groups =
      List.map
        (fun g -> { label = g.glabel; columns = List.map column g.columns })
        s.groups }

(* One shaped graph per variable whose final value is a non-empty set of
   edges. *)
let shaped_matrices env =
  List.filter_map
    (fun (name, v) -> match v with VSet elems -> shape name elems | _ -> None)
    env.vars

let matrices env = List.map to_matrix (shaped_matrices env)

(* -- text ------------------------------------------------------------------- *)

let render_text ms =
  let b = Buffer.create 1024 in
  List.iter
    (fun m ->
      let cols = List.concat_map (fun (g : group) -> g.columns) m.groups in
      let summary =
        String.concat ", "
          (List.map
             (fun (g : group) ->
                Printf.sprintf "%s[%d]" g.label (List.length g.columns))
             m.groups)
      in
      Buffer.add_string b
        (Printf.sprintf "graph %s: %d vertices x %d columns (groups: %s)\n" m.graph
           (List.length m.vertices) (List.length cols) summary);
      let vw =
        max 1
          (List.fold_left (fun n v -> max n (Width.width v)) 0 m.vertices)
      in
      let widths = List.map (fun (c : column) -> max 2 (Width.width c.label)) cols in
      Buffer.add_string b (Printf.sprintf "  %s" (String.make vw ' '));
      List.iter2
        (fun (c : column) w -> Buffer.add_string b ("  " ^ Width.rpad c.label w))
        cols widths;
      Buffer.add_char b '\n';
      (* Entries are sparse; a per-column table restores by-row access. *)
      let cells =
        List.map
          (fun (c : column) ->
            let h = Hashtbl.create 8 in
            List.iter (fun (r, v) -> Hashtbl.replace h r v) c.entries;
            h)
          cols
      in
      List.iteri
        (fun r v ->
          Buffer.add_string b ("  " ^ Width.rpad v vw);
          List.iter2
            (fun h w ->
              let cell =
                match Hashtbl.find_opt h r with
                | None | Some 0 -> "."
                | Some 1 -> "+1"
                | Some (-1) -> "-1"
                | Some other -> string_of_int other
              in
              Buffer.add_string b ("  " ^ Width.rpad cell w))
            cells widths;
          Buffer.add_char b '\n')
        m.vertices;
      Buffer.add_char b '\n')
    ms;
  Buffer.contents b

(* The same matrices as JSON, which is what a consumer that wants the numbers
   rather than the picture reads. Entries stay sparse: [row, value] pairs, with
   rows not listed being zero. *)
let to_json ms =
  let open Json in
  List
    (List.map
       (fun m ->
         Obj
           [ ("graph", Str m.graph);
             ("vertices", List (List.map (fun v -> Str v) m.vertices));
             ("groups",
              List
                (List.map
                   (fun (g : group) ->
                     Obj
                       [ ("label", Str g.label);
                         ("columns",
                          List
                            (List.map
                               (fun (c : column) ->
                                 Obj
                                   [ ("label", Str c.label);
                                     ("entries",
                                      List
                                        (List.map
                                           (fun (r, v) ->
                                             List
                                               [ Num (string_of_int r);
                                                 Num (string_of_int v) ])
                                           c.entries)) ])
                               g.columns)) ])
                   m.groups)) ])
       ms)

let render_json ms = Json.to_string (to_json ms)
