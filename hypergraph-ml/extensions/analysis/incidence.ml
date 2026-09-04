open Hypergraph

type error = { binding : string; message : string }

type shaped_column = {
  column_label : string;
  tail : Value.t;
  head : Value.t;
  payload : Value.t option;
}

type shaped_group = {
  group_label : string;
  shaped_columns : shaped_column list;
}

type shaped = {
  graph_name : string;
  vertices : Value.t list;
  shaped_groups : shaped_group list;
}

type column = { label : string; entries : (int * int) list }
type group = { label : string; columns : column list }
type matrix = { graph : string; vertices : string list; groups : group list }

let ( let* ) = Result.bind

let evaluated_bindings (result : Program.result) =
  List.filter_map
    (fun (binding : Check.binding) ->
      Option.map
        (fun value -> (binding, value))
        (Value.find result.values binding.name))
    result.checked.bindings

let binding_name bindings accepts value =
  List.find_map
    (fun ((binding : Check.binding), candidate) ->
      if accepts binding.ty && Value.equal candidate value then Some binding.name
      else None)
    bindings

let edge_binding_name bindings value =
  binding_name bindings Types.is_edge value

let display_vertex bindings value =
  match binding_name bindings Types.is_graph value with
  | Some name -> name
  | None -> Value.to_string value

let annotated_label label = function
  | None -> label
  | Some payload -> label ^ "[" ^ Value.to_string payload ^ "]"

let columns_of_element bindings index (element : Value.element) =
  let base =
    Option.value (edge_binding_name bindings element.value)
      ~default:(Printf.sprintf "#%d" index)
  in
  match element.value.node with
  | Value.Edge edge ->
      let label = annotated_label base edge.payload in
      Ok
        { group_label = base;
          shaped_columns =
            [ { column_label = label;
                tail = edge.left;
                head = edge.right;
                payload = edge.payload } ] }
  | Value.UndirectedEdge edge ->
      let label = annotated_label base edge.payload in
      Ok
        { group_label = base;
          shaped_columns =
            [ { column_label = label ^ ".fwd";
                tail = edge.left;
                head = edge.right;
                payload = edge.payload };
              { column_label = label ^ ".bwd";
                tail = edge.right;
                head = edge.left;
                payload = edge.payload } ] }
  | _ ->
      Error
        { binding = "";
          message = "a graph value contains an element that is not an edge" }

let side_elements graph_name column_label side =
  match side.Value.node with
  | Value.Set elements -> Ok elements
  | _ ->
      Error
        { binding = graph_name;
          message =
            Printf.sprintf "column '%s' has a side that is not a set" column_label }

let add_unique values value =
  if List.exists (Value.equal value) values then values else values @ [ value ]

let vertices_of_groups graph_name groups =
  List.fold_left
    (fun result group ->
      let* vertices = result in
      List.fold_left
        (fun result column ->
          let* vertices = result in
          let* tail = side_elements graph_name column.column_label column.tail in
          let* head = side_elements graph_name column.column_label column.head in
          Ok
            (List.fold_left
               (fun output element -> add_unique output element.Value.value)
               (List.fold_left
                  (fun output element -> add_unique output element.Value.value)
                  vertices tail)
               head))
        (Ok vertices) group.shaped_columns)
    (Ok []) groups

let shape_graph bindings graph_name value =
  match value.Value.node with
  | Value.Set elements ->
      let* groups =
        List.fold_left
          (fun result (index, element) ->
            let* groups = result in
            match columns_of_element bindings index element with
            | Ok group -> Ok (groups @ [ group ])
            | Error error -> Error { error with binding = graph_name })
          (Ok []) (List.mapi (fun index element -> (index, element)) elements)
      in
      let* vertices = vertices_of_groups graph_name groups in
      Ok { graph_name; vertices; shaped_groups = groups }
  | _ ->
      Error
        { binding = graph_name;
          message = "a graph-typed binding did not evaluate to a set" }

let shaped_graphs (result : Program.result) =
  let bindings = evaluated_bindings result in
  List.fold_left
    (fun output ((binding : Check.binding), value) ->
      let* graphs = output in
      if Types.is_graph binding.ty then
        let* graph = shape_graph bindings binding.name value in
        Ok (graphs @ [ graph ])
      else Ok graphs)
    (Ok []) bindings

let row_of vertices value =
  let rec find index = function
    | [] -> invalid_arg "incidence vertex was not indexed"
    | candidate :: _ when Value.equal candidate value -> index
    | _ :: rest -> find (index + 1) rest
  in
  find 0 vertices

let matrix_column (shaped : shaped) (column : shaped_column) =
  let cells = Hashtbl.create 8 in
  let add_tail element =
    Hashtbl.replace cells (row_of shaped.vertices element.Value.value) (-1)
  in
  let add_head element =
    let row = row_of shaped.vertices element.Value.value in
    let coefficient = if Hashtbl.mem cells row then 2 else 1 in
    Hashtbl.replace cells row coefficient
  in
  (match column.tail.Value.node with
  | Value.Set elements -> List.iter add_tail elements
  | _ -> assert false);
  (match column.head.Value.node with
  | Value.Set elements -> List.iter add_head elements
  | _ -> assert false);
  { label = column.column_label;
    entries =
      Hashtbl.to_seq cells |> List.of_seq
      |> List.sort (fun (left, _) (right, _) -> Int.compare left right) }

let to_matrix bindings (shaped : shaped) =
  { graph = shaped.graph_name;
    vertices = List.map (display_vertex bindings) shaped.vertices;
    groups =
      List.map
        (fun group ->
          { label = group.group_label;
            columns = List.map (matrix_column shaped) group.shaped_columns })
        shaped.shaped_groups }

let matrices (result : Program.result) =
  let bindings = evaluated_bindings result in
  Result.map (List.map (to_matrix bindings)) (shaped_graphs result)

let render_text (matrices : matrix list) =
  let buffer = Buffer.create 1024 in
  List.iter
    (fun (matrix : matrix) ->
      let columns =
        List.concat_map (fun (group : group) -> group.columns) matrix.groups
      in
      let group_summary =
        match matrix.groups with
        | [] -> "none"
        | groups ->
            String.concat ", "
              (List.map
                 (fun (group : group) ->
                   Printf.sprintf "%s[%d]" group.label (List.length group.columns))
                 groups)
      in
      Buffer.add_string buffer
        (Printf.sprintf "graph %s: %d vertices x %d columns (groups: %s)\n"
           matrix.graph (List.length matrix.vertices) (List.length columns)
           group_summary);
      if columns <> [] then (
        let vertex_width =
          max 1
            (List.fold_left
               (fun width vertex -> max width (Width.width vertex))
               0 matrix.vertices)
        in
        let column_widths =
          List.map
            (fun (column : column) -> max 2 (Width.width column.label))
            columns
        in
        Buffer.add_string buffer ("  " ^ String.make vertex_width ' ');
        List.iter2
          (fun (column : column) width ->
            Buffer.add_string buffer ("  " ^ Width.left_pad column.label width))
          columns column_widths;
        Buffer.add_char buffer '\n';
        let cells =
          List.map
            (fun (column : column) ->
              let table = Hashtbl.create (List.length column.entries) in
              List.iter (fun (row, value) -> Hashtbl.add table row value) column.entries;
              table)
            columns
        in
        List.iteri
          (fun row vertex ->
            Buffer.add_string buffer ("  " ^ Width.left_pad vertex vertex_width);
            List.iter2
              (fun table width ->
                let cell =
                  match Hashtbl.find_opt table row with
                  | None | Some 0 -> "."
                  | Some 1 -> "+1"
                  | Some (-1) -> "-1"
                  | Some value -> string_of_int value
                in
                Buffer.add_string buffer ("  " ^ Width.left_pad cell width))
              cells column_widths;
            Buffer.add_char buffer '\n')
          matrix.vertices);
      Buffer.add_char buffer '\n')
    matrices;
  Buffer.contents buffer

let to_yojson (matrices : matrix list) =
  `List
    (List.map
       (fun (matrix : matrix) ->
         `Assoc
           [ ("graph", `String matrix.graph);
             ("vertices", `List (List.map (fun value -> `String value) matrix.vertices));
             ( "groups",
               `List
                 (List.map
                    (fun (group : group) ->
                      `Assoc
                        [ ("label", `String group.label);
                          ( "columns",
                            `List
                              (List.map
                                 (fun (column : column) ->
                                   `Assoc
                                     [ ("label", `String column.label);
                                       ( "entries",
                                         `List
                                           (List.map
                                              (fun (row, value) ->
                                                `List [ `Int row; `Int value ])
                                              column.entries) ) ])
                                 group.columns) ) ])
                    matrix.groups) ) ] )
       matrices)

let render_json matrices = Yojson.Safe.to_string (to_yojson matrices)
