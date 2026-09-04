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

val shaped_graphs : Program.result -> (shaped list, error) result
val matrices : Program.result -> (matrix list, error) result
val render_text : matrix list -> string
val to_yojson : matrix list -> Yojson.Safe.t
val render_json : matrix list -> string
