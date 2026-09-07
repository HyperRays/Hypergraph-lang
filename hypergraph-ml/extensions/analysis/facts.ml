open Hypergraph

type error = { message : string }

type column_kind = Integer | Decimal | String | Reference

type relation = {
  relation_name : string;
  relation_columns : (string * column_kind) list;
}

type variant_schema = {
  variant_name : string;
  variant_payload : Types.t list;
}

let ( let* ) = Result.bind
let fail message = Error { message }

let base_relation_names =
  [ "graph"; "graph_name"; "graph_tag"; "vertex"; "edge"; "group";
    "tail"; "head"; "payload"; "show"; "val_int"; "val_dec";
    "val_str"; "val_set"; "val_elem"; "val_list"; "val_item";
    "val_graph"; "val_edge";
    "val_uedge"; "val_ann"; "val_struct"; "val_variant"; "val_arg" ]

let base_schema =
  {|// hypergraph analysis facts
.type id <: symbol
.decl graph(g: id)
.decl graph_name(g: id, name: symbol)
.decl graph_tag(g: id, tag: symbol)
.decl vertex(g: id, v: id)
.decl edge(g: id, e: id)
.decl group(g: id, grp: symbol, e: id)
.decl tail(e: id, v: id)
.decl head(e: id, v: id)
.decl payload(e: id, p: id)
.decl show(x: id, text: symbol)
.decl val_int(x: id, literal: symbol)
.decl val_dec(x: id, numerator: symbol, denominator: symbol)
.decl val_str(x: id, value: symbol)
.decl val_set(x: id)
.decl val_elem(x: id, member: id)
.decl val_list(x: id)
.decl val_item(x: id, position: number, value: id)
.decl val_graph(x: id, g: id)
.decl val_edge(x: id, tail_set: id, head_set: id)
.decl val_uedge(x: id, left_set: id, right_set: id)
.decl val_ann(x: id, p: id)
.decl val_struct(x: id, name: symbol)
.decl val_variant(x: id, enum_name: symbol, variant_name: symbol)
.decl val_arg(x: id, position: number, value: id)
|}

let column_kind = function
  | Types.Int -> Integer
  | Types.Decimal -> Decimal
  | Types.String -> String
  | _ -> Reference

let souffle_type = function
  | Integer | Decimal | String -> "symbol"
  | Reference -> "id"

let split_member_label label =
  match String.index_opt label ':' with
  | None -> (label, None)
  | Some index ->
      (String.sub label 0 index,
       Some
         (int_of_string
            (String.sub label (index + 1) (String.length label - index - 1))))

let variant_schemas (declaration : Check.declaration) =
  List.fold_left
    (fun variants (label, ty) ->
      let name, position = split_member_label label in
      match position with
      | None ->
          variants @ [ { variant_name = name; variant_payload = [] } ]
      | Some _ ->
          let rec append = function
            | [] -> [ { variant_name = name; variant_payload = [ ty ] } ]
            | variant :: rest when String.equal variant.variant_name name ->
                { variant with variant_payload = variant.variant_payload @ [ ty ] }
                :: rest
            | variant :: rest -> variant :: append rest
          in
          append variants)
    [] declaration.resolved_members

let struct_relation (declaration : Check.declaration) =
  { relation_name = declaration.name;
    relation_columns =
      ("x", Reference)
      :: List.map
           (fun (name, ty) -> (name, column_kind ty))
           declaration.resolved_members }

let enum_relations (declaration : Check.declaration) =
  variant_schemas declaration
  |> List.map (fun variant ->
       { relation_name = declaration.name ^ "__" ^ variant.variant_name;
         relation_columns =
           ("x", Reference)
           :: List.mapi
                (fun index ty -> ("arg" ^ string_of_int index, column_kind ty))
                variant.variant_payload })

let generated_relations (checked : Check.checked) =
  let option_relations =
    [ { relation_name = "Option__None";
        relation_columns = [ ("x", Reference) ] };
      { relation_name = "Option__Some";
        relation_columns = [ ("x", Reference); ("arg0", Reference) ] } ]
  in
  option_relations
  @ List.concat_map
      (fun (declaration : Check.declaration) ->
        match declaration.kind with
        | Check.Struct_kind -> [ struct_relation declaration ]
        | Check.Enum_kind -> enum_relations declaration)
      checked.declarations

let validate_relations relations =
  let seen = Hashtbl.create (List.length base_relation_names + List.length relations) in
  List.iter (fun name -> Hashtbl.add seen name ()) base_relation_names;
  let rec validate = function
    | [] -> Ok ()
    | relation :: rest ->
        if Hashtbl.mem seen relation.relation_name then
          fail
            (Printf.sprintf "generated relation '%s' collides with another relation"
               relation.relation_name)
        else
          let names = List.map fst relation.relation_columns in
          let duplicate =
            List.find_opt
              (fun name ->
                List.length (List.filter (String.equal name) names) > 1)
              names
          in
          (match duplicate with
          | Some name ->
              fail
                (Printf.sprintf "relation '%s' has duplicate attribute '%s'"
                   relation.relation_name name)
          | None ->
              Hashtbl.add seen relation.relation_name ();
              validate rest)
  in
  validate relations

let schema checked =
  let relations = generated_relations checked in
  let* () = validate_relations relations in
  let buffer = Buffer.create 2048 in
  Buffer.add_string buffer base_schema;
  List.iter
    (fun relation ->
      Buffer.add_string buffer (".decl " ^ relation.relation_name ^ "(");
      relation.relation_columns
      |> List.iteri (fun index (name, kind) ->
           if index > 0 then Buffer.add_string buffer ", ";
           Buffer.add_string buffer (name ^ ": " ^ souffle_type kind));
      Buffer.add_string buffer ")\n")
    relations;
  Ok (Buffer.contents buffer)

let quote text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\t' -> Buffer.add_string buffer "\\t"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\b' -> Buffer.add_string buffer "\\b"
      | '\012' -> Buffer.add_string buffer "\\f"
      | character -> Buffer.add_char buffer character)
    text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

type emitter = {
  declarations : Check.declaration list;
  graph_bindings : (string * Value.t) list;
  tag : string;
  mutable interned : (Value.t * string) list;
  next : (string, int) Hashtbl.t;
  values : Buffer.t;
}

let tagged emitter name =
  if String.equal emitter.tag "" then name else emitter.tag ^ ":" ^ name

let fresh emitter prefix =
  let index = Option.value (Hashtbl.find_opt emitter.next prefix) ~default:0 in
  Hashtbl.replace emitter.next prefix (index + 1);
  tagged emitter (Printf.sprintf "%%%s%d" prefix index)

let line buffer format =
  Printf.ksprintf
    (fun text ->
      Buffer.add_string buffer text;
      Buffer.add_char buffer '\n')
    format

let same_marker left right =
  match (left.Value.marker, right.Value.marker) with
  | Some left, Some right -> String.equal left right
  | _ -> false

let graph_names emitter value =
  List.filter_map
    (fun (name, graph) -> if same_marker value graph then Some name else None)
    emitter.graph_bindings

let declaration emitter kind name =
  List.find_opt
    (fun (declaration : Check.declaration) ->
      declaration.kind = kind && String.equal declaration.name name)
    emitter.declarations

let rec typed_argument emitter ty value =
  match (column_kind ty, value.Value.node) with
  | Integer, Value.Int integer -> Ok (quote (Z.to_string integer))
  | Decimal, Value.Decimal decimal -> Ok (quote (Q.to_string decimal))
  | String, Value.String text -> Ok (quote text)
  | Reference, _ -> Result.map quote (value_id emitter value)
  | Integer, _ -> fail "an Int query column received a non-Int runtime value"
  | Decimal, _ -> fail "a Decimal query column received a non-Decimal runtime value"
  | String, _ -> fail "a String query column received a non-String runtime value"

and typed_row emitter relation_name types values =
  if List.length types <> List.length values then
    fail
      (Printf.sprintf "relation '%s' received the wrong number of values"
         relation_name)
  else
    let* rendered =
      List.fold_left2
        (fun output ty value ->
          let* output = output in
          let* value = typed_argument emitter ty value in
          Ok (output @ [ value ]))
        (Ok []) types values
    in
    Ok rendered

and generic_arguments emitter id values =
  List.fold_left
    (fun result (index, value) ->
      let* () = result in
      let* value_id = value_id emitter value in
      line emitter.values "val_arg(%s, %d, %s)." (quote id) index
        (quote value_id);
      Ok ())
    (Ok ()) (List.mapi (fun index value -> (index, value)) values)

and emit_struct emitter id name values =
  line emitter.values "val_struct(%s, %s)." (quote id) (quote name);
  let* () = generic_arguments emitter id values in
  match declaration emitter Check.Struct_kind name with
  | None -> fail ("missing checked struct declaration '" ^ name ^ "'")
  | Some declaration ->
      let types = List.map snd declaration.resolved_members in
      let* rendered = typed_row emitter name types values in
      line emitter.values "%s(%s%s)." name (quote id)
        (if rendered = [] then "" else ", " ^ String.concat ", " rendered);
      Ok ()

and emit_variant emitter id enum_name variant_name values =
  line emitter.values "val_variant(%s, %s, %s)." (quote id) (quote enum_name)
    (quote variant_name);
  let* () = generic_arguments emitter id values in
  let relation_name = enum_name ^ "__" ^ variant_name in
  if String.equal enum_name "Option" then
    let types = List.map (fun _ -> Types.Parameter "Option") values in
    let* rendered = typed_row emitter relation_name types values in
    line emitter.values "%s(%s%s)." relation_name (quote id)
      (if rendered = [] then "" else ", " ^ String.concat ", " rendered);
    Ok ()
  else
    match declaration emitter Check.Enum_kind enum_name with
    | None -> fail ("missing checked enum declaration '" ^ enum_name ^ "'")
    | Some declaration -> (
        match
          List.find_opt
            (fun variant -> String.equal variant.variant_name variant_name)
            (variant_schemas declaration)
        with
        | None ->
            fail
              (Printf.sprintf "enum '%s' has no checked variant '%s'" enum_name
                 variant_name)
        | Some variant ->
            let* rendered =
              typed_row emitter relation_name variant.variant_payload values
            in
            line emitter.values "%s(%s%s)." relation_name (quote id)
              (if rendered = [] then "" else ", " ^ String.concat ", " rendered);
            Ok ())

and emit_value emitter id value =
  let names = graph_names emitter value in
  if names <> [] then (
    List.iter
      (fun name ->
        line emitter.values "val_graph(%s, %s)." (quote id)
          (quote (tagged emitter name)))
      names;
    Ok ())
  else
    match value.Value.node with
    | Value.Int integer ->
        line emitter.values "val_int(%s, %s)." (quote id)
          (quote (Z.to_string integer));
        Ok ()
    | Value.Decimal decimal ->
        line emitter.values "val_dec(%s, %s, %s)." (quote id)
          (quote (Z.to_string (Q.num decimal)))
          (quote (Z.to_string (Q.den decimal)));
        Ok ()
    | Value.String text ->
        line emitter.values "val_str(%s, %s)." (quote id) (quote text);
        Ok ()
    | Value.Set elements ->
        line emitter.values "val_set(%s)." (quote id);
        List.fold_left
          (fun result (element : Value.element) ->
            let* () = result in
            let* member = value_id emitter element.value in
            line emitter.values "val_elem(%s, %s)." (quote id) (quote member);
            Ok ())
          (Ok ()) elements
    | Value.List values ->
        line emitter.values "val_list(%s)." (quote id);
        List.fold_left
          (fun result (position, value) ->
            let* () = result in
            let* item = value_id emitter value in
            line emitter.values "val_item(%s, %d, %s)." (quote id) position
              (quote item);
            Ok ())
          (Ok ()) (List.mapi (fun position value -> (position, value)) values)
    | Value.Edge edge | Value.UndirectedEdge edge ->
        let relation =
          match value.node with Value.Edge _ -> "val_edge" | _ -> "val_uedge"
        in
        let* left = value_id emitter edge.left in
        let* right = value_id emitter edge.right in
        line emitter.values "%s(%s, %s, %s)." relation (quote id) (quote left)
          (quote right);
        (match edge.payload with
        | None -> Ok ()
        | Some payload ->
            let* payload = value_id emitter payload in
            line emitter.values "val_ann(%s, %s)." (quote id) (quote payload);
            Ok ())
    | Value.Struct (name, values) -> emit_struct emitter id name values
    | Value.Variant (enum_name, variant_name, values) ->
        emit_variant emitter id enum_name variant_name values

and value_id emitter value =
  match
    List.find_opt
      (fun (candidate, _) -> Value.equal candidate value)
      emitter.interned
  with
  | Some (_, id) -> Ok id
  | None ->
      let id = fresh emitter "v" in
      emitter.interned <- emitter.interned @ [ (value, id) ];
      let display =
        match graph_names emitter value with
        | name :: _ -> name
        | [] -> Value.to_string value
      in
      line emitter.values "show(%s, %s)." (quote id)
        (quote display);
      let* () = emit_value emitter id value in
      Ok id

let evaluated_graph_bindings (result : Program.result) =
  List.filter_map
    (fun (binding : Check.binding) ->
      if Types.is_graph binding.ty then
        Option.map (fun value -> (binding.name, value))
          (Value.find result.values binding.name)
      else None)
    result.checked.bindings

let emit_side emitter topology relation edge_id side =
  match side.Value.node with
  | Value.Set elements ->
      List.fold_left
        (fun result (element : Value.element) ->
          let* () = result in
          let* vertex = value_id emitter element.value in
          line topology "%s(%s, %s)." relation (quote edge_id) (quote vertex);
          Ok ())
        (Ok ()) elements
  | _ -> fail ("topology relation '" ^ relation ^ "' received a non-set side")

let facts ?(tag = "") (result : Program.result) =
  let relations = generated_relations result.checked in
  let* () = validate_relations relations in
  let* graphs =
    Result.map_error
      (fun (error : Incidence.error) -> { message = error.binding ^ ": " ^ error.message })
      (Incidence.shaped_graphs result)
  in
  let emitter =
    { declarations = result.checked.declarations;
      graph_bindings = evaluated_graph_bindings result;
      tag;
      interned = [];
      next = Hashtbl.create 4;
      values = Buffer.create 4096 }
  in
  let topology = Buffer.create 4096 in
  let* () =
    List.fold_left
      (fun result (graph : Incidence.shaped) ->
        let* () = result in
        let graph_id = tagged emitter graph.graph_name in
        line topology "graph(%s)." (quote graph_id);
        line topology "graph_name(%s, %s)." (quote graph_id)
          (quote graph.graph_name);
        line topology "graph_tag(%s, %s)." (quote graph_id) (quote tag);
        line topology "show(%s, %s)." (quote graph_id) (quote graph.graph_name);
        let* () =
          List.fold_left
            (fun result vertex ->
              let* () = result in
              let* vertex_id = value_id emitter vertex in
              line topology "vertex(%s, %s)." (quote graph_id) (quote vertex_id);
              Ok ())
            (Ok ()) graph.vertices
        in
        List.fold_left
          (fun result (group : Incidence.shaped_group) ->
            let* () = result in
            List.fold_left
              (fun result (column : Incidence.shaped_column) ->
                let* () = result in
                let edge_id = fresh emitter "e" in
                line topology "edge(%s, %s)." (quote graph_id) (quote edge_id);
                line topology "group(%s, %s, %s)." (quote graph_id)
                  (quote group.group_label) (quote edge_id);
                line topology "show(%s, %s)." (quote edge_id)
                  (quote column.column_label);
                let* () = emit_side emitter topology "tail" edge_id column.tail in
                let* () = emit_side emitter topology "head" edge_id column.head in
                (match column.payload with
                | None -> Ok ()
                | Some payload ->
                    let* payload_id = value_id emitter payload in
                    line topology "payload(%s, %s)." (quote edge_id)
                      (quote payload_id);
                    Ok ()))
              (Ok ()) group.shaped_columns)
          (Ok ()) graph.shaped_groups)
      (Ok ()) graphs
  in
  Ok (Buffer.contents emitter.values ^ Buffer.contents topology)
