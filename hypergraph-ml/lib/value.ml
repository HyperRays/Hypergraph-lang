type t = { node : node; marker : string option }

and node =
  | Int of Z.t
  | Decimal of Q.t
  | String of string
  | Set of element list
  | List of t list
  | Edge of edge
  | UndirectedEdge of edge
  | Struct of string * t list
  | Variant of string * string * t list

and edge = { left : t; right : t; payload : t option }

and element = { value : t }

type binding = { mutable_ : bool; mutable current : t }

type environment = (string, binding) Hashtbl.t

type error = { loc : Ast.loc; message : string }

let at ?marker node = { node; marker }

let location_marker prefix (loc : Ast.loc) =
  Printf.sprintf "%s:%d:%d" prefix loc.line loc.column

let is_graph value =
  match value.node with
  | Set (_ :: _ as elements) ->
      List.for_all
        (fun element ->
          match element.value.node with Edge _ | UndirectedEdge _ -> true | _ -> false)
        elements
  | _ -> false

let rec equal left right =
  if is_graph left && is_graph right then
    match (left.marker, right.marker) with
    | Some left, Some right -> left = right
    | _ -> equal_node left.node right.node
  else equal_node left.node right.node

and equal_node left right =
  match (left, right) with
  | Int left, Int right -> Z.equal left right
  | Decimal left, Decimal right -> Q.equal left right
  | String left, String right -> String.equal left right
  | Set left, Set right ->
      List.length left = List.length right
      && List.for_all
           (fun left -> List.exists (fun right -> equal left.value right.value) right)
           left
  | List left, List right ->
      List.length left = List.length right && List.for_all2 equal left right
  | Edge left, Edge right | UndirectedEdge left, UndirectedEdge right ->
      equal_edge left right
  | Struct (left_name, left_values), Struct (right_name, right_values) ->
      String.equal left_name right_name
      && List.length left_values = List.length right_values
      && List.for_all2 equal left_values right_values
  | Variant (left_enum, left_name, left_values),
    Variant (right_enum, right_name, right_values) ->
      String.equal left_enum right_enum
      && String.equal left_name right_name
      && List.length left_values = List.length right_values
      && List.for_all2 equal left_values right_values
  | _ -> false

and equal_edge left right =
  equal left.left right.left
  && equal left.right right.right
  &&
  match (left.payload, right.payload) with
  | None, None -> true
  | Some left, Some right -> equal left right
  | _ -> false

let add_unique elements value =
  if List.exists (fun element -> equal element.value value) elements then elements
  else elements @ [ { value } ]

let union left right =
  List.fold_left (fun values element -> add_unique values element.value) left right

let intersection left right =
  List.filter
    (fun element ->
      List.exists (fun candidate -> equal element.value candidate.value) right)
    left

let difference left right =
  List.filter
    (fun element ->
      not (List.exists (fun candidate -> equal element.value candidate.value) right))
    left

let set_operation operator left right =
  match operator with
  | Ast.Union -> union left right
  | Ast.Intersection -> intersection left right
  | Ast.Difference -> difference left right

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
      | character -> Buffer.add_char buffer character)
    text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let decimal_string value =
  let numerator = Q.num value and denominator = Q.den value in
  let rec powers value twos fives =
    if Z.equal (Z.erem value (Z.of_int 2)) Z.zero then
      powers (Z.ediv value (Z.of_int 2)) (twos + 1) fives
    else if Z.equal (Z.erem value (Z.of_int 5)) Z.zero then
      powers (Z.ediv value (Z.of_int 5)) twos (fives + 1)
    else (value, twos, fives)
  in
  let remainder, twos, fives = powers denominator 0 0 in
  if not (Z.equal remainder Z.one) then Q.to_string value
  else
    let scale = max twos fives in
    let scaled = Z.ediv (Z.mul numerator (Z.pow (Z.of_int 10) scale)) denominator in
    let negative = Z.sign scaled < 0 in
    let digits = Z.to_string (Z.abs scaled) in
    let digits = String.make (max 0 (scale + 1 - String.length digits)) '0' ^ digits in
    let length = String.length digits in
    let integer = String.sub digits 0 (length - scale) in
    let fraction = if scale = 0 then "0" else String.sub digits (length - scale) scale in
    let rec trim index =
      if index > 1 && fraction.[index - 1] = '0' then trim (index - 1) else index
    in
    let fraction = String.sub fraction 0 (trim (String.length fraction)) in
    (if negative then "-" else "") ^ integer ^ "." ^ fraction

let rec to_string value =
  match value.node with
  | Int value -> Z.to_string value
  | Decimal value -> decimal_string value
  | String value -> quote value
  | Set elements ->
      "{" ^ String.concat ", " (List.map (fun element -> to_string element.value) elements)
      ^ "}"
  | List values -> "[" ^ String.concat ", " (List.map to_string values) ^ "]"
  | Edge edge -> edge_string " -> " " -[" "]-> " edge
  | UndirectedEdge edge -> edge_string " <-> " " <-[" "]-> " edge
  | Struct (name, values) ->
      name ^ "(" ^ String.concat ", " (List.map to_string values) ^ ")"
  | Variant (enum_name, name, []) -> enum_name ^ "::" ^ name
  | Variant (enum_name, name, values) ->
      enum_name ^ "::" ^ name ^ "("
      ^ String.concat ", " (List.map to_string values)
      ^ ")"

and edge_string plain prefix suffix edge =
  match edge.payload with
  | None -> to_string edge.left ^ plain ^ to_string edge.right
  | Some payload ->
      to_string edge.left ^ prefix ^ to_string payload ^ suffix ^ to_string edge.right

let has_coercion (checked : Check.checked) (loc : Ast.loc) =
  List.exists
    (fun (coercion : Ast.loc) ->
      coercion.line = loc.line && coercion.column = loc.column)
    checked.Check.coercions

let error loc message = Error { loc; message }

let ( let* ) = Result.bind

let coerce_undirected loc value =
  match value.node with
  | UndirectedEdge edge ->
      let forward = at (Edge edge) in
      let reverse =
        at (Edge { left = edge.right; right = edge.left; payload = edge.payload })
      in
      Ok
        (at ~marker:(location_marker "coercion" loc)
           (Set (add_unique (add_unique [] forward) reverse)))
  | _ -> error loc "internal coercion site did not evaluate to an UndirectedEdge"

let rec eval checked environment expression =
  let* value = eval_raw checked environment expression in
  if has_coercion checked expression.Ast.loc then coerce_undirected expression.loc value
  else Ok value

and eval_raw checked environment expression =
  let expression_marker = Some (location_marker "value" expression.Ast.loc) in
  match expression.Ast.it with
  | Ast.Int value -> Ok (at ~marker:(Option.get expression_marker) (Int value))
  | Ast.Decimal value -> Ok (at ~marker:(Option.get expression_marker) (Decimal value))
  | Ast.String value -> Ok (at ~marker:(Option.get expression_marker) (String value))
  | Ast.Ref name -> (
      match Hashtbl.find_opt environment name with
      | Some binding -> Ok binding.current
      | None when name = "None" ->
          Ok (at ~marker:(location_marker "variant" expression.loc) (Variant ("Option", "None", [])))
      | None -> error expression.loc ("undefined variable '" ^ name ^ "'"))
  | Ast.Set expressions ->
      let* elements =
        List.fold_left
          (fun result element_expression ->
            let* elements = result in
            let* value = eval checked environment element_expression in
            if has_coercion checked element_expression.loc then
              match value.node with
              | Set coerced -> Ok (union elements coerced)
              | _ -> error element_expression.loc "coercion did not produce a set"
            else Ok (add_unique elements value))
          (Ok []) expressions
      in
      Ok (at ~marker:(location_marker "set" expression.loc) (Set elements))
  | Ast.List expressions ->
      let* values = eval_all checked environment expressions in
      Ok (at ~marker:(location_marker "list" expression.loc) (List values))
  | Ast.SetOp (operator, operands) ->
      eval_operation checked environment expression.loc operator operands
  | Ast.Edge (left, right, payload) ->
      eval_edge checked environment expression.loc false left right payload
  | Ast.UndirectedEdge (left, right, payload) ->
      eval_edge checked environment expression.loc true left right payload
  | Ast.Apply (name, _, arguments) ->
      let* arguments = eval_all checked environment arguments in
      if name = "Some" then
        Ok
          (at ~marker:(location_marker "variant" expression.loc)
             (Variant ("Option", "Some", arguments)))
      else
        Ok
          (at ~marker:(location_marker "struct" expression.loc)
             (Struct (name, arguments)))
  | Ast.Variant (enum_name, name, arguments) ->
      let* arguments = eval_all checked environment arguments in
      Ok
        (at ~marker:(location_marker "variant" expression.loc)
           (Variant (enum_name, name, arguments)))

and eval_all checked environment expressions =
  List.fold_left
    (fun result expression ->
      let* values = result in
      let* value = eval checked environment expression in
      Ok (values @ [ value ]))
    (Ok []) expressions

and eval_edge checked environment loc undirected left right payload =
  let* left = eval checked environment left in
  let* right = eval checked environment right in
  let* () =
    match (left.node, right.node) with
    | Set _, Set _ -> Ok ()
    | _ -> error loc "edge sides must evaluate to sets"
  in
  let* payload =
    match payload with
    | None -> Ok None
    | Some payload ->
        let* payload = eval checked environment payload in
        Ok (Some payload)
  in
  let edge = { left; right; payload } in
  Ok
    (at ~marker:(location_marker "edge" loc)
       (if undirected then UndirectedEdge edge else Edge edge))

and eval_operation checked environment loc operator operands =
  let* values = eval_all checked environment operands in
  match values with
  | [] -> error loc "set operation has no operands"
  | first :: rest ->
      List.fold_left
        (fun result right ->
          let* left = result in
          apply_operation loc operator left right)
        (Ok first) rest

and apply_operation loc operator left right =
  match (left.node, right.node) with
  | Set left_elements, Set right_elements ->
      Ok
        (at ~marker:(Option.value left.marker ~default:(location_marker "set-op" loc))
           (Set (set_operation operator left_elements right_elements)))
  | Edge left_edge, Edge right_edge ->
      let* edge = surgery loc operator left_edge right_edge in
      Ok (at ~marker:(location_marker "edge-op" loc) (Edge edge))
  | UndirectedEdge left_edge, UndirectedEdge right_edge ->
      let* edge = surgery loc operator left_edge right_edge in
      Ok (at ~marker:(location_marker "uedge-op" loc) (UndirectedEdge edge))
  | _ -> error loc "set operator received incompatible runtime values"

and surgery loc operator left right =
  let payloads_equal =
    match (left.payload, right.payload) with
    | None, None -> true
    | Some left, Some right -> equal left right
    | _ -> false
  in
  if not payloads_equal then
    error loc "edge side surgery requires equal payload values"
  else
    match (left.left.node, left.right.node, right.left.node, right.right.node) with
    | Set left_tail, Set left_head, Set right_tail, Set right_head ->
        Ok
          { left = at (Set (set_operation operator left_tail right_tail));
            right = at (Set (set_operation operator left_head right_head));
            payload = left.payload }
    | _ -> error loc "edge side surgery received a non-set side"

let update checked environment name operator expression =
  match Hashtbl.find_opt environment name with
  | None -> error expression.Ast.loc ("undefined variable '" ^ name ^ "'")
  | Some binding when not binding.mutable_ ->
      error expression.loc ("binding '" ^ name ^ "' is immutable")
  | Some binding ->
      let* right = eval checked environment expression in
      let* value = apply_operation expression.loc operator binding.current right in
      binding.current <- { value with marker = binding.current.marker };
      Ok ()

let run checked =
  let environment = Hashtbl.create (List.length checked.Check.bindings) in
  let binding_types =
    List.fold_left
      (fun output (binding : Check.binding) ->
        Check.String_map.add binding.name binding output)
      Check.String_map.empty checked.bindings
  in
  let rec statements = function
    | [] -> Ok environment
    | statement :: rest -> (
        let* () =
          match statement.Ast.it with
          | Ast.Let (name, _, expression) ->
              let* value = eval checked environment expression in
              let checked_binding = Check.String_map.find name binding_types in
              Hashtbl.add environment name
                { mutable_ = checked_binding.mutable_; current = value };
              Ok ()
          | Ast.Update (name, operator, expression) ->
              update checked environment name operator expression
          | Ast.Struct _ | Ast.Enum _ | Ast.Alias _ -> Ok ()
        in
        statements rest)
  in
  statements checked.program

let find environment name =
  Option.map (fun binding -> binding.current) (Hashtbl.find_opt environment name)
