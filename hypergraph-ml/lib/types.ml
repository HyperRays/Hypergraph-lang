type edge_kind = Directed | Undirected

type t =
  | Empty
  | Int
  | Decimal
  | String
  | Parameter of string
  | Variable of string
  | Sum of t list
  | Set of t
  | Option of t
  | Edge of edge_kind * t * t * t
  | Named of string * (string * t) list
  | Opaque of t * t
  | Error

let rec equal left right =
  match (left, right) with
  | Empty, Empty | Int, Int | Decimal, Decimal | String, String | Error, Error -> true
  | Parameter left, Parameter right | Variable left, Variable right -> left = right
  | Sum left, Sum right ->
      List.length left = List.length right && List.for_all2 equal left right
  | Set left, Set right | Option left, Option right -> equal left right
  | Edge (left_kind, left_tail, left_head, left_payload),
    Edge (right_kind, right_tail, right_head, right_payload) ->
      left_kind = right_kind
      && equal left_tail right_tail
      && equal left_head right_head
      && equal left_payload right_payload
  | Named (left_name, left_members), Named (right_name, right_members) ->
      left_name = right_name
      && List.length left_members = List.length right_members
      && List.for_all2
           (fun (left_label, left_type) (right_label, right_type) ->
             left_label = right_label && equal left_type right_type)
           left_members right_members
  | Opaque (left_hidden, left_marker), Opaque (right_hidden, right_marker) ->
      equal left_hidden right_hidden && equal left_marker right_marker
  | _ -> false

let rec flatten_sum output = function
  | [] -> output
  | Empty :: rest -> flatten_sum output rest
  | Sum nested :: rest -> flatten_sum output (nested @ rest)
  | value :: rest -> flatten_sum (value :: output) rest

let sum values =
  let values = List.rev (flatten_sum [] values) in
  let values =
    List.fold_left
      (fun output value ->
        if List.exists (equal value) output then output else output @ [ value ])
      [] values
  in
  match values with [] -> Empty | [ value ] -> value | _ -> Sum values

let summands = function Sum values -> values | Empty -> [] | value -> [ value ]

let rec meet left right =
  if equal left right then left
  else
    match (left, right) with
    | Set left, Set right -> Set (meet left right)
    | _ ->
        let right = summands right in
        summands left
        |> List.filter (fun value -> List.exists (equal value) right)
        |> sum

let apply_set_operator operator left right =
  match operator with
  | Ast.Union -> sum [ left; right ]
  | Ast.Intersection -> meet left right
  | Ast.Difference -> left

let rec substitute parameters ty =
  match ty with
  | Parameter name -> Option.value (List.assoc_opt name parameters) ~default:ty
  | Sum values -> sum (List.map (substitute parameters) values)
  | Set element -> Set (substitute parameters element)
  | Option payload -> Option (substitute parameters payload)
  | Edge (kind, tail, head, payload) ->
      Edge
        (kind, substitute parameters tail, substitute parameters head,
         substitute parameters payload)
  | Named (name, members) ->
      Named
        (name, List.map (fun (label, ty) -> (label, substitute parameters ty)) members)
  | Opaque (hidden, marker) ->
      Opaque (substitute parameters hidden, substitute parameters marker)
  | (Empty | Int | Decimal | String | Variable _ | Error) as ty -> ty

let rec has_variable = function
  | Variable _ -> true
  | Sum values -> List.exists has_variable values
  | Set element | Option element -> has_variable element
  | Edge (_, tail, head, payload) ->
      has_variable tail || has_variable head || has_variable payload
  | Named (_, members) -> List.exists (fun (_, ty) -> has_variable ty) members
  | Opaque (hidden, marker) -> has_variable hidden || has_variable marker
  | Empty | Int | Decimal | String | Parameter _ | Error -> false

let is_edge = function Edge _ -> true | _ -> false

let edge_parts = function
  | Edge (kind, tail, head, payload) -> Some (kind, tail, head, payload)
  | _ -> None

let as_set = function Set element -> Some element | _ -> None

let is_graph = function
  | Set element ->
      let components = summands element in
      components <> [] && List.for_all is_edge components
  | _ -> false

let rec contains_graph ty =
  is_graph ty
  ||
  match ty with
  | Sum values -> List.exists contains_graph values
  | Set element | Option element -> contains_graph element
  | Edge (_, tail, head, payload) ->
      contains_graph tail || contains_graph head || contains_graph payload
  | Named (_, members) -> List.exists (fun (_, ty) -> contains_graph ty) members
  | Opaque _ -> false
  | Empty | Int | Decimal | String | Parameter _ | Variable _ | Error -> false

let rec equality_projection ty =
  match ty with
  | Opaque (_, marker) -> Named ("$OpaqueEq", [ ("marker", marker) ])
  | Sum values -> sum (List.map equality_projection values)
  | Set element -> Set (equality_projection element)
  | Option payload -> Option (equality_projection payload)
  | Edge (kind, tail, head, payload) ->
      Edge
        (kind, equality_projection tail, equality_projection head,
         equality_projection payload)
  | Named (name, members) ->
      Named
        (name, List.map (fun (label, ty) -> (label, equality_projection ty)) members)
  | ty -> ty

let rec protect_graphs marker ty =
  if is_graph ty then Opaque (ty, marker)
  else
    match ty with
    | Sum values -> sum (List.map (protect_graphs marker) values)
    | Set element -> Set (protect_graphs marker element)
    | Option payload -> Option (protect_graphs marker payload)
    | Edge (kind, tail, head, payload) ->
        Edge
          (kind, protect_graphs marker tail, protect_graphs marker head,
           protect_graphs marker payload)
    | Named (name, members) ->
        Named
          (name,
           List.map
             (fun (label, ty) -> (label, protect_graphs marker ty))
             members)
    | Opaque _ as opaque -> opaque
    | (Empty | Int | Decimal | String | Parameter _ | Variable _ | Error) as ty -> ty

let named_term name members =
  let body =
    Solver.constant ("decl:" ^ name)
    :: List.map
         (fun (label, ty) -> Solver.hom ("member:" ^ name ^ ":" ^ label) ty)
         members
  in
  Solver.e (Solver.sum body)

let rec to_solver = function
  | Empty -> Solver.empty
  | Int -> Solver.constant "builtin:Int"
  | Decimal -> Solver.constant "builtin:Decimal"
  | String -> Solver.constant "builtin:String"
  | Parameter name -> Solver.variable ("parameter:" ^ name)
  | Variable name -> Solver.variable name
  | Sum values -> Solver.sum (List.map to_solver values)
  | Set element ->
      Solver.sum
        [ Solver.constant "builtin:Set";
          Solver.hom "set:element" (to_solver element) ]
  | Option payload ->
      named_term "Option"
        [ ("Some:0", to_solver payload); ("None", Solver.empty) ]
  | Edge (kind, tail, head, payload) ->
      let name = match kind with Directed -> "Edge" | Undirected -> "UndirectedEdge" in
      named_term name
        [ ("tail", to_solver (Set tail));
          ("head", to_solver (Set head));
          ("payload", to_solver (Option payload)) ]
  | Named (name, members) ->
      named_term name (List.map (fun (label, ty) -> (label, to_solver ty)) members)
  | Opaque (hidden, marker) ->
      named_term "$Opaque"
        [ ("hide", to_solver hidden); ("marker", to_solver marker) ]
  | Error -> Solver.empty

type relation = Yes | No | Deferred

let combine_relations relations =
  if List.exists (( = ) No) relations then No
  else if List.exists (( = ) Deferred) relations then Deferred
  else Yes

let rec below left right =
  if equal left right || left = Empty || left = Error || right = Error then Yes
  else if has_variable left || has_variable right then Deferred
  else
    match (left, right) with
    | _, Sum choices ->
        summands left
        |> List.map (fun value ->
             if List.exists (fun choice -> below value choice = Yes) choices then Yes else No)
        |> combine_relations
    | Sum values, _ -> List.map (fun value -> below value right) values |> combine_relations
    | Set left, Set right | Option left, Option right -> below left right
    | Edge (left_kind, left_tail, left_head, left_payload),
      Edge (right_kind, right_tail, right_head, right_payload)
      when left_kind = right_kind ->
        combine_relations
          [ below left_tail right_tail; below left_head right_head;
            below left_payload right_payload ]
    | Named (left_name, left_members), Named (right_name, right_members)
      when left_name = right_name && List.length left_members = List.length right_members ->
        List.map2
          (fun (left_label, left_type) (right_label, right_type) ->
            if left_label <> right_label then No else below left_type right_type)
          left_members right_members
        |> combine_relations
    | Opaque (left_hidden, left_marker), Opaque (right_hidden, right_marker) ->
        combine_relations [ below left_hidden right_hidden; below left_marker right_marker ]
    | _ -> No

let rec pretty = function
  | Empty -> "EmptySet"
  | Int -> "Int"
  | Decimal -> "Decimal"
  | String -> "String"
  | Parameter name | Variable name -> name
  | Sum values -> String.concat " + " (List.map pretty values)
  | Set element -> "Set<" ^ pretty element ^ ">"
  | Option payload -> "Option<" ^ pretty payload ^ ">"
  | Edge (kind, tail, head, payload) ->
      let name = match kind with Directed -> "Edge" | Undirected -> "UndirectedEdge" in
      Printf.sprintf "%s<%s, %s, %s>" name (pretty tail) (pretty head)
        (pretty payload)
  | Named (name, _) -> name
  | Opaque (hidden, marker) ->
      Printf.sprintf "Opaque<%s, %s>" (pretty hidden) (pretty marker)
  | Error -> "<error>"
