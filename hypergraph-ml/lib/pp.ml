open Ast

type sexp = Atom of string | Quoted of string | Sequence of sexp list

let node tag children = Sequence (Atom tag :: children)
let id (name : identifier) = Quoted name.value
let optional f = function None -> node "none" [] | Some value -> node "some" [f value]

let operator = function
  | Union -> "union"
  | Intersection -> "intersection"
  | Difference -> "difference"

let direction = function
  | Forward -> "forward"
  | Backward -> "backward"
  | Undirected -> "undirected"

let rec type_sexp (typ : typ) =
  match typ.value with
  | Named_type (name, arguments) -> node "type" (id name :: List.map type_sexp arguments)
  | Sum_type (left, right) -> node "sum" [type_sexp left; type_sexp right]

let rec expr_sexp (expr : expr) =
  match expr.value with
  | Int value -> node "int" [Atom value]
  | Decimal value -> node "decimal" [Atom value]
  | String value -> node "string" [Quoted value]
  | Name name -> node "name" [id name]
  | Construct (name, arguments) -> node "construct" (id name :: List.map expr_sexp arguments)
  | Variant (name, variant, arguments) ->
      node "variant" [id name; id variant;
        optional (fun args -> Sequence (List.map expr_sexp args)) arguments]
  | Set values -> node "set" (List.map expr_sexp values)
  | List values -> node "list" (List.map expr_sexp values)
  | Edge { direction = arrow; left; right; payload } ->
      node "edge" [Atom (direction arrow); expr_sexp left;
        optional expr_sexp payload; expr_sexp right]
  | Binary (op, left, right) -> node (operator op) [expr_sexp left; expr_sexp right]

let parameters names = node "parameters" (List.map id names)

let statement_sexp (statement : statement) =
  match statement.value with
  | Struct { name; parameters = params; fields } ->
      node "struct" (id name :: parameters params ::
        List.map (fun field -> node "field" [id field.field_name; type_sexp field.field_type]) fields)
  | Enum { name; parameters = params; variants } ->
      node "enum" (id name :: parameters params ::
        List.map (fun variant -> node "variant" [id variant.variant_name;
          optional (fun args -> Sequence (List.map type_sexp args)) variant.arguments]) variants)
  | Alias { name; parameters = params; body } ->
      node "alias" [id name; parameters params; type_sexp body]
  | Let { name; mutable_; annotation; value } ->
      node "let" [id name; Atom (if mutable_ then "mutable" else "immutable");
        optional type_sexp annotation; expr_sexp value]
  | Update { name; operator = op; value } ->
      node "update" [id name; Atom (operator op); expr_sexp value]

let rec sexp formatter = function
  | Atom text -> Format.pp_print_string formatter text
  | Quoted text -> Format.fprintf formatter "%S" text
  | Sequence items ->
      Format.fprintf formatter "(@[<hov>%a@])"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space sexp) items

let typ formatter value = sexp formatter (type_sexp value)
let expression formatter value = sexp formatter (expr_sexp value)
let program formatter value = sexp formatter (node "program" (List.map statement_sexp value))
