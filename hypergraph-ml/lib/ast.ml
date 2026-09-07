type loc = { line : int; column : int }

type 'a located = { it : 'a; loc : loc }

let at loc it = { it; loc }

type setop = Union | Intersection | Difference

type ty = ty_node located

and ty_node =
  | TyName of string
  | TyApply of string * ty list
  | TySum of ty list

type annotation = { mutable_ : bool; ty : ty }

type expr = expr_node located

and expr_node =
  | Int of Z.t
  | Decimal of Q.t
  | String of string
  | Ref of string
  | Set of expr list
  | List of expr list
  | SetOp of setop * expr list
  | Edge of expr * expr * expr option
  | UndirectedEdge of expr * expr * expr option
  | Apply of string * ty option list option * expr list
  | Variant of string * string * expr list

type field = { field_name : string; field_type : ty; field_loc : loc }

type variant = {
  variant_name : string;
  variant_payload : ty list;
  variant_loc : loc;
}

type stmt = stmt_node located

and stmt_node =
  | Let of string * annotation option * expr
  | Update of string * setop * expr
  | Struct of string * string list * field list
  | Enum of string * string list * variant list
  | Alias of string * string list * ty

type program = stmt list

let op_symbol = function
  | Union -> "|"
  | Intersection -> "&"
  | Difference -> "-"

let set_shaped expression =
  match expression.it with Set _ | Ref _ | SetOp _ -> true | _ -> false

let operator_shaped expression =
  match expression.it with
  | Set _ | Ref _ | SetOp _ | Edge _ | UndirectedEdge _ -> true
  | _ -> false

exception Mixed_ops of setop * setop * loc

let rec string_of_type ty =
  match ty.it with
  | TyName name -> name
  | TyApply (name, arguments) ->
      name ^ "<" ^ String.concat ", " (List.map string_of_type arguments) ^ ">"
  | TySum summands -> String.concat " + " (List.map string_of_type summands)
