type identifier = string Location.located

type typ = typ_desc Location.located
and typ_desc =
  | Named_type of identifier * typ list
  | Sum_type of typ * typ

type set_operator = Union | Intersection | Difference
type direction = Forward | Backward | Undirected

type expr = expr_desc Location.located
and expr_desc =
  (* Keep the source spelling: machine ints/floats would lose precision. *)
  | Int of string
  | Decimal of string
  | String of string
  | Name of identifier
  | Construct of identifier * expr list
  | Variant of identifier * identifier * expr list option
  | Set of expr list
  | List of expr list
  | Edge of {
      direction : direction;
      left : expr;
      right : expr;
      payload : expr option;
    }
  | Binary of set_operator * expr * expr

type field = {
  field_name : identifier;
  field_type : typ;
  loc : Location.t;
}

type variant = {
  variant_name : identifier;
  arguments : typ list option;
  loc : Location.t;
}

type statement = statement_desc Location.located
and statement_desc =
  | Struct of {
      name : identifier;
      parameters : identifier list;
      fields : field list;
    }
  | Enum of {
      name : identifier;
      parameters : identifier list;
      variants : variant list;
    }
  | Alias of {
      name : identifier;
      parameters : identifier list;
      body : typ;
    }
  | Let of {
      name : identifier;
      mutable_ : bool;
      annotation : typ option;
      value : expr;
    }
  | Update of {
      name : identifier;
      operator : set_operator;
      value : expr;
    }

type program = statement list
