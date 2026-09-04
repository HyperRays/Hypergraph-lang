type problem = { loc : Ast.loc; message : string }

let describe expression =
  match expression.Ast.it with
  | Ast.Int _ -> "an integer"
  | Ast.Decimal _ -> "a decimal"
  | Ast.String _ -> "a string"
  | Ast.Apply (name, _, _) -> "a " ^ name ^ " value"
  | Ast.Variant (name, variant, _) -> name ^ "::" ^ variant
  | Ast.Edge _ -> "an edge"
  | Ast.UndirectedEdge _ -> "an undirected edge"
  | Ast.Set _ | Ast.Ref _ | Ast.SetOp _ -> "a set expression"

let require_set problems context expression =
  if Ast.set_shaped expression then problems
  else
    { loc = expression.Ast.loc;
      message =
        describe expression ^ " cannot be " ^ context
        ^ "; this position requires a set expression" }
    :: problems

let rec expression problems value =
  let problems =
    match value.Ast.it with
    | Ast.SetOp (operator, operands) ->
        List.fold_left
          (fun problems operand ->
            require_set problems
              ("an operand of '" ^ Ast.op_symbol operator ^ "'") operand)
          problems operands
    | Ast.Edge (tail, head, _) ->
        require_set
          (require_set problems "the tail of an edge" tail)
          "the head of an edge" head
    | Ast.UndirectedEdge (left, right, _) ->
        require_set
          (require_set problems "a side of an undirected edge" left)
          "a side of an undirected edge" right
    | _ -> problems
  in
  match value.Ast.it with
  | Ast.Int _ | Ast.Decimal _ | Ast.String _ | Ast.Ref _ -> problems
  | Ast.Set values | Ast.SetOp (_, values) | Ast.Apply (_, _, values)
  | Ast.Variant (_, _, values) -> List.fold_left expression problems values
  | Ast.Edge (left, right, payload) | Ast.UndirectedEdge (left, right, payload) ->
      List.fold_left expression problems
        (left :: right :: Option.to_list payload)

let statement problems statement =
  match statement.Ast.it with
  | Ast.Let (_, _, value) -> expression problems value
  | Ast.Update (name, operator, value) ->
      let problems =
        match value.Ast.it with
        | Ast.Edge _ | Ast.UndirectedEdge _ -> problems
        | _ ->
            require_set problems
              ("the right side of '" ^ name ^ " " ^ Ast.op_symbol operator ^ "='")
              value
      in
      expression problems value
  | Ast.Struct _ | Ast.Enum _ | Ast.Alias _ -> problems

let check program =
  match
    List.fold_left statement [] program
    |> List.sort (fun left right ->
         compare (left.loc.line, left.loc.column) (right.loc.line, right.loc.column))
  with
  | [] -> None
  | first :: _ -> Some first
