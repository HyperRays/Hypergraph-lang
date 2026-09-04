(* Two restrictions the grammar states by having narrower nonterminals in three
   positions, checked here instead.

     set_atom = set | var_name | '(' set_expr ')'    (operands and edge sides)
     ext_rhs  = edge_expr | set_expr

   Writing those as separate nonterminals would make the parser ambiguous,
   since '(x)' could reduce either way and no lookahead settles which. The
   grammar therefore accepts the wider form and this pass rejects what the
   narrower one would have. That is the same shape as the mixed-operator rule,
   which also parses broadly so the error can name the operators rather than
   describe a parser state.

   The AST keeps enough to decide all three. A parenthesised expression leaves
   no trace, so '(3339)' is an Int wherever it appears, and an operand that is
   an Int was never set-shaped however it was spelled. *)

type problem = { loc : Ast.loc; what : string; why : string }

let set_shaped = Ast.set_shaped

let describe (n : Ast.node) =
  match n.it with
  | Ast.Int _ -> "an integer"
  | Ast.Dec _ -> "a decimal"
  | Ast.Str _ -> "a string"
  | Ast.Fronce _ -> "a fronce token"
  | Ast.Init (name, _, _) -> "a " ^ name ^ " value"
  | Ast.Edge _ -> "an edge"
  | Ast.UEdge _ -> "an undirected edge"
  | Ast.Set _ | Ast.Ref _ | Ast.Op _ -> "a set"

let require_set_shaped acc where why node =
  if set_shaped node then acc
  else { loc = node.Ast.loc; what = describe node ^ " " ^ where; why } :: acc

let rec node acc (n : Ast.node) =
  let acc =
    match n.it with
    | Ast.Op (op, operands) ->
        List.fold_left
          (fun acc o ->
            require_set_shaped acc
              ("as an operand of '" ^ Ast.op_symbol op ^ "'")
              "set operators combine sets, so each operand must be a set, a \
               name, or a parenthesised set expression"
              o)
          acc operands
    (* Both sides of an arrow are set expressions. The payload is not, so
       'a -[5]-> b' is fine while '5 -> b' is not. *)
    | Ast.Edge (a, b, _) | Ast.UEdge (a, b, _) ->
        List.fold_left
          (fun acc side ->
            require_set_shaped acc "as a side of an edge"
              "an edge joins sets of vertices, so each side must be a set, a \
               name, or a parenthesised set expression"
              side)
          acc [ a; b ]
    | _ -> acc
  in
  children acc n

and children acc (n : Ast.node) =
  match n.it with
  | Ast.Int _ | Ast.Dec _ | Ast.Str _ | Ast.Ref _ | Ast.Fronce _ -> acc
  | Ast.Set xs | Ast.Op (_, xs) | Ast.Init (_, _, xs) ->
      List.fold_left node acc xs
  | Ast.Edge (a, b, ann) | Ast.UEdge (a, b, ann) ->
      let acc = node (node acc a) b in
      Option.fold ~none:acc ~some:(node acc) ann

let stmt acc (s : Ast.stmt) =
  match s.it with
  | Ast.SLet (_, _, v) -> node acc v
  | Ast.SExt (name, op, rhs) ->
      let acc =
        match rhs.it with
        | Ast.Edge _ | Ast.UEdge _ -> acc
        | _ ->
            require_set_shaped acc
              ("on the right of '" ^ Ast.op_symbol op ^ "='")
              ("'" ^ name ^ " " ^ Ast.op_symbol op
             ^ "= ...' extends a set or edits an edge, so the right side must \
                be a set or an edge")
              rhs
      in
      node acc rhs
  | Ast.SStruct _ | Ast.SType _ -> acc

(* The earliest problem in the source, which is the one a reader fixes first.
   Later ones are often consequences of it. *)
let check (p : Ast.program) : problem option =
  match List.fold_left stmt [] p with
  | [] -> None
  | problems ->
      Some
        (List.hd
           (List.sort
              (fun a b -> compare (a.loc.line, a.loc.column) (b.loc.line, b.loc.column))
              problems))
