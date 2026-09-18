module Term = struct
  type t
  external make_zero : unit -> t = "caml_acuihe_zero"
  let zero = make_zero ()
  external constant : int -> t = "caml_acuihe_constant"
  external variable : int -> t = "caml_acuihe_variable"
  external add : t -> t -> t = "caml_acuihe_add"
  external hom : int -> t -> t = "caml_acuihe_hom"
  external free : t -> t = "caml_acuihe_free"
  external equal : t -> t -> bool = "caml_acuihe_equal"
  external below : t -> t -> bool = "caml_acuihe_below"
end

module Graph = struct
  type t
  type atom = Constant of int | Variable of int | Free of t
  type summand = { word : int array; atom : atom }
  external normalize : Term.t -> t = "caml_acuihe_normalize"
  external equal : t -> t -> bool = "caml_acuihe_graph_equal"
  external below : t -> t -> bool = "caml_acuihe_graph_below"
  external layer : t -> summand array = "caml_acuihe_graph_layer"

  let rec to_term graph =
    Array.fold_left (fun result { word; atom } ->
      let base = match atom with
        | Constant id -> Term.constant id
        | Variable id -> Term.variable id
        | Free child -> Term.free (to_term child)
      in
      let summand = Array.fold_right Term.hom word base in
      Term.add result summand) Term.zero (layer graph)
end

module Solution = struct
  type t
  external get : t -> int -> Graph.t = "caml_acuihe_solution_get"
end

type equation = Term.t * Term.t
external solve : equation array -> Solution.t option = "caml_acuihe_solve"
external is_unifiable : equation array -> bool = "caml_acuihe_is_unifiable"

type constraint_ = Equal of Term.t * Term.t | Below of Term.t * Term.t

let equations_of_constraints = Array.map (function
  | Equal (left, right) -> left, right
  | Below (left, right) -> Term.add left right, right)

let solve_constraints constraints = solve (equations_of_constraints constraints)
let constraints_satisfiable constraints = is_unifiable (equations_of_constraints constraints)
