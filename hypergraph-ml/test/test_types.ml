open Hypergraph

let check name condition = if not condition then failwith name

let () =
  let open Types in
  check "sum idempotence" (equal (sum [ Int; String; Int ]) (Sum [ Int; String ]));
  check "set join"
    (equal
       (apply_set_operator Ast.Union Int String)
       (Sum [ Int; String ]));
  check "set meet"
    (equal
       (apply_set_operator Ast.Intersection (sum [ Int; String ])
          (sum [ Decimal; String ]))
       String);
  check "difference is left typed"
    (equal (apply_set_operator Ast.Difference (sum [ Int; String ]) Decimal)
       (sum [ Int; String ]));
  let edge = Edge (Directed, Int, String, Bottom) in
  let undirected = Edge (Undirected, Int, String, Bottom) in
  check "graph shape" (is_graph (Set (sum [ edge; undirected ])));
  let marker = Named ("marker", []) in
  let left = equality_projection (Opaque (Set edge, marker)) in
  let right = equality_projection (Opaque (Set undirected, marker)) in
  check "opaque equality ignores hidden type" (equal left right);
  let encoded = Format.asprintf "%a" Solver.pp_term (to_solver edge) in
  check "named types use E" (String.length encoded > 2 && encoded.[0] = 'E')
