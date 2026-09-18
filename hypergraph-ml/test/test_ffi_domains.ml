open Hypergraph.Solver

let () =
  let shared_term = Term.free (Term.hom 7 (Term.constant 42)) in
  let shared_solution = match solve [|Term.variable 0, shared_term|] with
    | Some result -> result
    | None -> failwith "expected a solution"
  in
  let domains = Array.init 4 (fun index -> Domain.spawn (fun () ->
    for _ = 1 to 50 do
      let graph = Solution.get shared_solution 0 in
      if not (Term.equal (Graph.to_term graph) shared_term) then failwith "shared solution";
      let temporary = Term.hom index (Term.constant index) in
      if not (is_unifiable [|Term.variable index, temporary|]) then failwith "parallel solver";
      if index = 0 then Gc.compact ()
    done;
    Graph.normalize (Term.constant index))) in
  let graphs = Array.map Domain.join domains in
  Gc.full_major ();
  Array.iteri (fun index graph ->
    if not (Graph.equal graph (Graph.normalize (Term.constant index))) then
      failwith "graph outlives originating domain") graphs;
  Printf.printf "ok: native OCaml domains and cross-domain ownership\n%!"
