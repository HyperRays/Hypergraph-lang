open Hypergraph.Solver

let check label condition = if not condition then failwith label
let answer equations = match solve equations with
  | Some value -> value
  | None -> failwith "expected a solution"

let constant = Term.constant
let variable = Term.variable
let ( +! ) = Term.add
let graph term = Graph.normalize term
let assignment solution id term = Graph.equal (Solution.get solution id) (graph term)

let test_algebra () =
  let a = constant 1 and b = constant 2 in
  check "ACUI laws" (Term.equal ((a +! b) +! a) (b +! a));
  check "additive zero" (Term.equal (a +! Term.zero) a);
  check "distinct constants" (not (Term.equal a b));
  check "namespaces" (not (Term.equal a (variable 1)));
  check "inclusion" (Term.below a (a +! b));
  check "inclusion direction" (not (Term.below (a +! b) a));
  check "homomorphism distribution"
    (Term.equal (Term.hom 3 (a +! b)) (Term.hom 3 a +! Term.hom 3 b));
  check "homomorphism zero" (Term.equal (Term.hom 3 Term.zero) Term.zero);
  check "E zero" (Term.equal (Term.free Term.zero) Term.zero);
  check "E does not distribute"
    (not (Term.equal (Term.free (a +! b)) (Term.free a +! Term.free b)));
  check "word order" (not (Term.equal (Term.hom 3 (Term.hom 4 a)) (Term.hom 4 (Term.hom 3 a))));
  check "maximum symbol" (Term.equal (constant max_int) (constant max_int));
  check "distinct maximum symbol" (not (Term.equal (constant max_int) (constant (max_int - 1))))

let test_solve () =
  let a = constant 11 and b = constant 12 and x = variable 0 and y = variable 1 in
  let equations = [|Term.free x, Term.free a; y, Term.hom 5 x|] in
  check "decision" (is_unifiable equations);
  let solution = answer equations in
  check "E cancellation witness" (assignment solution 0 a);
  check "coupled homomorphism witness" (assignment solution 1 (Term.hom 5 a));
  check "absent variable" (assignment solution 999 Term.zero);
  check "unsatisfiable decision" (not (is_unifiable [|x, a; x, b|]));
  check "unsatisfiable result" (Option.is_none (solve [|x, a; x, b|]));
  check "E injectivity" (Option.is_none (solve [|Term.free a, Term.free b|]));
  check "shared homomorphism constraint"
    (is_unifiable [|Term.hom 5 x, Term.hom 5 y|]);
  check "empty problem" (is_unifiable [||]);
  check "empty solution" (assignment (answer [||]) 0 Term.zero);
  let constraints = [|Below (a, x); Equal (x, a +! b)|] in
  check "mixed inclusion decision" (constraints_satisfiable constraints);
  check "mixed inclusion witness" (match solve_constraints constraints with
    | Some solution -> assignment solution 0 (a +! b)
    | None -> false);
  check "inconsistent inclusion" (not (constraints_satisfiable [|Below (a, x); Equal (x, b)|]));
  let sum_solution = answer [|x +! y, a|] in
  let x_value = Graph.to_term (Solution.get sum_solution 0) in
  let y_value = Graph.to_term (Solution.get sum_solution 1) in
  check "nonunique solution satisfies original equation" (Term.equal (x_value +! y_value) a)

let test_layers () =
  check "zero has no layer" (Graph.layer (graph Term.zero) = [||]);
  let a = constant max_int in
  let source = Term.hom 7 (Term.hom 8 (a +! a)) +! variable 2 +! Term.free (constant 3) in
  let normalized = graph source in
  let entries = Graph.layer normalized in
  check "deduplicated layer" (Array.length entries = 3);
  check "constant and word representation" (Array.exists (fun (entry : Graph.summand) ->
    entry.word = [|7; 8|] && match entry.atom with Constant id -> id = max_int | _ -> false) entries);
  check "variable representation" (Array.exists (fun (entry : Graph.summand) ->
    entry.word = [||] && match entry.atom with Variable 2 -> true | _ -> false) entries);
  check "child representation" (Array.exists (fun (entry : Graph.summand) ->
    match entry.atom with Free child -> Graph.equal child (graph (constant 3)) | _ -> false) entries);
  check "graph inclusion" (Graph.below (graph (variable 2)) normalized);
  check "graph round trip" (Term.equal source (Graph.to_term normalized));
  let nested = Term.hom 9 (Term.free (Term.hom 8 (Term.free (a +! constant 4)))) in
  check "nested round trip" (Term.equal nested (Graph.to_term (graph nested)))

let test_lifetimes () =
  let solution = answer [|variable 0, Term.free (constant 42)|] in
  Gc.full_major ();
  Gc.compact ();
  check "solution outlives inputs" (assignment solution 0 (Term.free (constant 42)));
  let child =
    match (Graph.layer (Solution.get solution 0)).(0).atom with
    | Free child -> child
    | _ -> failwith "expected E child"
  in
  Gc.full_major ();
  Gc.compact ();
  check "child outlives layer" (Graph.equal child (graph (constant 42)));
  for i = 1 to 500 do
    let term = Term.free (Term.hom i (constant i +! constant (i + 1))) in
    let s = answer [|variable 0, term|] in
    check "repeated calls" (Term.equal term (Graph.to_term (Solution.get s 0)));
    if i mod 25 = 0 then Gc.compact ()
  done;
  Gc.full_major ()

let test_invalid_ids () =
  let rejects f = try f (); false with Invalid_argument _ -> true in
  check "negative constant" (rejects (fun () -> ignore (constant (-1))));
  check "negative variable" (rejects (fun () -> ignore (variable (-1))));
  check "negative homomorphism" (rejects (fun () -> ignore (Term.hom (-1) Term.zero)));
  check "negative lookup" (rejects (fun () -> ignore (Solution.get (answer [||]) (-1))))

let test_allocating_layer () =
  let settings = Gc.get () in
  Fun.protect ~finally:(fun () -> Gc.set settings) (fun () ->
    Gc.set { settings with minor_heap_size = 4096 };
    let term = ref Term.zero in
    for id = 0 to 599 do term := !term +! Term.constant id done;
    let normalized = graph !term in
    for _ = 1 to 8 do
      let entries = Graph.layer normalized in
      check "large layer length" (Array.length entries = 600);
      let ids = Array.map (fun (entry : Graph.summand) ->
        match entry.atom with Constant id -> id | _ -> failwith "expected constant") entries in
      Array.sort Int.compare ids;
      Array.iteri (fun expected id -> check "large layer value" (expected = id)) ids
    done)

let test_threads () =
  let shared = Term.free (constant 87) in
  let failures = Array.make 4 None in
  let threads = Array.init 4 (fun index -> Thread.create (fun () ->
    try
      for _ = 1 to 30 do
        let solution = answer [|variable index, shared|] in
        check "shared term across threads" (assignment solution index shared)
      done
    with error -> failures.(index) <- Some error) ()) in
  Array.iter Thread.join threads;
  Array.iter (Option.iter raise) failures;
  Gc.full_major ()

let () =
  List.iter (fun (name, test) -> test (); Printf.printf "ok: native %s\n%!" name)
    ["algebra", test_algebra; "solver", test_solve; "graph layers", test_layers;
     "GC and ownership", test_lifetimes; "allocation during layer copying", test_allocating_layer;
     "invalid symbol IDs", test_invalid_ids;
     "system threads", test_threads]
