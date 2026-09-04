open Hypergraph

let fail_error (error : Solver.error) = failwith error.message

let expect_sat = function
  | Ok (Solver.Sat assignment) -> assignment
  | Ok Solver.Unsat -> failwith "expected SAT, got UNSAT"
  | Error error -> fail_error error

let expect_unsat = function
  | Ok Solver.Unsat -> ()
  | Ok (Solver.Sat _) -> failwith "expected UNSAT, got SAT"
  | Error error -> fail_error error

let () =
  let open Solver in
  let x = variable "X" and a = constant "A" and b = constant "B" in
  let constraints = [ Equal (x, sum [ a; b ]); Below (a, x) ] in
  let assignment = expect_sat (solve constraints) in
  (match check_assignment constraints assignment with
   | Ok true -> ()
   | Ok false -> failwith "Lean rejected its returned assignment"
   | Error error -> fail_error error);

  expect_unsat (solve [ Equal (a, b) ]);
  let undirected = e (sum [ constant "UndirectedEdge"; hom "tail" a ]) in
  let directed_set = sum [ constant "Set"; hom "element" (e (constant "Edge")) ] in
  let rule = of_subsumption ~lower:undirected ~upper:directed_set in
  ignore (expect_sat (solve ~rules:[ rule ] []));

  let malformed =
    `Assoc
      [ ("version", `Int 1); ("operation", `String "solve");
        ("constants", `Int 0); ("variables", `Int 0);
        ("homomorphisms", `Int 0); ("rules", `List []);
        ( "constraints",
          `List
            [ `Assoc
                [ ("kind", `String "below");
                  ("left", `Assoc [ ("tag", `String "const"); ("id", `Int 4) ]);
                  ("right", `Assoc [ ("tag", `String "zero") ]) ] ] ) ]
  in
  match Lean_bridge.invoke malformed with
  | Error _ -> ()
  | Ok _ -> failwith "malformed finite index was accepted"
