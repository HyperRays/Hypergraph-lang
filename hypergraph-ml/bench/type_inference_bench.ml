open Hypergraph

type workload = Simple_bindings | Generic_chain | Wide_set | Solver_chain

type measurement = {
  iterations : int;
  median_ms : float;
  p95_ms : float;
  mean_ms : float;
  min_ms : float;
  allocated_mib : float;
}

let workload_name = function
  | Simple_bindings -> "simple_bindings"
  | Generic_chain -> "generic_chain"
  | Wide_set -> "wide_set"
  | Solver_chain -> "solver_chain"

let parse_workload = function
  | "simple_bindings" -> Simple_bindings
  | "generic_chain" -> Generic_chain
  | "wide_set" -> Wide_set
  | "solver_chain" -> Solver_chain
  | name -> invalid_arg ("unknown workload '" ^ name ^ "'")

let simple_bindings size =
  let output = Buffer.create (size * 20) in
  for index = 0 to size - 1 do
    Printf.bprintf output "let value_%d = %d\n" index index
  done;
  Buffer.contents output

let generic_chain size =
  let output = Buffer.create (size * 80) in
  Buffer.add_string output
    {|
enum Deferred<A> {
  Present(A),
  Missing,
}
struct Same<A> {
  left: Deferred<A>,
  right: Deferred<A>,
}
let node_0 = Deferred::Present(0)
|};
  for index = 1 to size do
    Printf.bprintf output "let node_%d = Deferred::Missing\n" index;
    Printf.bprintf output "let link_%d = Same(node_%d, node_%d)\n" index
      (index - 1) index
  done;
  Buffer.contents output

let wide_set size =
  let output = Buffer.create (size * 75) in
  for index = 0 to size - 1 do
    Printf.bprintf output "struct Item_%d { value: Int, }\n" index
  done;
  for index = 0 to size - 1 do
    Printf.bprintf output "let item_%d = Item_%d(%d)\n" index index index
  done;
  Buffer.add_string output "let all_items = {\n";
  for index = 0 to size - 1 do
    Printf.bprintf output "  item_%d,\n" index
  done;
  Buffer.add_string output "}\n";
  Buffer.contents output

let source workload size =
  if size < 1 then invalid_arg "workload size must be positive";
  match workload with
  | Simple_bindings -> simple_bindings size
  | Generic_chain -> generic_chain size
  | Wide_set -> wide_set size
  | Solver_chain -> invalid_arg "solver_chain has no source document"

let fail_parse error =
  failwith
    (Printf.sprintf "parse error at %d:%d: %s" error.Driver.line error.column
       error.message)

let parse text = match Driver.parse text with Ok ast -> ast | Error error -> fail_parse error

let consume = function
  | Ok checked -> List.length checked.Check.bindings
  | Error diagnostics ->
      failwith
        (String.concat "; "
           (List.map
              (fun (diagnostic : Check.diagnostic) ->
                Printf.sprintf "%d:%d: %s" diagnostic.loc.line diagnostic.loc.column
                  diagnostic.message)
              diagnostics))

let elapsed action iterations =
  let allocated_before = Gc.allocated_bytes () in
  let started = Unix.gettimeofday () in
  let checksum = ref 0 in
  for _ = 1 to iterations do
    checksum := !checksum + action ()
  done;
  let duration = Unix.gettimeofday () -. started in
  let allocated = Gc.allocated_bytes () -. allocated_before in
  if !checksum < 0 then invalid_arg "unreachable checksum";
  (duration, allocated)

let batch_size action =
  let target_seconds = 0.075 in
  let rec choose iterations =
    let duration, _ = elapsed action iterations in
    if duration >= target_seconds || iterations >= 65_536 then iterations
    else choose (iterations * 2)
  in
  choose 1

let percentile sorted fraction =
  let count = Array.length sorted in
  let index = min (count - 1) (int_of_float (ceil (fraction *. float count)) - 1) in
  sorted.(max 0 index)

let measure action =
  ignore (action ());
  ignore (action ());
  let iterations = batch_size action in
  Gc.compact ();
  let samples =
    Array.init 15 (fun _ ->
        let duration, allocated = elapsed action iterations in
        (duration /. float iterations, allocated /. float iterations))
  in
  let timings = Array.map fst samples in
  Array.sort Float.compare timings;
  let allocations = Array.fold_left (fun total (_, value) -> total +. value) 0. samples in
  { iterations;
    median_ms = percentile timings 0.50 *. 1_000.;
    p95_ms = percentile timings 0.95 *. 1_000.;
    mean_ms = Array.fold_left ( +. ) 0. timings /. 15. *. 1_000.;
    min_ms = timings.(0) *. 1_000.;
    allocated_mib = allocations /. 15. /. 1_048_576. }

let print_measurement workload size source_bytes mode measurement =
  Printf.printf "%s,%d,%d,%s,%d,%.6f,%.6f,%.6f,%.6f,%.6f\n%!"
    (workload_name workload) size source_bytes mode measurement.iterations
    measurement.median_ms measurement.p95_ms measurement.mean_ms measurement.min_ms
    measurement.allocated_mib

let solver_chain size =
  let variable index = Solver.variable (Printf.sprintf "control:%d" index) in
  let link index = Solver.variable (Printf.sprintf "control-link:%d" index) in
  let constraints = ref [ Solver.Equal (variable 0, Types.to_solver Types.Int) ] in
  for index = 1 to size do
    constraints := Solver.Equal (variable (index - 1), link index) :: !constraints;
    constraints := Solver.Equal (variable index, link index) :: !constraints
  done;
  let constraints = List.rev !constraints in
  let action () =
    match Solver.solve constraints with
    | Ok (Solver.Sat assignment) -> List.length assignment
    | Ok Solver.Unsat -> failwith "control solver chain was unexpectedly unsatisfiable"
    | Error error -> failwith ("solver error: " ^ error.message)
  in
  print_measurement Solver_chain size 0 "solver" (measure action)

let benchmark ~inference_only argument =
  let workload_name, size =
    match String.split_on_char ':' argument with
    | [ workload; size ] -> (workload, int_of_string size)
    | _ -> invalid_arg ("expected WORKLOAD:SIZE, got '" ^ argument ^ "'")
  in
  let workload = parse_workload workload_name in
  match workload with
  | Solver_chain -> solver_chain size
  | Simple_bindings | Generic_chain | Wide_set ->
      let text = source workload size in
      let ast = parse text in
      let inference () = consume (Check.check ast) in
      let parse_and_infer () = consume (Check.check (parse text)) in
      print_measurement workload size (String.length text) "inference"
        (measure inference);
      if not inference_only then
        print_measurement workload size (String.length text) "parse_and_infer"
          (measure parse_and_infer)

let () =
  if Array.length Sys.argv < 2 then (
    prerr_endline
      "usage: type_inference_bench.exe [--inference-only] WORKLOAD:SIZE ...";
    exit 2);
  let inference_only = ref false in
  print_endline
    "workload,size,source_bytes,mode,batch_iterations,median_ms,p95_ms,mean_ms,min_ms,allocated_mib";
  for index = 1 to Array.length Sys.argv - 1 do
    if String.equal Sys.argv.(index) "--inference-only" then inference_only := true
    else benchmark ~inference_only:!inference_only Sys.argv.(index)
  done
