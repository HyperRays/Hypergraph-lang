(* The laws of model/lattice.hg, checked against types.ml directly.

   That model was written against the Rust and Haskell implementation and
   states what the sum lattice does independently of who implements it, which
   makes it the right oracle for this port. Rows here are its rows: the
   normal-form classes, the generating subtype steps, and the pairs it refuses.

   The two rendered strings are quoted from what the existing checker actually
   prints, so the canonical ORDER is pinned and not just the component set. *)

open Hypergraph.Types

let failures = ref 0

let check name expected got =
  if expected <> got then (
    incr failures;
    Printf.printf "FAIL %s\n  expected: %s\n  got:      %s\n" name expected got)

let yes name b = if not b then (incr failures; Printf.printf "FAIL %s: expected true\n" name)
let no name b = if b then (incr failures; Printf.printf "FAIL %s: expected false\n" name)

let graph_components = [ TEdge None; TUndirectedEdge None; TGraph ]

let () =
  (* -- normal forms, from lattice.hg's 'norm' classes -- *)

  (* canon takes COMPONENTS, so 'Set<Int + String>' is the one-set case and
     its components are Int and String. *)
  check "components" "Set<Int> + Set<String>" (pretty (canon [ TInt; TStr ]));

  (* distribute: a component that is itself a multi-component set is a sum in
     an element slot, and splicing makes the two spellings of it converge.
     lattice.hg's law about written syntax lives one level up, in the
     interpreter that turns a tsyn into components; this is the same law at
     the level canon works on. *)
  check "distribute/nested-sum" "Set<Set<Int>> + Set<Set<String>>"
    (pretty (canon [ TSet [ TInt; TStr ] ]));
  check "distribute/already-split" "Set<Set<Int>> + Set<Set<String>>"
    (pretty (canon [ TSet [ TInt ]; TSet [ TStr ] ]));
  check "distribute/converges" "true"
    (string_of_bool
       (equal (canon [ TSet [ TInt; TStr ] ]) (canon [ TSet [ TInt ]; TSet [ TStr ] ])));

  (* and it is what lets embed see a Set<Edge> summand to abstract. *)
  check "distribute/exposes-graph" "Set<Set<Int>> + Set<Set<Edge>>"
    (pretty (canon [ TSet [ TEdge None; TInt ] ]));

  (* unordered: components come back in one canonical order however written,
     and that order is constructor declaration order, not alphabetical. *)
  check "unordered/a" "Set<Int> + Set<Decimal> + Set<String>"
    (pretty (canon [ TInt; TStr; TDec ]));
  check "unordered/b" "Set<Int> + Set<Decimal> + Set<String>"
    (pretty (canon [ TStr; TDec; TInt ]));
  check "unordered/c" "Set<Int> + Set<Decimal> + Set<String>"
    (pretty (canon [ TDec; TInt; TStr ]));

  (* idempotent *)
  check "idempotent/outer" "Set<Int>" (pretty (canon [ TInt; TInt ]));
  check "idempotent/nested" "Set<Set<Int>>"
    (pretty (canon [ TSet [ TInt ]; TSet [ TInt ] ]));

  (* sugar: what 'Graph' expands to, in the order the checker prints it. *)
  check "sugar/graph" "Set<Edge> + Set<UndirectedEdge> + Set<Graph>"
    (pretty (canon graph_components));

  (* bottom *)
  check "bottom/empty" "Set<>" (pretty (canon []));

  (* error placeholders never reach a canonical form *)
  check "canon/drops-unknown" "Set<Int>" (pretty (canon [ TUnknown; TInt ]));

  (* -- the order, from lattice.hg's generating steps -- *)

  yes "reflexive" (sub (TSet [ TInt ]) (TSet [ TInt ]));
  yes "width" (sub (TSet [ TInt ]) (TSet [ TInt; TStr ]));
  yes "bottom" (sub (TSet []) (canon graph_components));
  yes "coerce" (sub (TUndirectedEdge None) (TSet [ TEdge None ]));
  yes "coerce/payload-preserved"
    (sub (TUndirectedEdge (Some TInt)) (TSet [ TEdge (Some TInt) ]));

  (* two width steps compose, which is lattice.hg's 'derived' row *)
  yes "transitive"
    (sub (TSet [ TInt ]) (TSet [ TInt; TStr; TDec ]));

  (* -- and the pairs it refuses -- *)

  no "width is one-way" (sub (TSet [ TInt; TStr ]) (TSet [ TInt ]));
  no "coerce is one-way" (sub (TSet [ TEdge None ]) (TUndirectedEdge None));
  no "unrelated" (sub (TSet [ TInt ]) (TSet [ TStr ]));
  no "payload invariance/annotated-to-plain"
    (sub (TSet [ TEdge (Some TInt) ]) (TSet [ TEdge None ]));
  no "payload invariance/plain-to-annotated"
    (sub (TSet [ TEdge None ]) (TSet [ TEdge (Some TInt) ]));
  no "struct invariance"
    (sub (TStruct ("P", [ [ TInt ] ])) (TStruct ("P", [ [ TStr ] ])));

  (* unknown relates to everything, for error recovery *)
  yes "unknown/left" (sub TUnknown (TSet [ TInt ]));
  yes "unknown/right" (sub (TSet [ TInt ]) TUnknown);

  (* -- graph shape -- *)

  yes "is_graph_set" (is_graph_set (TSet graph_components));
  no "is_graph_set/empty" (is_graph_set (TSet []));
  no "is_graph_set/mixed" (is_graph_set (TSet [ TEdge None; TInt ]));
  check "embed/abstracts" "Graph" (pretty (embed (TSet [ TEdge None ])));
  check "embed/leaves-others" "Set<Int>" (pretty (embed (TSet [ TInt ])));

  (* -- rendering the rest -- *)

  check "pretty/struct" "struct P" (pretty (TStruct ("P", [])));
  check "pretty/struct-args" "struct P<Int + String, Decimal>"
    (pretty (TStruct ("P", [ [ TInt; TStr ]; [ TDec ] ])));
  check "pretty/edge-payload" "Edge<Int>" (pretty (TEdge (Some TInt)));
  check "pretty/param" "T" (pretty (TParam "T"));
  check "pretty/unknown" "unknown" (pretty TUnknown);

  if !failures = 0 then print_endline "types: OK"
  else (Printf.printf "types: %d FAILED\n" !failures; exit 1)
