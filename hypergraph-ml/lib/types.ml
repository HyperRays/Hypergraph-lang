(* Types, and the three judgments that shape them: canonical form, subtyping,
   and how a type is written back out. *)

type ty =
  | TInt
  | TDec
  | TStr
  | TFronce                       (* '#' and '#N' literals *)
  | TEdge of ty option            (* None: plain; Some t: Edge<t> payload *)
  | TUndirectedEdge of ty option
  | TStruct of string * targ list (* nominal, and invariant in its arguments,
                                     so Pair<Int> and Pair<String> never relate *)
  | TGraph                        (* element type of a nested named graph *)
  | TSet of ty list               (* canonical component set; [] is the empty sum *)
  | TParam of string              (* rigid variable, definition-site only *)
  | TUnknown                      (* error recovery *)

(* One type argument of an instantiated struct: a component sum kept as a
   canonical sorted list. 'Bag<Int + String>' has the one argument
   [Int; String], and a single type is the singleton sum. *)
and targ = ty list [@@deriving ord, eq]

(* The derived comparison is NOT OCaml's polymorphic compare, and the
   difference is visible. 'canon' sorts components and the sorted order is
   what gets printed, so 'Graph' must render as
   'Set<Edge> + Set<UndirectedEdge> + Set<Graph>'. That is constructor
   declaration order, which is what both Haskell's derived Ord and
   ppx_deriving.ord give. Polymorphic compare would order every constant
   constructor before every non-constant one, putting TGraph before TEdge and
   changing the rendering. test_types.ml pins it.

   Written by hand first, at 39 lines against Haskell's single 'deriving'
   word, which was most of this file's excess over the original. *)

let equal = equal_ty

(* -- writing a type back out ------------------------------------------------ *)

let rec pretty = function
  | TInt -> "Int"
  | TDec -> "Decimal"
  | TStr -> "String"
  | TFronce -> "Fronce"
  | TEdge None -> "Edge"
  | TEdge (Some t) -> "Edge<" ^ pretty t ^ ">"
  | TUndirectedEdge None -> "UndirectedEdge"
  | TUndirectedEdge (Some t) -> "UndirectedEdge<" ^ pretty t ^ ">"
  | TGraph -> "Graph"
  | TStruct (n, []) -> "struct " ^ n
  | TStruct (n, args) ->
      "struct " ^ n ^ "<" ^ String.concat ", " (List.map pretty_arg args) ^ ">"
  | TParam n -> n
  | TUnknown -> "unknown"
  | TSet [] -> "Set<>"
  | TSet cs -> String.concat " + " (List.map (fun c -> "Set<" ^ pretty c ^ ">") cs)

and pretty_arg a = String.concat " + " (List.map pretty a)

(* -- canonical form --------------------------------------------------------- *)

(* A multi-component TSet is the sum of its single-component sets, which is
   what 'pretty' renders as 'Set<A> + Set<B>'. A component that is itself such
   a set is therefore a sum standing in an element slot, and it gets spliced
   back out. These two are equal by F(A + B) = F(A) + F(B), but only the second
   lets 'embed' see the 'Set<Edge>' summand and abstract it to 'Graph', so
   splicing is what makes both spellings converge.

       Set<Set<Edge + Int>>          one component
       Set<Set<Edge> + Set<Int>>     two *)
let distribute = function
  | TSet cs when List.length cs > 1 -> List.map (fun c -> TSet [ c ]) cs
  | t -> [ t ]

(* Sorted, deduplicated, no error placeholders, every component distributed.
   Sorting before removing duplicates is the same answer as Haskell's nub
   then sort, and cheaper. *)
let canon_components components =
  let rec dedup = function
    | a :: (b :: _ as rest) -> if equal a b then dedup rest else a :: dedup rest
    | rest -> rest
  in
  components
  |> List.concat_map distribute
  |> List.filter (fun t -> not (equal t TUnknown))
  |> List.sort compare_ty |> dedup

let canon components = TSet (canon_components components)

(* One type argument of an instantiated struct, canonicalised the same way but
   left as a list, since an argument is a component sum rather than a set. *)
let arg_canon = canon_components

(* -- graph shape ------------------------------------------------------------ *)

(* Edge-shaped components, annotated or not. *)
let is_edgy = function
  | TEdge _ | TUndirectedEdge _ | TGraph -> true
  | _ -> false

(* A graph type: a non-empty set whose components are all edge-shaped. *)
let is_graph_set = function
  | TSet cs -> cs <> [] && List.for_all is_edgy cs
  | _ -> false

(* Element types are abstracted at the graph boundary. A graph-typed element
   contributes the nominal component 'Graph' and never its precise type, which
   is what keeps comparison from descending into a graph. *)
let embed t = if is_graph_set t then TGraph else t

(* -- subtyping -------------------------------------------------------------- *)

(* Exactly three rules: width on component sets, the empty sum below every set
   type, and UndirectedEdge <: Set<Edge> with the payload preserved. Annotated
   and plain edges are unrelated, since annotations are invariant throughout.

   The empty sum needs no case of its own. 'TSet []' has no components, so the
   width rule's "every component of the left has a supertype on the right" is
   vacuously true against any set. *)
let rec sub a b =
  match (a, b) with
  | TUnknown, _ | _, TUnknown -> true
  | _ when equal a b -> true
  | TUndirectedEdge ann, _ -> sub (TSet [ TEdge ann ]) b
  | TSet aa, TSet bb -> List.for_all (fun x -> List.exists (sub x) bb) aa
  | _ -> false
