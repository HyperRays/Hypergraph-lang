import ACUIhE.FILO.Choices.Search

/-!
# Finite indexing for the shared status search

Structured component names are translated once to integer indices. This is a
representation change around the same propagation/search implementation, not
a second solver. Decoding recovers every classification on the original names.
-/

namespace ACUIhE.FILO.Choices.Indexing

open Components
universe v w z
variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def names (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom)) :
    List (Variable Var Hom) := (ns ++ cs.flatMap Clause.variables).dedup

theorem mem_names {ns : List (Variable Var Hom)} {cs : List (Clause Var Hom)}
    {x : Variable Var Hom} (hx : x ∈ ns) : x ∈ names ns cs :=
  List.mem_dedup.mpr (List.mem_append_left _ hx)

theorem variable_mem_names {ns : List (Variable Var Hom)} {cs : List (Clause Var Hom)}
    {q : Clause Var Hom} (hq : q ∈ cs) {x : Variable Var Hom} (hx : x ∈ q.variables) :
    x ∈ names ns cs :=
  List.mem_dedup.mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hx⟩))

def literal (ns : List (Variable Var Hom)) (l : Literal Var Hom) : Literal Nat Empty :=
  ⟨match l.atom with
    | .const a => .const a
    | .var x => .var (.base (ns.idxOf x)), l.allowed⟩

def encode (ns : List (Variable Var Hom)) (c : Choice Var Hom) : Choice Nat Empty
  | .base i => (ns[i]?.map c).getD .top
  | _ => .top

def decode (ns : List (Variable Var Hom)) (c : Choice Nat Empty) : Choice Var Hom :=
  fun x => c (.base (ns.idxOf x))

theorem encode_decode (ns : List (Variable Var Hom)) (c : Choice Var Hom)
    {x : Variable Var Hom} (hx : x ∈ ns) : decode ns (encode ns c) x = c x := by
  simp only [decode, encode, List.getElem?_idxOf hx, Option.map_some, Option.getD_some]

theorem literal_holds (ns : List (Variable Var Hom)) (c : Choice Var Hom) (l : Literal Var Hom)
    (hn : ∀ x, l.atom = .var x → x ∈ ns) :
    (literal ns l).Holds (encode ns c) ↔ l.Holds c := by
  cases he : l.atom with
  | const a => simp only [literal, Literal.Holds, atomStatus, he]
  | var x =>
    simp only [literal, Literal.Holds, atomStatus, he, encode,
      List.getElem?_idxOf (hn x he), Option.map_some, Option.getD_some]

def context (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom)) : Context Nat Empty :=
  Context.build ((List.range ns.length).map Variable.base) (cs.map (List.map (literal ns)))

theorem index_mem_context (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom))
    {x : Variable Var Hom} (hx : x ∈ ns) :
    Variable.base (ns.idxOf x) ∈ (context ns cs).names :=
  Context.mem_build_names (List.mem_map.mpr
    ⟨ns.idxOf x, List.mem_range.mpr (List.idxOf_lt_length_of_mem hx), rfl⟩)

theorem context_holds (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom))
    (c : Choice Var Hom) (h : ∀ q ∈ cs, q.Holds c) :
    (context (names ns cs) cs).Holds (encode (names ns cs) c) := by
  intro q hq
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp hq
  obtain ⟨l, hl, holds⟩ := h original member
  refine ⟨literal (names ns cs) l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
  exact (literal_holds _ c l (fun x hx => variable_mem_names member
    (Clause.mem_variables hl hx))).mpr holds

variable {Result : Type z}

@[noinline] def run (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom))
    (finish : Choice Var Hom → Option Result) : Option Result :=
  let ns := names ns cs
  let ctx := context ns cs
  searchDomains ctx (initial ctx) (fun c => finish (decode ns c))

theorem run_sound (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom))
    (finish : Choice Var Hom → Option Result) {r : Result} (h : run ns cs finish = some r) :
    ∃ c, finish c = some r := by
  obtain ⟨choice, found⟩ := searchDomains_sound _ _ _ h
  exact ⟨decode (names ns cs) choice, found⟩

theorem run_complete (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom))
    (c : Choice Var Hom) (h : ∀ q ∈ cs, q.Holds c) (finish : Choice Var Hom → Option Result)
    (hf : ∀ choice, (∀ x ∈ ns, choice x = c x) → finish choice ≠ none) : run ns cs finish ≠ none := by
  apply searchDomains_complete _ (Context.build_wellFormed _ _) _ (encode (names ns cs) c)
    (context_holds ns cs c h) (initial_contains _ _)
  intro choice same
  apply hf
  intro x hx
  have hn := mem_names (cs := cs) hx
  exact (same _ (index_mem_context _ _ hn)).trans (encode_decode _ c hn)

end ACUIhE.FILO.Choices.Indexing
