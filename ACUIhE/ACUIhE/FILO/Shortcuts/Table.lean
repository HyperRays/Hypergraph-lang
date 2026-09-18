import ACUIhE.FILO.Goal.Prepared
import ACUIhE.FILO.Shortcuts.Semantics

/-! # Stored acyclic resolver tables (§4.7)

New entries refer only to the older table. Resolver edges are ordinary data;
their invariants are proved separately. Reconstruction is memoized by folding
the table from oldest to newest, not by rerunning saturation.
-/

namespace ACUIhE.FILO.Shortcuts.Table

open Components ACUIh.Linear Goal

universe v w u z

def lookup {Key : Type u} {Value : Type z} [DecidableEq Key]
    (key : Key) (pairs : List (Key × Value)) : Option Value :=
  (pairs.find? (fun p => decide (p.1 = key))).map Prod.snd

theorem lookup_mem {Key : Type u} {Value : Type z} [DecidableEq Key]
    {key : Key} {pairs : List (Key × Value)} {value : Value}
    (h : lookup key pairs = some value) : (key, value) ∈ pairs := by
  unfold lookup at h
  cases hf : pairs.find? (fun p => decide (p.1 = key)) with
  | none => simp [hf] at h
  | some pair =>
    have hm := List.mem_of_find?_eq_some hf
    have checked := List.find?_some hf
    have hk : pair.1 = key := of_decide_eq_true checked
    have hv : pair.2 = value := Option.some.inj (by simpa [hf] using h)
    have eq : pair = (key, value) := Prod.ext hk hv
    exact eq ▸ hm

theorem lookup_exists {Key : Type u} {Value : Type z} [DecidableEq Key]
    {key : Key} {pairs : List (Key × Value)} {value : Value} (h : (key, value) ∈ pairs) :
    ∃ found, lookup key pairs = some found := by
  cases hf : pairs.find? (fun p => decide (p.1 = key)) with
  | none => exact False.elim (List.find?_eq_none.mp hf _ h (by simp))
  | some pair => exact ⟨pair.2, by simp [lookup, hf]⟩

structure Entry (Var : Type v) (Hom : Type w) where
  node : Node Var Hom
  edges : List (Hom × Node Var Hom)

abbrev Store (Var : Type v) (Hom : Type w) := List (Entry Var Hom)

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def nodes (table : Store Var Hom) : Finset (Node Var Hom) := (table.map Entry.node).toFinset

@[simp] theorem mem_nodes (table : Store Var Hom) (node : Node Var Hom) :
    node ∈ nodes table ↔ ∃ e ∈ table, e.node = node := by simp [nodes]

def resolver (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom) (r : Hom) :
    Option (Node Var Hom) :=
  (table.find? (fun e => decide (Resolves s node r e.node))).map Entry.node

theorem resolver_some (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom)
    (r : Hom) {target : Node Var Hom} (h : resolver s table node r = some target) :
    target ∈ nodes table ∧ Resolves s node r target := by
  unfold resolver at h
  cases hf : table.find? (fun e => decide (Resolves s node r e.node)) with
  | none => simp [hf] at h
  | some e =>
    have eq : e.node = target := Option.some.inj (by simpa [hf] using h)
    have checked := List.find?_some hf
    exact ⟨(mem_nodes _ _).mpr ⟨e, List.mem_of_find?_eq_some hf, eq⟩,
      eq ▸ of_decide_eq_true checked⟩

def Ready (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom) : Prop :=
  ∀ r ∈ s.roles, Needs s node r → ∃ target ∈ nodes table, Resolves s node r target

instance (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom) :
    Decidable (Ready s table node) :=
  inferInstanceAs (Decidable (∀ r ∈ s.roles, Needs s node r →
    ∃ target ∈ nodes table, Resolves s node r target))

theorem resolver_exists (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom)
    (r : Hom) (h : ∃ target ∈ nodes table, Resolves s node r target) :
    ∃ target, resolver s table node r = some target := by
  obtain ⟨target, member, link⟩ := h
  obtain ⟨e, he, rfl⟩ := (mem_nodes _ _).mp member
  cases hf : table.find? (fun e => decide (Resolves s node r e.node)) with
  | none => exact False.elim (List.find?_eq_none.mp hf e he (decide_eq_true link))
  | some found => exact ⟨found.node, by simp [resolver, hf]⟩

def links (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom) :
    List (Hom × Node Var Hom) :=
  s.roles.filterMap (fun r => if Needs s node r then (resolver s table node r).map (r, ·) else none)

theorem mem_links (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom)
    (r : Hom) (target : Node Var Hom) : (r, target) ∈ links s table node ↔
    r ∈ s.roles ∧ Needs s node r ∧ resolver s table node r = some target := by
  simp only [links, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, h⟩
    split at h
    · rename_i hn
      cases hr : resolver s table node t with
      | none => simp [hr] at h
      | some value =>
        have eq : (t, value) = (r, target) := Option.some.inj (by simpa [hr] using h)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
        exact ⟨ht, hn, hr⟩
    · cases h
  · rintro ⟨hr, hn, found⟩
    exact ⟨r, hr, by simp [hn, found]⟩

def Entry.Good (s : System Var Hom) (older : Store Var Hom) (e : Entry Var Hom) : Prop :=
  ∀ r ∈ s.roles, match lookup r e.edges with
    | none => ¬ Needs s e.node r
    | some target => target ∈ nodes older ∧ Resolves s e.node r target

def make (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom) : Option (Entry Var Hom) :=
  if Ready s table node then some ⟨node, links s table node⟩ else none

theorem make_some (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom)
    {e : Entry Var Hom} (h : make s table node = some e) :
    e.node = node ∧ e.Good s table := by
  unfold make at h
  split at h
  · rename_i ready
    have eq := Option.some.inj h
    subst e
    refine ⟨rfl, ?_⟩
    intro r hr
    cases hl : lookup r (links s table node) with
    | none =>
      intro hn
      obtain ⟨target, found⟩ := resolver_exists s table node r (ready r hr hn)
      have member := (mem_links s table node r target).mpr ⟨hr, hn, found⟩
      obtain ⟨value, hv⟩ := lookup_exists member
      rw [hl] at hv
      cases hv
    | some target =>
      exact resolver_some s table node r ((mem_links s table node r target).mp (lookup_mem hl)).2.2
  · cases h

theorem make_none_iff (s : System Var Hom) (table : Store Var Hom) (node : Node Var Hom) :
    make s table node = none ↔ ¬ Ready s table node := by simp [make]

theorem Entry.Good.mono {s : System Var Hom} {a b : Store Var Hom} {e : Entry Var Hom}
    (h : e.Good s a) (sub : nodes a ⊆ nodes b) : e.Good s b := by
  intro r hr
  have original := h r hr
  cases hf : lookup r e.edges with
  | none => simpa [hf] using original
  | some target =>
    simp only [hf] at original ⊢
    exact ⟨sub original.1, original.2⟩

def Certified (g : Prepared Var Hom) : Store Var Hom → Prop
  | [] => True
  | e :: rest => Certified g rest ∧ g.Normal e.node ∧ e.Good g.source rest

theorem certified_normal (g : Prepared Var Hom) (table : Store Var Hom) (h : Certified g table) :
    ∀ node ∈ nodes table, g.Normal node := by
  induction table with
  | nil => simp [nodes]
  | cons first rest ih =>
    intro node hn
    obtain ⟨e, he, rfl⟩ := (mem_nodes _ _).mp hn
    rcases List.mem_cons.mp he with rfl | he
    · exact h.2.1
    · exact ih h.1 e.node ((mem_nodes _ _).mpr ⟨e, he, rfl⟩)

theorem certified_extend (g : Prepared Var Hom) (older newer : Store Var Hom)
    (old : Certified g older)
    (fresh : ∀ e ∈ newer, g.Normal e.node ∧ e.Good g.source older) : Certified g (newer ++ older) := by
  induction newer with
  | nil => exact old
  | cons e rest ih =>
    obtain ⟨normal, good⟩ := fresh e (by simp)
    refine ⟨ih (fun a ha => fresh a (by simp [ha])), normal, good.mono ?_⟩
    intro node hn
    obtain ⟨a, ha, eq⟩ := (mem_nodes _ _).mp hn
    exact (mem_nodes _ _).mpr ⟨a, List.mem_append_right _ ha, eq⟩

def trace (s : System Var Hom) (computed : List (Node Var Hom × Trace Var Hom))
    (e : Entry Var Hom) : Trace Var Hom :=
  graft s.roles e.node (fun r => match lookup r e.edges with
    | none => ∅
    | some target => (lookup target computed).getD ∅)

def materialize (s : System Var Hom) : Store Var Hom → List (Node Var Hom × Trace Var Hom)
  | [] => []
  | e :: rest => let computed := materialize s rest
      (e.node, trace s computed e) :: computed

@[simp] theorem materialize_nodes (s : System Var Hom) (table : Store Var Hom) :
    (materialize s table).map Prod.fst = table.map Entry.node := by
  induction table with
  | nil => rfl
  | cons e rest ih => simp [materialize, ih]

theorem trace_correct (g : Prepared Var Hom) (valid : g.Valid) (older : Store Var Hom)
    (normal : ∀ node ∈ nodes older, g.Normal node)
    (computed : List (Node Var Hom × Trace Var Hom))
    (same : computed.map Prod.fst = older.map Entry.node)
    (realized : ∀ pair ∈ computed, Realizes g.source pair.1 pair.2)
    (e : Entry Var Hom) (initial : Bool) (localRoot : Local g.source initial e.node)
    (good : e.Good g.source older) : Realizes g.source e.node (trace g.source computed e) := by
  let targets := fun r => (lookup r e.edges).getD ∅
  apply realizes_graft g.source initial e.node localRoot targets
  · intro r hr
    have hg := good r hr
    cases hf : lookup r e.edges with
    | none => simpa [targets, hf] using local_empty g.source
    | some target =>
      simp only [hf] at hg
      simpa [targets, hf] using g.normal_local valid target (normal target hg.1)
  · intro r hr
    have hg := good r hr
    cases hf : lookup r e.edges with
    | none => simpa [targets, hf] using realizes_empty g.source
    | some target =>
      simp only [hf] at hg
      have hm : target ∈ computed.map Prod.fst := by
        rw [same]
        exact List.mem_toFinset.mp hg.1
      obtain ⟨pair, hp, he⟩ := List.mem_map.mp hm
      have hp' : (target, pair.2) ∈ computed := by simpa [← he] using hp
      obtain ⟨value, hv⟩ := lookup_exists hp'
      have result := realized (target, value) (lookup_mem hv)
      simpa [targets, hf, hv] using result
  · intro r hr
    have hg := good r hr
    cases hf : lookup r e.edges with
    | none =>
      simp only [hf] at hg
      simp only [targets, hf, Option.getD_none]
      change Resolves g.source e.node r ∅
      intro x hx
      cases x with
      | base v | constant p => trivial
      | role t p =>
        intro eq; subst t
        simp only [Finset.notMem_empty, iff_false]
        exact fun hm => hg (needs_of_member g.source hx hm)
    | some target =>
      simp only [hf] at hg
      simpa [targets, hf] using hg.2

theorem materialize_correct (g : Prepared Var Hom) (valid : g.Valid)
    (table : Store Var Hom) (certified : Certified g table) :
    ∀ pair ∈ materialize g.source table, Realizes g.source pair.1 pair.2 := by
  induction table with
  | nil => simp [materialize]
  | cons e rest ih =>
    have previous := ih certified.1
    intro pair hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact trace_correct g valid rest (certified_normal g rest certified.1)
        (materialize g.source rest) (materialize_nodes _ _) previous e false
        (g.normal_local valid e.node certified.2.1) certified.2.2
    · exact previous pair hp

end ACUIhE.FILO.Shortcuts.Table
