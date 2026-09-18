import ACUIhE.FILO.Shortcuts.Table
import ACUIhE.FILO.Shortcuts.Enumeration

/-! # Good-variable generation and strict growth of stored shortcut tables -/

namespace ACUIhE.FILO.Shortcuts.Engine

open Components ACUIh.Linear Goal Table

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def GoodAtom (table : Store Var Hom) : Atom Var Hom → Prop
  | .var (.role _ p) => ∃ target ∈ nodes table, .var p ∈ target
  | _ => True

instance (table : Store Var Hom) (a : Atom Var Hom) : Decidable (GoodAtom table a) := by
  cases a with
  | const _ => unfold GoodAtom; infer_instance
  | var x => cases x <;> unfold GoodAtom <;> infer_instance

def goodAtoms (g : Prepared Var Hom) (table : Store Var Hom) : List (Atom Var Hom) :=
  g.active.filter (fun a => decide (GoodAtom table a))

def generateOne (g : Prepared Var Hom) (table : Store Var Hom) (node : Node Var Hom) :
    Option (Entry Var Hom) :=
  if node ∈ nodes table then none else if g.Flat node then make g.source table node else none

def fresh (g : Prepared Var Hom) (table : Store Var Hom) : Store Var Hom :=
  (subsets (goodAtoms g table)).filterMap (generateOne g table)

theorem fresh_sound (g : Prepared Var Hom) (table : Store Var Hom)
    {e : Entry Var Hom} (h : e ∈ fresh g table) :
    g.Normal e.node ∧ e.Good g.source table ∧ e.node ∉ nodes table := by
  obtain ⟨node, hn, he⟩ := List.mem_filterMap.mp h
  unfold generateOne at he
  split at he
  · cases he
  · rename_i new
    split at he
    · rename_i flat
      obtain ⟨eq, good⟩ := make_some g.source table node he
      refine ⟨⟨?_, eq ▸ flat⟩, good, eq ▸ new⟩
      rw [eq]
      intro a ha
      have hm := List.mem_toFinset.mp ((mem_subsets _ _).mp hn ha)
      exact List.mem_toFinset.mpr (List.mem_filter.mp hm).1
    · cases he

theorem ready_good (g : Prepared Var Hom) (valid : g.Valid) (table : Store Var Hom) (node : Node Var Hom)
    (normal : g.Normal node) (ready : Ready g.source table node) :
    node ⊆ (goodAtoms g table).toFinset := by
  intro a ha
  have active := List.mem_toFinset.mp (normal.1 ha)
  apply List.mem_toFinset.mpr
  apply List.mem_filter.mpr
  refine ⟨active, decide_eq_true ?_⟩
  cases a with
  | const _ => trivial
  | var x =>
    cases x with
    | base _ | constant _ => trivial
    | role r p =>
      have hx := (Prepared.mem_active_var g (.role r p)).mp active |>.1
      have needs := needs_of_member g.source hx ha
      by_cases hr : r ∈ g.source.roles
      · obtain ⟨target, ht, link⟩ := ready r hr needs
        exact ⟨target, ht, (link (.role r p) hx rfl).mp ha⟩
      · exact False.elim (((Prepared.mem_active_var g (.role r p)).mp active).2.1
          ((valid.1 _ hx).2.1 hr))

theorem fresh_complete (g : Prepared Var Hom) (valid : g.Valid) (table : Store Var Hom)
    (node : Node Var Hom) (normal : g.Normal node) (ready : Ready g.source table node)
    (new : node ∉ nodes table) : ∃ e ∈ fresh g table, e.node = node := by
  refine ⟨⟨node, links g.source table node⟩, ?_, rfl⟩
  apply List.mem_filterMap.mpr
  refine ⟨node, (mem_subsets _ _).mpr (ready_good g valid table node normal ready), ?_⟩
  simp only [generateOne, if_neg new, if_pos normal.2, make, if_pos ready]

def allNodes (g : Prepared Var Hom) : Finset (Node Var Hom) := g.active.toFinset.powerset

theorem nodes_append (a b : Store Var Hom) : nodes (a ++ b) = nodes a ∪ nodes b := by
  simp [nodes]

theorem fresh_decreases (g : Prepared Var Hom) (table : Store Var Hom) (h : fresh g table ≠ []) :
    (allNodes g \ nodes (fresh g table ++ table)).card < (allNodes g \ nodes table).card := by
  have sub : allNodes g \ nodes (fresh g table ++ table) ⊆ allNodes g \ nodes table := by
    intro node hn
    obtain ⟨hu, absent⟩ := Finset.mem_sdiff.mp hn
    refine Finset.mem_sdiff.mpr ⟨hu, fun old => absent ?_⟩
    rw [nodes_append]
    exact Finset.mem_union_right _ old
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨normal, _, new⟩ := fresh_sound g table he
  have oldMember : e.node ∈ allNodes g \ nodes table :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_powerset.mpr normal.1, new⟩
  have newMember : e.node ∈ nodes (fresh g table ++ table) :=
    (mem_nodes _ _).mpr ⟨e, List.mem_append_left _ he, rfl⟩
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨sub, ?_⟩
  intro eq
  have impossible := Finset.mem_sdiff.mp (eq.symm ▸ oldMember) |>.2
  exact impossible newMember

theorem fresh_certified (g : Prepared Var Hom) (table : Store Var Hom) (h : Certified g table) :
    Certified g (fresh g table ++ table) := by
  apply certified_extend g table (fresh g table) h
  intro e he
  have hs := fresh_sound g table he
  exact ⟨hs.1, hs.2.1⟩

theorem stalled_closed (g : Prepared Var Hom) (valid : g.Valid) (table : Store Var Hom)
    (stalled : fresh g table = []) (node : Node Var Hom)
    (normal : g.Normal node) (ready : Ready g.source table node) : node ∈ nodes table := by
  by_contra absent
  obtain ⟨e, he, _⟩ := fresh_complete g valid table node normal ready absent
  simp [stalled] at he

/-- Every noninitial shortcut of a solution lies in any table closed under
the paper's good-variable generation and resolving rule. -/
theorem stalled_ready (g : Prepared Var Hom) (valid : g.Valid) (table : Store Var Hom)
    (stalled : fresh g table = []) (iv : Column Var Hom)
    (solution : g.source.Solution iv) (hc : Choices.Classifies g.source g.choice iv) :
    Ready g.source table g.root := by
  have bounded : ∀ n word, maximumLength g.source iv < word.length + n → word ≠ [] →
      atWord g.source iv word ∈ nodes table := by
    intro n
    induction n with
    | zero =>
      intro word bound notNil
      have empty : atWord g.source iv word = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have := length_le_maximum g.source iv word a ha
        omega
      rw [empty]
      apply stalled_closed g valid table stalled ∅
      · refine ⟨Finset.empty_subset _, ?_⟩
        intro q hq impossible
        exact False.elim (Finset.notMem_empty _ impossible)
      · intro r hr needs
        obtain ⟨x, hx, hn⟩ := needs
        cases x <;> simp_all
    | succ n ih =>
      intro word bound notNil
      apply stalled_closed g valid table stalled (atWord g.source iv word)
      · refine ⟨g.compatible_subset_active _ ?_, g.atWord_flat valid iv solution hc word⟩
        simpa [notNil] using g.atWord_compatible iv hc word
      · intro r hr hn
        refine ⟨atWord g.source iv (r :: word), ih (r :: word) ?_ (by simp),
          atWord_resolves g.source iv word r⟩
        simp only [List.length_cons]
        omega
  rw [← g.atWord_root iv hc]
  intro r hr hn
  exact ⟨atWord g.source iv [r], bounded (maximumLength g.source iv + 1) [r]
    (by simp; omega) (by simp), atWord_resolves g.source iv [] r⟩

end ACUIhE.FILO.Shortcuts.Engine
