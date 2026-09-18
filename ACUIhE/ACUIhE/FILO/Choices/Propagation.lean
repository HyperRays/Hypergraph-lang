import ACUIhE.FILO.Choices.Constraints

/-!
# Indexed propagation of necessary status clauses

The occurrence lists are built once. Refinement consults only the clauses
mentioning the variable being refined. A strict finite-set decrease proves
termination; no iteration bound is supplied by a caller.
-/

namespace ACUIhE.FILO.Choices

open Components ACUIh.Linear Goal

universe v w
variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

abbrev Domain (Var : Type v) (Hom : Type w) := Finset (Variable Var Hom × Status)

def options (d : Domain Var Hom) (x : Variable Var Hom) : List Status :=
  statuses.filter (fun k => decide ((x, k) ∈ d))

@[simp] theorem mem_options (d : Domain Var Hom) (x : Variable Var Hom) (k : Status) :
    k ∈ options d x ↔ (x, k) ∈ d := by simp [options]

def Clause.variables (q : Clause Var Hom) : List (Variable Var Hom) :=
  q.filterMap (fun l => match l.atom with | .var x => some x | .const _ => none)

omit [DecidableEq Var] [DecidableEq Hom] in
theorem Clause.mem_variables {q : Clause Var Hom} {l : Literal Var Hom} {x : Variable Var Hom}
    (hl : l ∈ q) (hx : l.atom = .var x) : x ∈ q.variables :=
  List.mem_filterMap.mpr ⟨l, hl, by simp [hx]⟩

def Literal.Possible (d : Domain Var Hom) (l : Literal Var Hom) : Prop :=
  match l.atom with
  | .const _ => .constant ∈ l.allowed
  | .var x => ∃ k ∈ l.allowed, (x, k) ∈ d

instance (d : Domain Var Hom) (l : Literal Var Hom) : Decidable (l.Possible d) := by
  unfold Literal.Possible
  split <;> infer_instance

def Clause.Possible (d : Domain Var Hom) (q : Clause Var Hom) : Prop :=
  ∃ l ∈ q, l.Possible d

instance (d : Domain Var Hom) (q : Clause Var Hom) : Decidable (q.Possible d) :=
  inferInstanceAs (Decidable (∃ l ∈ q, l.Possible d))

structure Context (Var : Type v) (Hom : Type w) where
  names : List (Variable Var Hom)
  clauses : List (Clause Var Hom)
  incident : List (Variable Var Hom × List (Clause Var Hom))

def Context.build (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom)) : Context Var Hom :=
  let names := (ns ++ cs.flatMap Clause.variables).dedup
  ⟨names, cs, names.map (fun x => (x, cs.filter (fun q => x ∈ q.variables)))⟩

def Context.WellFormed (ctx : Context Var Hom) : Prop :=
  (∀ q ∈ ctx.clauses, q.variables ⊆ ctx.names) ∧
  ctx.incident = ctx.names.map (fun x => (x, ctx.clauses.filter (fun q => x ∈ q.variables)))

theorem Context.build_wellFormed (ns : List (Variable Var Hom)) (cs : List (Clause Var Hom)) :
    (Context.build ns cs).WellFormed := by
  refine ⟨?_, rfl⟩
  intro q hq x hx
  exact List.mem_dedup.mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hx⟩))

theorem Context.mem_build_names {ns : List (Variable Var Hom)} {cs : List (Clause Var Hom)}
    {x : Variable Var Hom} (hx : x ∈ ns) : x ∈ (Context.build ns cs).names :=
  List.mem_dedup.mpr (List.mem_append_left _ hx)

def Context.Contains (ctx : Context Var Hom) (d : Domain Var Hom) (c : Choice Var Hom) : Prop :=
  ∀ x ∈ ctx.names, (x, c x) ∈ d

def Context.Holds (ctx : Context Var Hom) (c : Choice Var Hom) : Prop :=
  ∀ q ∈ ctx.clauses, q.Holds c

def Context.Possible (ctx : Context Var Hom) (d : Domain Var Hom) : Prop :=
  (∀ x ∈ ctx.names, ∃ k ∈ statuses, (x, k) ∈ d) ∧ ∀ q ∈ ctx.clauses, q.Possible d

instance (ctx : Context Var Hom) (d : Domain Var Hom) : Decidable (ctx.Possible d) :=
  inferInstanceAs (Decidable ((∀ x ∈ ctx.names, ∃ k ∈ statuses, (x, k) ∈ d) ∧
    ∀ q ∈ ctx.clauses, q.Possible d))

theorem Context.clause_possible (ctx : Context Var Hom) (wf : ctx.WellFormed)
    (d : Domain Var Hom) (c : Choice Var Hom) (hd : ctx.Contains d c) {q : Clause Var Hom}
    (hq : q ∈ ctx.clauses) (h : q.Holds c) : q.Possible d := by
  obtain ⟨l, hl, holds⟩ := h
  refine ⟨l, hl, ?_⟩
  cases he : l.atom with
  | const a => simpa [Literal.Possible, Literal.Holds, atomStatus, he] using holds
  | var x =>
    simp only [Literal.Possible, he]
    exact ⟨c x, by simpa [Literal.Holds, he, atomStatus] using holds,
      hd x (wf.1 q hq (Clause.mem_variables hl he))⟩

theorem Context.possible_of_solution (ctx : Context Var Hom) (wf : ctx.WellFormed)
    (d : Domain Var Hom) (c : Choice Var Hom) (hd : ctx.Contains d c) (h : ctx.Holds c) :
    ctx.Possible d :=
  ⟨fun x hx => ⟨c x, mem_statuses _, hd x hx⟩,
    fun q hq => ctx.clause_possible wf d c hd hq (h q hq)⟩

def restrict (d : Domain Var Hom) (x : Variable Var Hom) (k : Status) : Domain Var Hom :=
  d.filter (fun p => p.1 ≠ x ∨ p.2 = k)

@[simp] theorem mem_restrict (d : Domain Var Hom) (x y : Variable Var Hom) (k l : Status) :
    (y, l) ∈ restrict d x k ↔ (y, l) ∈ d ∧ (y ≠ x ∨ l = k) := by simp [restrict]

theorem contains_restrict (ctx : Context Var Hom) (d : Domain Var Hom) (c : Choice Var Hom)
    (hd : ctx.Contains d c) (x : Variable Var Hom) : ctx.Contains (restrict d x (c x)) c := by
  intro y hy
  exact mem_restrict _ _ _ _ _ |>.mpr ⟨hd y hy, by by_cases h : y = x <;> simp [h]⟩

/-- Query a hypothetical restriction without constructing another finite set. -/
def Literal.PossibleAt (d : Domain Var Hom) (x : Variable Var Hom) (k : Status)
    (l : Literal Var Hom) : Prop :=
  match l.atom with
  | .const _ => .constant ∈ l.allowed
  | .var y => ∃ j ∈ l.allowed, (y, j) ∈ d ∧ (y ≠ x ∨ j = k)

instance (d : Domain Var Hom) (x : Variable Var Hom) (k : Status) (l : Literal Var Hom) :
    Decidable (l.PossibleAt d x k) := by
  unfold Literal.PossibleAt
  split <;> infer_instance

def Clause.PossibleAt (d : Domain Var Hom) (x : Variable Var Hom) (k : Status)
    (q : Clause Var Hom) : Prop := ∃ l ∈ q, l.PossibleAt d x k

instance (d : Domain Var Hom) (x : Variable Var Hom) (k : Status) (q : Clause Var Hom) :
    Decidable (q.PossibleAt d x k) := inferInstanceAs (Decidable (∃ l ∈ q, l.PossibleAt d x k))

theorem Literal.possibleAt_iff (d : Domain Var Hom) (x : Variable Var Hom) (k : Status)
    (l : Literal Var Hom) : l.PossibleAt d x k ↔ l.Possible (restrict d x k) := by
  cases he : l.atom <;> simp [Literal.PossibleAt, Literal.Possible, he]

theorem Clause.possibleAt_iff (d : Domain Var Hom) (x : Variable Var Hom) (k : Status)
    (q : Clause Var Hom) : q.PossibleAt d x k ↔ q.Possible (restrict d x k) := by
  simp only [Clause.PossibleAt, Clause.Possible, Literal.possibleAt_iff]

/-- Compute the surviving statuses once, then update just this variable. -/
@[noinline] def refineEntry (e : Variable Var Hom × List (Clause Var Hom))
    (d : Domain Var Hom) : Domain Var Hom :=
  let allowed := statuses.filter (fun k => decide
    ((e.1, k) ∈ d ∧ ∀ q ∈ e.2, q.PossibleAt d e.1 k))
  d.filter (fun p => p.1 ≠ e.1 ∨ p.2 ∈ allowed)

theorem refineEntry_subset (e : Variable Var Hom × List (Clause Var Hom)) (d : Domain Var Hom) :
    refineEntry e d ⊆ d := Finset.filter_subset _ _

theorem refineEntry_preserves (ctx : Context Var Hom) (wf : ctx.WellFormed)
    (e : Variable Var Hom × List (Clause Var Hom)) (he : e.2 ⊆ ctx.clauses)
    (d : Domain Var Hom) (c : Choice Var Hom) (hd : ctx.Contains d c) (h : ctx.Holds c) :
    ctx.Contains (refineEntry e d) c := by
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨hd x hx, ?_⟩
  by_cases eq : x = e.1
  · right
    apply List.mem_filter.mpr
    refine ⟨mem_statuses _, decide_eq_true ⟨by simpa [← eq] using hd x hx, ?_⟩⟩
    intro q hq
    apply (Clause.possibleAt_iff _ _ _ _).mpr
    have contained := contains_restrict ctx d c hd x
    rw [eq] at contained
    simpa [← eq] using ctx.clause_possible wf _ c contained (he hq) (h q (he hq))
  · exact .inl eq

/-- Later entries immediately see earlier removals, rather than waiting for
another whole sweep. Both directions are swept to avoid an ordering bias. -/
def refineEntries : List (Variable Var Hom × List (Clause Var Hom)) → Domain Var Hom → Domain Var Hom
  | [], d => d
  | e :: es, d => refineEntries es (refineEntry e d)

theorem refineEntries_subset (es : List (Variable Var Hom × List (Clause Var Hom)))
    (d : Domain Var Hom) : refineEntries es d ⊆ d := by
  induction es generalizing d with
  | nil => exact Finset.Subset.refl _
  | cons e es ih => exact Finset.Subset.trans (ih _) (refineEntry_subset _ _)

theorem refineEntries_preserves (ctx : Context Var Hom) (wf : ctx.WellFormed)
    (es : List (Variable Var Hom × List (Clause Var Hom)))
    (he : ∀ e ∈ es, e.2 ⊆ ctx.clauses) (d : Domain Var Hom) (c : Choice Var Hom)
    (hd : ctx.Contains d c) (h : ctx.Holds c) : ctx.Contains (refineEntries es d) c := by
  induction es generalizing d with
  | nil => exact hd
  | cons e es ih =>
    exact ih (fun e he' => he e (List.mem_cons_of_mem _ he')) _
      (refineEntry_preserves ctx wf e (he e (by simp)) d c hd h)

@[noinline] def refineClauses (entries : List (Variable Var Hom × List (Clause Var Hom)))
    (d : Domain Var Hom) : Domain Var Hom :=
  refineEntries entries.reverse (refineEntries entries d)

theorem refineClauses_subset (entries : List (Variable Var Hom × List (Clause Var Hom)))
    (d : Domain Var Hom) : refineClauses entries d ⊆ d := by
  exact Finset.Subset.trans (refineEntries_subset _ _) (refineEntries_subset _ _)

theorem refineClauses_preserves (ctx : Context Var Hom) (wf : ctx.WellFormed)
    (d : Domain Var Hom) (c : Choice Var Hom) (hd : ctx.Contains d c) (h : ctx.Holds c) :
    ctx.Contains (refineClauses ctx.incident d) c := by
  have valid : ∀ e ∈ ctx.incident, e.2 ⊆ ctx.clauses := by
    intro e he
    rw [wf.2] at he
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp he
    exact fun _ hq => (List.mem_filter.mp hq).1
  exact refineEntries_preserves ctx wf _ (by simpa using valid) _ c
    (refineEntries_preserves ctx wf _ valid d c hd h) h

def close (ctx : Context Var Hom) (d : Domain Var Hom) : Domain Var Hom :=
  let next := refineClauses ctx.incident d
  if next = d then d else close ctx next
termination_by d.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨refineClauses_subset _ _, by assumption⟩)

theorem close_subset (ctx : Context Var Hom) (d : Domain Var Hom) : close ctx d ⊆ d := by
  fun_induction close ctx d
  · exact Finset.Subset.refl _
  · exact Finset.Subset.trans (by assumption) (refineClauses_subset _ _)

theorem close_preserves (ctx : Context Var Hom) (wf : ctx.WellFormed) (d : Domain Var Hom)
    (c : Choice Var Hom) (h : ctx.Holds c) (hd : ctx.Contains d c) : ctx.Contains (close ctx d) c := by
  revert hd
  fun_induction close ctx d
  · exact fun hd => hd
  · intro hd
    apply_assumption
    exact refineClauses_preserves ctx wf _ c hd h

theorem close_fixed (ctx : Context Var Hom) (d : Domain Var Hom) :
    refineClauses ctx.incident (close ctx d) = close ctx d := by
  fun_induction close ctx d <;> assumption

def initial (ctx : Context Var Hom) : Domain Var Hom :=
  (ctx.names.flatMap (fun x => statuses.map (x, ·))).toFinset

theorem initial_contains (ctx : Context Var Hom) (c : Choice Var Hom) : ctx.Contains (initial ctx) c := by
  intro x hx
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
    ⟨x, hx, List.mem_map.mpr ⟨c x, mem_statuses _, rfl⟩⟩)

end ACUIhE.FILO.Choices
