import ACUIhE.FILO.Choices.Propagation

/-!
# Propagating finite status search

Each branch removes at least one status. Propagation is repeated after each
decision, and singleton domains never introduce a branch. Completeness follows
by following the classification of an arbitrary genuine solution, not by a
bound on the size of that solution or by validating reconstructed candidates.
-/

namespace ACUIhE.FILO.Choices

open Components

universe v w z
variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def pivot (ctx : Context Var Hom) (d : Domain Var Hom) : Option (Variable Var Hom × Status) :=
  (ctx.names.flatMap (fun x => statuses.map (x, ·))).find?
    (fun p => decide (p ∈ d ∧ ∃ q ∈ d, q.1 = p.1 ∧ q.2 ≠ p.2))

theorem pivot_some (ctx : Context Var Hom) (d : Domain Var Hom) {p : Variable Var Hom × Status}
    (h : pivot ctx d = some p) : p ∈ d ∧ ∃ q ∈ d, q.1 = p.1 ∧ q.2 ≠ p.2 := by
  have hp := List.find?_some h
  exact of_decide_eq_true hp

theorem restrict_subset (d : Domain Var Hom) (x : Variable Var Hom) (k : Status) :
    restrict d x k ⊆ d := Finset.filter_subset _ _

theorem pivot_restrict_lt (ctx : Context Var Hom) (d : Domain Var Hom) {p : Variable Var Hom × Status}
    (h : pivot ctx d = some p) : (restrict d p.1 p.2).card < d.card := by
  obtain ⟨_, q, hq, same, different⟩ := pivot_some ctx d h
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨restrict_subset _ _ _, ?_⟩
  intro eq
  have member : q ∈ restrict d p.1 p.2 := by rw [eq]; exact hq
  have := (Finset.mem_filter.mp member).2
  simp [same, different] at this

theorem pivot_erase_lt (ctx : Context Var Hom) (d : Domain Var Hom) {p : Variable Var Hom × Status}
    (h : pivot ctx d = some p) : (d.erase p).card < d.card :=
  Finset.card_erase_lt_of_mem (pivot_some ctx d h).1

def lookup (d : Domain Var Hom) : Choice Var Hom := fun x => (options d x).headD .top

theorem lookup_eq (ctx : Context Var Hom) (d : Domain Var Hom) (c : Choice Var Hom)
    (hd : ctx.Contains d c) (hp : pivot ctx d = none) : ∀ x ∈ ctx.names, lookup d x = c x := by
  intro x hx
  have unique : ∀ k, (x, k) ∈ d → k = c x := by
    intro k hk
    by_contra ne
    have no := (List.find?_eq_none.mp hp) (x, c x) (List.mem_flatMap.mpr
      ⟨x, hx, List.mem_map.mpr ⟨c x, mem_statuses _, rfl⟩⟩)
    exact no (decide_eq_true ⟨hd x hx, (x, k), hk, rfl, ne⟩)
  have member := (mem_options d x (c x)).mpr (hd x hx)
  unfold lookup
  cases he : options d x with
  | nil => simp [he] at member
  | cons k ks =>
    exact unique k ((mem_options _ _ _).mp (by simp [he]))

theorem contains_erase (ctx : Context Var Hom) (d : Domain Var Hom) (c : Choice Var Hom)
    (hd : ctx.Contains d c) (p : Variable Var Hom × Status) (h : c p.1 ≠ p.2) :
    ctx.Contains (d.erase p) c := by
  intro x hx
  refine Finset.mem_erase.mpr ⟨?_, hd x hx⟩
  intro eq
  have first := congrArg Prod.fst eq
  have second := congrArg Prod.snd eq
  exact h (by simpa only [show x = p.1 from first] using second)

variable {Result : Type z}

/-- The callback is the existing complete word solver for one classification. -/
def searchDomains (ctx : Context Var Hom) (d : Domain Var Hom)
    (finish : Choice Var Hom → Option Result) : Option Result :=
  if ctx.Possible d then
    let stable := close ctx d
    if ctx.Possible stable then
      match _hp : pivot ctx stable with
      | none => finish (lookup stable)
      | some p =>
          (searchDomains ctx (restrict stable p.1 p.2) finish).orElse
            (fun _ => searchDomains ctx (stable.erase p) finish)
    else none
  else none
termination_by d.card
decreasing_by
  · exact Nat.lt_of_lt_of_le (pivot_restrict_lt _ _ _hp) (Finset.card_le_card (close_subset _ _))
  · exact Nat.lt_of_lt_of_le (pivot_erase_lt _ _ _hp) (Finset.card_le_card (close_subset _ _))

theorem searchDomains_sound (ctx : Context Var Hom) (d : Domain Var Hom)
    (finish : Choice Var Hom → Option Result) {r : Result}
    (h : searchDomains ctx d finish = some r) : ∃ c, finish c = some r := by
  fun_induction searchDomains ctx d finish
  · exact ⟨_, h⟩
  · rename_i d _ stable _ p hp left right
    cases he : searchDomains ctx (restrict stable p.1 p.2) finish with
    | none => exact right (by simpa [he] using h)
    | some found =>
      have eq : found = r := Option.some.inj (by simpa [he] using h)
      exact left (eq ▸ he)
  · cases h
  · cases h

theorem searchDomains_complete (ctx : Context Var Hom) (wf : ctx.WellFormed)
    (d : Domain Var Hom) (c : Choice Var Hom) (holds : ctx.Holds c)
    (hd : ctx.Contains d c) (finish : Choice Var Hom → Option Result)
    (hf : ∀ choice, (∀ x ∈ ctx.names, choice x = c x) → finish choice ≠ none) :
    searchDomains ctx d finish ≠ none := by
  revert hd
  fun_induction searchDomains ctx d finish
  · intro hd
    exact hf _ (lookup_eq ctx _ c (close_preserves ctx wf _ c holds hd) (by assumption))
  · intro hd
    rename_i d _ stable _ p hp left right
    have contained := close_preserves ctx wf _ c holds hd
    by_cases eq : c p.1 = p.2
    · have yes := left (by simpa only [← eq] using contains_restrict ctx _ c contained p.1)
      cases he : searchDomains ctx (restrict stable p.1 p.2) finish <;> simp_all
    · have no := right (contains_erase ctx _ c contained p eq)
      cases he : searchDomains ctx (restrict stable p.1 p.2) finish <;> simp_all
  · intro hd
    have stable := close_preserves ctx wf _ c holds hd
    exact False.elim (by
      have := ctx.possible_of_solution wf _ c stable holds
      contradiction)
  · intro hd
    exact False.elim (by
      have := ctx.possible_of_solution wf _ c hd holds
      contradiction)

end ACUIhE.FILO.Choices
