import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs

/-!
# Complete finite Horn propagation

Bits denote absent memberships in the layer solver. Saturation adds consequences,
never enumerates assignments, and stabilizes within the cardinality of the bit
universe. The returned set is the least model, when one exists.
-/

namespace ACUIhE.ACUIESolver.Layers.Horn

structure Rule (α : Type) where
  body : Finset α
  head : Option α
  deriving DecidableEq

variable {α : Type} [DecidableEq α]

def Model (rs : Finset (Rule α)) (s : Finset α) : Prop :=
  ∀ r ∈ rs, r.body ⊆ s → ∃ i, r.head = some i ∧ i ∈ s

def step (rs : Finset (Rule α)) (s : Finset α) : Finset α :=
  s ∪ rs.biUnion (fun r => if r.body ⊆ s then r.head.toFinset else ∅)

theorem subset_step (rs : Finset (Rule α)) (s : Finset α) : s ⊆ step rs s :=
  Finset.subset_union_left

theorem step_subset_model {rs : Finset (Rule α)} {s m : Finset α}
    (hm : Model rs m) (hsm : s ⊆ m) : step rs s ⊆ m := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hsm hi
  · obtain ⟨r, hr, hi⟩ := Finset.mem_biUnion.mp hi
    split_ifs at hi with hb
    · obtain ⟨j, hj, hjm⟩ := hm r hr (Finset.Subset.trans hb hsm)
      have hij : i = j := by simpa [hj] using hi
      simpa only [hij] using hjm
    · simp at hi

def iter (rs : Finset (Rule α)) : Nat → Finset α
  | 0 => ∅
  | k + 1 => step rs (iter rs k)

theorem iter_subset_model {rs : Finset (Rule α)} {m : Finset α}
    (hm : Model rs m) (k : Nat) : iter rs k ⊆ m := by
  induction k with
  | zero => exact Finset.empty_subset _
  | succ k ih => exact step_subset_model hm ih

theorem fixed_or_growth (rs : Finset (Rule α)) (k : Nat) :
    step rs (iter rs k) = iter rs k ∨ k ≤ (iter rs k).card := by
  induction k with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ k ih =>
    rcases ih with hf | hg
    · left
      simp only [iter, hf]
    · by_cases hf : step rs (iter rs k) = iter rs k
      · left
        simp only [iter, hf]
      · right
        have hlt := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr
            ⟨subset_step rs (iter rs k), Ne.symm hf⟩)
        change k + 1 ≤ (step rs (iter rs k)).card
        omega

section FiniteClosure

variable [Fintype α]

def closure (rs : Finset (Rule α)) : Finset α := iter rs (Fintype.card α)

theorem closure_fixed (rs : Finset (Rule α)) : step rs (closure rs) = closure rs := by
  rcases fixed_or_growth rs (Fintype.card α) with hf | hg
  · exact hf
  · by_contra hf
    have hlt := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step rs (closure rs), Ne.symm hf⟩)
    have hbound : (step rs (closure rs)).card ≤ Fintype.card α := by
      simpa using Finset.card_le_univ (step rs (closure rs))
    change Fintype.card α ≤ (closure rs).card at hg
    omega

omit [Fintype α] in
theorem step_mono (rs : Finset (Rule α)) {s t : Finset α} (h : s ⊆ t) :
    step rs s ⊆ step rs t := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact subset_step rs t (h hi)
  · obtain ⟨r, hr, hi⟩ := Finset.mem_biUnion.mp hi
    split_ifs at hi with hb
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨r, hr, by simpa [Finset.Subset.trans hb h] using hi⟩
    · simp at hi

theorem step_measure_lt (rs : Finset (Rule α)) (s : Finset α) (h : step rs s ≠ s) :
    Fintype.card α - (step rs s).card < Fintype.card α - s.card := by
  have hs := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step rs s, Ne.symm h⟩)
  have hb := Finset.card_le_univ (step rs s)
  omega

end FiniteClosure

/-- Stop immediately at a fixed point. Every recursive call adds a new bit. -/
def saturate [Fintype α] (rs : Finset (Rule α)) (s : Finset α) : Finset α :=
  let next := step rs s
  if _h : next = s then s else saturate rs next
termination_by Fintype.card α - s.card
decreasing_by exact step_measure_lt rs s _h

variable [Fintype α]

theorem saturate_fixed (rs : Finset (Rule α)) (s : Finset α) :
    step rs (saturate rs s) = saturate rs s := by
  rw [saturate]
  split_ifs with h
  · exact h
  · exact saturate_fixed rs (step rs s)
termination_by Fintype.card α - s.card
decreasing_by exact step_measure_lt rs s h

theorem saturate_le_fixed (rs : Finset (Rule α)) (s t : Finset α)
    (hst : s ⊆ t) (ht : step rs t = t) : saturate rs s ⊆ t := by
  rw [saturate]
  split_ifs with h
  · exact hst
  · exact saturate_le_fixed rs (step rs s) t (by simpa only [ht] using step_mono rs hst) ht
termination_by Fintype.card α - s.card
decreasing_by exact step_measure_lt rs s h

omit [Fintype α] in
theorem iter_le_fixed (rs : Finset (Rule α)) (t : Finset α) (ht : step rs t = t)
    (k : Nat) : iter rs k ⊆ t := by
  induction k with
  | zero => exact Finset.empty_subset _
  | succ k ih => simpa only [iter, ht] using step_mono rs ih

/-- Early stopping is exactly the former fixed-round closure, not an approximation. -/
theorem saturate_eq_closure (rs : Finset (Rule α)) : saturate rs ∅ = closure rs := by
  apply Finset.Subset.antisymm
  · exact saturate_le_fixed rs ∅ (closure rs) (Finset.empty_subset _) (closure_fixed rs)
  · exact iter_le_fixed rs (saturate rs ∅) (saturate_fixed rs ∅) (Fintype.card α)

def NoConflict (rs : Finset (Rule α)) (s : Finset α) : Prop :=
  ∀ r ∈ rs, r.head = none → ¬ r.body ⊆ s

instance (rs : Finset (Rule α)) (s : Finset α) : Decidable (NoConflict rs s) :=
  inferInstanceAs (Decidable (∀ r ∈ rs, r.head = none → ¬ r.body ⊆ s))

theorem closure_model {rs : Finset (Rule α)} (hc : NoConflict rs (closure rs)) :
    Model rs (closure rs) := by
  intro r hr hb
  cases he : r.head with
  | none => exact (hc r hr he hb).elim
  | some i =>
    refine ⟨i, rfl, ?_⟩
    rw [← closure_fixed rs]
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨r, hr, by simp [hb, he]⟩

theorem model_noConflict {rs : Finset (Rule α)} {m : Finset α}
    (hm : Model rs m) : NoConflict rs (closure rs) := by
  intro r hr he hb
  obtain ⟨i, hi, _⟩ := hm r hr (Finset.Subset.trans hb (iter_subset_model hm (Fintype.card α)))
  simp [he] at hi

def solve (rs : Finset (Rule α)) : Option (Finset α) :=
  let closed := saturate rs ∅
  if NoConflict rs closed then some closed else none

theorem solve_eq_fixedRounds (rs : Finset (Rule α)) :
    solve rs = if NoConflict rs (closure rs) then some (closure rs) else none := by
  simp only [solve, saturate_eq_closure]

theorem solve_sound {rs : Finset (Rule α)} {s : Finset α}
    (h : solve rs = some s) : Model rs s := by
  rw [solve_eq_fixedRounds] at h
  split_ifs at h with hc
  · cases Option.some.inj h
    exact closure_model hc

theorem solve_complete {rs : Finset (Rule α)} :
    (∃ m, Model rs m) ↔ ∃ s, solve rs = some s := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨closure rs, by simp [solve_eq_fixedRounds, model_noConflict hm]⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, solve_sound hs⟩

theorem solve_least {rs : Finset (Rule α)} {s m : Finset α}
    (hs : solve rs = some s) (hm : Model rs m) : s ⊆ m := by
  rw [solve_eq_fixedRounds] at hs
  split_ifs at hs with hc
  · cases Option.some.inj hs
    exact iter_subset_model hm (Fintype.card α)


/-- One named-atom coordinate of a flat union expression. -/
structure Coordinate (α : Type) where
  fixed : Bool
  vars : Finset α

def Coordinate.Present (c : Coordinate α) (absent : Finset α) : Prop :=
  c.fixed = true ∨ ∃ i ∈ c.vars, i ∉ absent

/-- Compile one coordinate of a layer inclusion, not a candidate substitution. -/
def compileInclusion (l r : Coordinate α) : Finset (Rule α) :=
  if r.fixed then ∅
  else l.vars.image (fun i => ⟨r.vars, some i⟩) ∪
    if l.fixed then {⟨r.vars, none⟩} else ∅

omit [Fintype α] in
theorem compileInclusion_exact (l r : Coordinate α) (s : Finset α) :
    Model (compileInclusion l r) s ↔ (l.Present s → r.Present s) := by
  rcases l with ⟨lf, lv⟩
  rcases r with ⟨rf, rv⟩
  cases lf <;> cases rf <;>
    simp [compileInclusion, Model, Coordinate.Present, Finset.subset_iff]
  · constructor
    · intro h i hi hn
      by_contra hex
      push Not at hex
      exact hn (h i hi hex)
    · intro h i hi hr
      by_contra hn
      obtain ⟨j, hj, hjn⟩ := h i hi hn
      exact hjn (hr hj)
  · aesop


end ACUIhE.ACUIESolver.Layers.Horn
