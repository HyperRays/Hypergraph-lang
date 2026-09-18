import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Finite bottom-up shortcut saturation

This is the finite AND/OR closure used by shortcut resolution: every needed
role must have a resolver in an earlier layer. The number of candidates is a
proved sufficient bound, not an externally supplied search depth.
-/

namespace ACUIhE.FILO.Shortcuts.Saturation

universe u v

variable {Node : Type u} {Role : Type v} [DecidableEq Node]

structure Rules (Node : Type u) (Role : Type v) where
  candidates : Finset Node
  roles : List Role
  needs : Node → Role → Prop
  resolves : Node → Role → Node → Prop

namespace Rules

variable (rules : Rules Node Role)
variable [∀ s r, Decidable (rules.needs s r)]
variable [∀ s r t, Decidable (rules.resolves s r t)]

def Ready (known : Finset Node) (s : Node) : Prop :=
  ∀ r ∈ rules.roles, rules.needs s r → ∃ t ∈ known, rules.resolves s r t

instance (known : Finset Node) (s : Node) : Decidable (rules.Ready known s) :=
  inferInstanceAs (Decidable (∀ r ∈ rules.roles,
    rules.needs s r → ∃ t ∈ known, rules.resolves s r t))

def step (known : Finset Node) : Finset Node := rules.candidates.filter (rules.Ready known)

def layers : Nat → Finset Node
  | 0 => ∅
  | n + 1 => rules.step (layers n)

omit [DecidableEq Node] [∀ s r, Decidable (rules.needs s r)]
  [∀ s r t, Decidable (rules.resolves s r t)] in
theorem ready_mono {a b : Finset Node} (h : a ⊆ b) {s : Node}
    (hs : rules.Ready a s) : rules.Ready b s := by
  intro r hr hn
  obtain ⟨t, ht, link⟩ := hs r hr hn
  exact ⟨t, h ht, link⟩

omit [DecidableEq Node] in
theorem step_mono {a b : Finset Node} (h : a ⊆ b) : rules.step a ⊆ rules.step b := by
  intro s hs
  obtain ⟨hc, hr⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨hc, rules.ready_mono h hr⟩

omit [DecidableEq Node] in
theorem layers_subset (n : Nat) : rules.layers n ⊆ rules.candidates := by
  cases n with
  | zero => exact Finset.empty_subset _
  | succ n => exact Finset.filter_subset _ _

omit [DecidableEq Node] in
theorem layers_mono_step (n : Nat) : rules.layers n ⊆ rules.layers (n + 1) := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih => exact rules.step_mono ih

omit [DecidableEq Node] in
theorem layers_mono : Monotone rules.layers :=
  monotone_nat_of_le_succ rules.layers_mono_step

omit [DecidableEq Node] in
theorem stable_after {n : Nat} (h : rules.layers (n + 1) = rules.layers n) :
    ∀ k, rules.layers (n + k) = rules.layers n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change rules.step (rules.layers (n + k)) = _
    rw [ih]
    exact h

/-- At most one strict growth step per candidate is possible. -/
theorem stabilized : rules.layers (rules.candidates.card + 1) =
    rules.layers rules.candidates.card := by
  by_contra h
  have growth : ∀ n ≤ rules.candidates.card, n ≤ (rules.layers n).card := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      have hn' : n ≤ rules.candidates.card := by omega
      have strict : rules.layers n ≠ rules.layers (n + 1) := by
        intro eq
        have h₁ := rules.stable_after eq.symm (rules.candidates.card - n)
        have h₂ := rules.stable_after eq.symm (rules.candidates.card + 1 - n)
        have ar₁ : n + (rules.candidates.card - n) = rules.candidates.card := by omega
        have ar₂ : n + (rules.candidates.card + 1 - n) = rules.candidates.card + 1 := by omega
        rw [ar₁] at h₁
        rw [ar₂] at h₂
        exact h (h₂.trans h₁.symm)
      have lt : (rules.layers n).card < (rules.layers (n + 1)).card :=
        lt_of_le_of_ne (Finset.card_le_card (rules.layers_mono_step n))
          (fun eq => strict (Finset.eq_of_subset_of_card_le (rules.layers_mono_step n) eq.ge))
      have := ih hn'
      omega
  have full : rules.layers rules.candidates.card = rules.candidates :=
    Finset.eq_of_subset_of_card_le (rules.layers_subset _) (growth _ (by omega))
  apply h
  apply Finset.Subset.antisymm
  · rw [full]
    exact rules.layers_subset _
  · exact rules.layers_mono_step _

def closure : Finset Node := rules.layers rules.candidates.card

theorem closure_fixed : rules.step rules.closure = rules.closure := rules.stabilized

theorem layers_subset_closure (n : Nat) : rules.layers n ⊆ rules.closure := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    change rules.step (rules.layers n) ⊆ _
    rw [← rules.closure_fixed]
    exact rules.step_mono ih

theorem mem_closure {s : Node} : s ∈ rules.closure ↔
    s ∈ rules.candidates ∧ rules.Ready rules.closure s := by
  conv_lhs => rw [← rules.closure_fixed]
  exact Finset.mem_filter

end Rules

end ACUIhE.FILO.Shortcuts.Saturation
