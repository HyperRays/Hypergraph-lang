import ACUIHE.Solver.Search.Automaton
import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Basic

/-!
Finite-state saturation for tree-automaton emptiness.

The exact round bound is the cardinality of the automaton's state type, and
`productiveStages_fixed` proves that one more round cannot add a state.
Consequently failure at that point is unrestricted failure: there is no
accepted finite tree of any height.
-/

namespace ACUIHE.Solver.Search

universe u

namespace Automaton

variable {State Branch Label : Type u}

/-- A state can be justified in one step from already productive child
states. -/
def CanStep [Fintype Branch]
    (automaton : Automaton State Branch Label)
    (known : Finset State) (state : State) : Prop :=
  ∃ label,
    automaton.locallyValid state label = true ∧
      (automaton.terminal state label = true ∨
        ∀ branch, automaton.next state label branch ∈ known)

/-- Add every state with a leaf justification or with all child states
already known. -/
def grow [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (known : Finset State) : Finset State := by
  letI : DecidablePred (automaton.CanStep known) := fun state => by
    unfold CanStep
    infer_instance
  exact known ∪ Finset.univ.filter (automaton.CanStep known)

@[simp]
theorem mem_grow_iff [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (known : Finset State) (state : State) :
    state ∈ automaton.grow known ↔
      state ∈ known ∨ automaton.CanStep known state := by
  simp [grow]

theorem subset_grow [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (known : Finset State) :
    known ⊆ automaton.grow known := by
  intro state membership
  exact (mem_grow_iff automaton known state).mpr (.inl membership)

theorem grow_mono [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) :
    Monotone automaton.grow := by
  intro first second subset state membership
  rcases (mem_grow_iff automaton first state).mp membership with old | step
  · exact (mem_grow_iff automaton second state).mpr (.inl (subset old))
  · apply (mem_grow_iff automaton second state).mpr (.inr ?_)
    rcases step with ⟨label, valid, terminal | children⟩
    · exact ⟨label, valid, .inl terminal⟩
    · exact ⟨label, valid, .inr fun branch => subset (children branch)⟩

/-- The increasing sequence of productive-state approximants. -/
def productiveStages [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) : Nat → Finset State
  | 0 => ∅
  | round + 1 => automaton.grow (automaton.productiveStages round)

theorem productiveStages_subset_succ
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (round : Nat) :
    automaton.productiveStages round ⊆
      automaton.productiveStages (round + 1) :=
  automaton.subset_grow _

theorem productiveStages_mono
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) :
    Monotone automaton.productiveStages := by
  apply monotone_nat_of_le_succ
  exact automaton.productiveStages_subset_succ

private theorem productiveCard_stable
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (round : Nat)
    (equality : (automaton.productiveStages round).card =
      (automaton.productiveStages (round + 1)).card) :
    (automaton.productiveStages (round + 1)).card =
      (automaton.productiveStages (round + 2)).card := by
  have setsEqual : automaton.productiveStages round =
      automaton.productiveStages (round + 1) :=
    Finset.eq_of_subset_of_card_le
      (automaton.productiveStages_subset_succ round) equality.ge
  have growEqual :
      automaton.grow (automaton.productiveStages round) =
        automaton.productiveStages round := by
    change automaton.productiveStages (round + 1) =
      automaton.productiveStages round
    exact setsEqual.symm
  simp [productiveStages, growEqual]

/-- Saturation has reached a fixed point after at most one round per state. -/
theorem productiveStages_fixed
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) :
    automaton.productiveStages (FinEnum.card State) =
      automaton.productiveStages (FinEnum.card State + 1) := by
  let cardinality : Nat → Nat :=
    fun round => (automaton.productiveStages round).card
  have monotoneCardinality : Monotone cardinality := by
    intro first second order
    exact Finset.card_le_card (automaton.productiveStages_mono order)
  have boundedCardinality : ∀ round, cardinality round ≤ FinEnum.card State := by
    intro round
    rw [FinEnum.card_eq_fintypeCard]
    exact Finset.card_le_univ _
  have stableCardinality : ∀ round,
      cardinality round = cardinality (round + 1) →
        cardinality (round + 1) = cardinality (round + 2) := by
    intro round equality
    exact productiveCard_stable automaton round equality
  have cardEquality :
      cardinality (FinEnum.card State + 1) =
        cardinality (FinEnum.card State) :=
    Nat.stabilises_of_monotone monotoneCardinality boundedCardinality
      stableCardinality (Nat.le_succ _)
  exact Finset.eq_of_subset_of_card_le
    (automaton.productiveStages_subset_succ (FinEnum.card State))
    cardEquality.le

/-- The fully saturated set of states. -/
def productiveStates [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) : Finset State :=
  automaton.productiveStages (FinEnum.card State)

theorem grow_productiveStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) :
    automaton.grow automaton.productiveStates = automaton.productiveStates := by
  change automaton.productiveStages (FinEnum.card State + 1) =
    automaton.productiveStages (FinEnum.card State)
  exact automaton.productiveStages_fixed.symm

/-- Membership at stage `round` supplies an accepted tree of height at most
`round`. -/
theorem mem_productiveStages_has_boundedTree
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (round : Nat) (state : State)
    (membership : state ∈ automaton.productiveStages round) :
    ∃ tree : BoundedTree Branch Label round,
      automaton.Accepts state (tree.toTree round) := by
  induction round generalizing state with
  | zero => simp [productiveStages] at membership
  | succ round inductionHypothesis =>
      rw [productiveStages, mem_grow_iff] at membership
      rcases membership with old | step
      · rcases inductionHypothesis state old with ⟨tree, accepted⟩
        exact ⟨tree.liftBound round, by simpa using accepted⟩
      · rcases step with ⟨label, valid, terminal | children⟩
        · exact ⟨(label, none), .leaf valid terminal⟩
        · have childWitness : ∀ branch, ∃ tree : BoundedTree Branch Label round,
              automaton.Accepts (automaton.next state label branch)
                (tree.toTree round) :=
            fun branch => inductionHypothesis _ (children branch)
          choose childTrees childAccepted using childWitness
          exact ⟨(label, some childTrees), .node valid childAccepted⟩

/-- Every accepted finite tree starts in a saturated productive state. -/
theorem accepts_mem_productiveStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) {state : State}
    {tree : Tree Branch Label} (accepted : automaton.Accepts state tree) :
    state ∈ automaton.productiveStates := by
  induction accepted with
  | leaf valid terminal =>
      have step : automaton.CanStep automaton.productiveStates _ :=
        ⟨_, valid, .inl terminal⟩
      have membership : _ ∈ automaton.grow automaton.productiveStates :=
        (mem_grow_iff automaton _ _).mpr (.inr step)
      rwa [grow_productiveStates] at membership
  | node valid children inductionHypothesis =>
      have step : automaton.CanStep automaton.productiveStates _ :=
        ⟨_, valid, .inr inductionHypothesis⟩
      have membership : _ ∈ automaton.grow automaton.productiveStates :=
        (mem_grow_iff automaton _ _).mpr (.inr step)
      rwa [grow_productiveStates] at membership

/-- Saturation is an exact decision procedure for existence of any accepted
finite tree. -/
theorem mem_productiveStates_iff
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (state : State) :
    state ∈ automaton.productiveStates ↔
      ∃ tree, automaton.Accepts state tree := by
  constructor
  · intro membership
    rcases automaton.mem_productiveStages_has_boundedTree
        (FinEnum.card State) state membership with ⟨tree, accepted⟩
    exact ⟨tree.toTree _, accepted⟩
  · rintro ⟨tree, accepted⟩
    exact automaton.accepts_mem_productiveStates accepted

/-- Total automaton solver.  Its bound is derived from the finite state
space and is justified by `productiveStages_fixed`. -/
def solve? [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (initial : State) :
    Option (Tree Branch Label) :=
  match automaton.buildTree? 0 initial with
  | some tree => some tree
  | none => automaton.buildTree? (FinEnum.card State) initial

theorem solve?_sound
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (initial : State)
    {tree : Tree Branch Label} (result : automaton.solve? initial = some tree) :
    automaton.Accepts initial tree := by
  unfold solve? at result
  cases shallow : automaton.buildTree? 0 initial with
  | none =>
      rw [shallow] at result
      exact automaton.buildTree?_sound _ _ result
  | some found =>
      rw [shallow] at result
      cases result
      exact automaton.buildTree?_sound _ _ shallow

theorem solve?_complete
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (initial : State)
    (solution : ∃ tree, automaton.Accepts initial tree) :
    ∃ tree, automaton.solve? initial = some tree := by
  cases shallow : automaton.buildTree? 0 initial with
  | some tree => exact ⟨tree, by simp [solve?, shallow]⟩
  | none =>
      have productive : initial ∈ automaton.productiveStates :=
        (automaton.mem_productiveStates_iff initial).mpr solution
      rcases automaton.mem_productiveStages_has_boundedTree
          (FinEnum.card State) initial productive with ⟨tree, accepted⟩
      rcases automaton.buildTree?_complete _ _ tree accepted with
        ⟨result, found⟩
      exact ⟨result, by simp [solve?, shallow, found]⟩

theorem solve?_eq_none_iff
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (initial : State) :
    automaton.solve? initial = none ↔
      ¬ ∃ tree, automaton.Accepts initial tree := by
  constructor
  · intro noResult solution
    rcases automaton.solve?_complete initial solution with ⟨tree, found⟩
    rw [noResult] at found
    contradiction
  · intro noSolution
    cases result : automaton.solve? initial with
    | none => rfl
    | some tree => exact False.elim (noSolution ⟨tree,
        automaton.solve?_sound initial result⟩)

end Automaton

end ACUIHE.Solver.Search
