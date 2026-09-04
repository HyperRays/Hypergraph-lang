import ACUIHE.Solver.Search.Saturation

-- The requested module path intentionally contains `Optimized.Optimized`.
set_option linter.dupNamespace false

/-!
An exact automaton solver that is kept separate from the original bounded
depth-first implementation.

The solver first tries small tree heights in increasing order.  If that does
not find a witness, it constructs the transition closure reachable from the
initial state and computes the least productive-state fixed point inside that
closure.  An absent initial state is therefore an exact rejection, not a
heuristic cutoff.  If the initial state is productive, bounded search is run
with the cardinality of the reachable closure rather than the cardinality of
the full function-space state type.
-/

namespace ACUIHE.Optimized.Optimized

universe u

open ACUIHE.Solver.Search

namespace Automaton

variable {State Branch Label : Type u}

/-- Apply `step` a fixed number of times, starting with `value`. -/
def iterateSteps (step : α → α) : Nat → α → α
  | 0, value => value
  | remainingRounds + 1, value =>
      iterateSteps step remainingRounds (step value)

theorem iterateSteps_succ_right (step : α → α) (rounds : Nat) (value : α) :
    iterateSteps step (rounds + 1) value =
      step (iterateSteps step rounds value) := by
  induction rounds generalizing value with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      simp only [iterateSteps]
      exact inductionHypothesis (step value)

theorem iterateSteps_fixed (step : α → α) {value : α}
    (fixed : step value = value) :
    ∀ rounds, iterateSteps step rounds value = value := by
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [iterateSteps_succ_right, inductionHypothesis, fixed]

/-- Iterate until a fixed point is detected, with a proved finite fallback
bound.  Stopping early is observationally equal to running every iteration. -/
def iterateUntilStable [DecidableEq α] (step : α → α) : Nat → α → α
  | 0, value => value
  | remainingRounds + 1, value =>
      let next := step value
      if next = value then value
      else iterateUntilStable step remainingRounds next

theorem iterateUntilStable_eq_iterateSteps [DecidableEq α]
    (step : α → α) (rounds : Nat) (value : α) :
    iterateUntilStable step rounds value = iterateSteps step rounds value := by
  induction rounds generalizing value with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      simp only [iterateUntilStable, iterateSteps]
      by_cases fixed : step value = value
      · simp only [fixed, ↓reduceIte]
        exact (iterateSteps_fixed step fixed rounds).symm
      · simp only [fixed, ↓reduceIte]
        exact inductionHypothesis (step value)

theorem subset_iterateSteps
    (step : Finset α → Finset α)
    (extensive : ∀ values, values ⊆ step values)
    (rounds : Nat) (initial : Finset α) :
    initial ⊆ iterateSteps step rounds initial := by
  induction rounds with
  | zero => exact fun _ membership => membership
  | succ rounds inductionHypothesis =>
      rw [iterateSteps_succ_right]
      exact fun value membership =>
        extensive _ (inductionHypothesis membership)

private theorem iterateCard_stable
    (step : Finset α → Finset α)
    (extensive : ∀ values, values ⊆ step values)
    (initial : Finset α) (round : Nat)
    (equality : (iterateSteps step round initial).card =
      (iterateSteps step (round + 1) initial).card) :
    (iterateSteps step (round + 1) initial).card =
      (iterateSteps step (round + 2) initial).card := by
  have setsEqual : iterateSteps step round initial =
      iterateSteps step (round + 1) initial :=
    Finset.eq_of_subset_of_card_le
      (by rw [iterateSteps_succ_right]; exact extensive _)
      equality.ge
  rw [iterateSteps_succ_right, iterateSteps_succ_right, ← setsEqual]

/-- An extensive operation on finite sets has stabilized after at most one
round per possible element. -/
theorem iterateSteps_fixed_at_card
    [FinEnum α]
    (step : Finset α → Finset α)
    (extensive : ∀ values, values ⊆ step values)
    (initial : Finset α) :
    iterateSteps step (FinEnum.card α) initial =
      iterateSteps step (FinEnum.card α + 1) initial := by
  let cardinality : Nat → Nat :=
    fun round => (iterateSteps step round initial).card
  have monotoneCardinality : Monotone cardinality := by
    apply monotone_nat_of_le_succ
    intro round
    exact Finset.card_le_card (by
      rw [iterateSteps_succ_right]
      exact extensive _)
  have boundedCardinality : ∀ round, cardinality round ≤ FinEnum.card α := by
    intro round
    rw [FinEnum.card_eq_fintypeCard]
    exact Finset.card_le_univ _
  have stableCardinality : ∀ round,
      cardinality round = cardinality (round + 1) →
        cardinality (round + 1) = cardinality (round + 2) := by
    intro round equality
    exact iterateCard_stable step extensive initial round equality
  have cardEquality :
      cardinality (FinEnum.card α + 1) = cardinality (FinEnum.card α) :=
    Nat.stabilises_of_monotone monotoneCardinality boundedCardinality
      stableCardinality (Nat.le_succ _)
  exact Finset.eq_of_subset_of_card_le
    (by rw [iterateSteps_succ_right]; exact extensive _)
    cardEquality.le

/-- Every successor of a state under a locally valid label. -/
def successors
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (state : State) : Finset State :=
  Finset.univ.biUnion fun label =>
    if automaton.locallyValid state label then
      Finset.univ.image fun branch => automaton.next state label branch
    else
      ∅

/-- One breadth-wise transition-closure step. -/
def growReachable
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (known : Finset State) : Finset State :=
  known ∪ known.biUnion (successors automaton)

theorem subset_growReachable
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (known : Finset State) :
    known ⊆ growReachable automaton known :=
  Finset.subset_union_left

/-- Reachable-state closure with early fixed-point detection. -/
def reachableStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) : Finset State :=
  iterateUntilStable (growReachable automaton) (FinEnum.card State) {initial}

theorem reachableStates_eq_iterateSteps
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) :
    reachableStates automaton initial =
      iterateSteps (growReachable automaton) (FinEnum.card State) {initial} :=
  iterateUntilStable_eq_iterateSteps _ _ _

theorem initial_mem_reachableStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) :
    initial ∈ reachableStates automaton initial := by
  rw [reachableStates_eq_iterateSteps]
  exact subset_iterateSteps (growReachable automaton)
    (subset_growReachable automaton) _ _ (by simp)

theorem grow_reachableStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) :
    growReachable automaton (reachableStates automaton initial) =
      reachableStates automaton initial := by
  rw [reachableStates_eq_iterateSteps]
  rw [← iterateSteps_succ_right (growReachable automaton)
    (FinEnum.card State) ({initial} : Finset State)]
  exact (iterateSteps_fixed_at_card
    (growReachable automaton) (subset_growReachable automaton) {initial}).symm

theorem next_mem_reachableStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial state : State) (membership : state ∈ reachableStates automaton initial)
    (label : Label) (valid : automaton.locallyValid state label = true)
    (branch : Branch) :
    automaton.next state label branch ∈ reachableStates automaton initial := by
  have successorMembership : automaton.next state label branch ∈
      successors automaton state := by
    apply Finset.mem_biUnion.mpr
    refine ⟨label, Finset.mem_univ label, ?_⟩
    simp [valid]
  have grown : automaton.next state label branch ∈
      growReachable automaton (reachableStates automaton initial) := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr
      ⟨state, membership, successorMembership⟩
  rwa [grow_reachableStates] at grown

/-- Add all currently justifiable candidate states. -/
def growProductive
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates known : Finset State) : Finset State := by
  letI : DecidablePred (automaton.CanStep known) := fun state => by
    unfold ACUIHE.Solver.Search.Automaton.CanStep
    infer_instance
  exact known ∪ candidates.filter (automaton.CanStep known)

theorem mem_growProductive_iff
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates known : Finset State) (state : State) :
    state ∈ growProductive automaton candidates known ↔
      state ∈ known ∨
        state ∈ candidates ∧ automaton.CanStep known state := by
  simp [growProductive]

theorem subset_growProductive
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates known : Finset State) :
    known ⊆ growProductive automaton candidates known :=
  Finset.subset_union_left

theorem growProductive_subset_candidates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates known : Finset State) (subset : known ⊆ candidates) :
    growProductive automaton candidates known ⊆ candidates := by
  intro state membership
  rcases (mem_growProductive_iff automaton candidates known state).mp membership with
    old | added
  · exact subset old
  · exact added.1

/-- Productive approximants restricted to the reachable candidate set. -/
def productiveSteps
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) (round : Nat) : Finset State :=
  iterateSteps (growProductive automaton candidates) round ∅

theorem productiveSteps_subset_candidates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) :
    ∀ round, productiveSteps automaton candidates round ⊆ candidates := by
  intro round
  induction round with
  | zero => simp [productiveSteps, iterateSteps]
  | succ round inductionHypothesis =>
      rw [productiveSteps, iterateSteps_succ_right]
      exact growProductive_subset_candidates automaton candidates _
        (by simpa [productiveSteps] using inductionHypothesis)

private theorem productiveCard_stable
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) (round : Nat)
    (equality : (productiveSteps automaton candidates round).card =
      (productiveSteps automaton candidates (round + 1)).card) :
    (productiveSteps automaton candidates (round + 1)).card =
      (productiveSteps automaton candidates (round + 2)).card := by
  apply iterateCard_stable
    (growProductive automaton candidates)
    (subset_growProductive automaton candidates)
    ∅ round
  exact equality

theorem productiveSteps_fixed
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) :
    productiveSteps automaton candidates candidates.card =
      productiveSteps automaton candidates (candidates.card + 1) := by
  let cardinality : Nat → Nat :=
    fun round => (productiveSteps automaton candidates round).card
  have monotoneCardinality : Monotone cardinality := by
    apply monotone_nat_of_le_succ
    intro round
    exact Finset.card_le_card (by
      rw [productiveSteps, productiveSteps, iterateSteps_succ_right]
      exact subset_growProductive automaton candidates _)
  have boundedCardinality : ∀ round, cardinality round ≤ candidates.card := by
    intro round
    exact Finset.card_le_card
      (productiveSteps_subset_candidates automaton candidates round)
  have stableCardinality : ∀ round,
      cardinality round = cardinality (round + 1) →
        cardinality (round + 1) = cardinality (round + 2) := by
    intro round equality
    exact productiveCard_stable automaton candidates round equality
  have cardEquality :
      cardinality (candidates.card + 1) = cardinality candidates.card :=
    Nat.stabilises_of_monotone monotoneCardinality boundedCardinality
      stableCardinality (Nat.le_succ _)
  exact Finset.eq_of_subset_of_card_le
    (by
      rw [productiveSteps, productiveSteps, iterateSteps_succ_right]
      exact subset_growProductive automaton candidates _)
    cardEquality.le

/-- Exact productive-state fixed point over the reachable closure, with early
fixed-point detection in the executable implementation. -/
def productiveStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) : Finset State :=
  iterateUntilStable (growProductive automaton candidates) candidates.card ∅

theorem productiveStates_eq_steps
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) :
    productiveStates automaton candidates =
      productiveSteps automaton candidates candidates.card :=
  iterateUntilStable_eq_iterateSteps _ _ _

theorem grow_productiveStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) :
    growProductive automaton candidates (productiveStates automaton candidates) =
      productiveStates automaton candidates := by
  rw [productiveStates_eq_steps]
  change growProductive automaton candidates
      (iterateSteps (growProductive automaton candidates) candidates.card ∅) =
    iterateSteps (growProductive automaton candidates) candidates.card ∅
  rw [← iterateSteps_succ_right (growProductive automaton candidates)
    candidates.card ∅]
  exact (productiveSteps_fixed automaton candidates).symm

/-- Membership in a restricted productive stage supplies a witness with the
same height bound. -/
theorem mem_productiveSteps_has_boundedTree
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (candidates : Finset State) (round : Nat) (state : State)
    (membership : state ∈ productiveSteps automaton candidates round) :
    ∃ tree : BoundedTree Branch Label round,
      automaton.Accepts state (tree.toTree round) := by
  induction round generalizing state with
  | zero => simp [productiveSteps, iterateSteps] at membership
  | succ round inductionHypothesis =>
      rw [productiveSteps, iterateSteps_succ_right,
        mem_growProductive_iff] at membership
      rcases membership with old | ⟨_, step⟩
      · rcases inductionHypothesis state (by
          simpa [productiveSteps] using old) with ⟨tree, accepted⟩
        exact ⟨tree.liftBound round, by simpa using accepted⟩
      · rcases step with ⟨label, valid, terminal | children⟩
        · exact ⟨(label, none), .leaf valid terminal⟩
        · have childWitness : ∀ branch, ∃ tree : BoundedTree Branch Label round,
              automaton.Accepts (automaton.next state label branch)
                (tree.toTree round) :=
            fun branch => inductionHypothesis _ (by
              simpa [productiveSteps] using children branch)
          choose childTrees childAccepted using childWitness
          exact ⟨(label, some childTrees), .node valid childAccepted⟩

theorem accepts_mem_productiveStates
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial state : State)
    (reachable : state ∈ reachableStates automaton initial)
    {tree : Tree Branch Label} (accepted : automaton.Accepts state tree) :
    state ∈ productiveStates automaton (reachableStates automaton initial) := by
  induction accepted with
  | @leaf state label valid terminal =>
      have step : automaton.CanStep
          (productiveStates automaton (reachableStates automaton initial)) state :=
        ⟨label, valid, .inl terminal⟩
      have grown : state ∈ growProductive automaton
          (reachableStates automaton initial)
          (productiveStates automaton (reachableStates automaton initial)) :=
        (mem_growProductive_iff _ _ _ _).mpr (.inr ⟨reachable, step⟩)
      rwa [grow_productiveStates] at grown
  | @node state label children valid descendants inductionHypothesis =>
      have childReachable : ∀ branch,
          automaton.next state label branch ∈ reachableStates automaton initial :=
        fun branch => next_mem_reachableStates automaton initial state reachable
          label valid branch
      have step : automaton.CanStep
          (productiveStates automaton (reachableStates automaton initial)) state :=
        ⟨label, valid, .inr fun branch =>
          inductionHypothesis branch (childReachable branch)⟩
      have grown : state ∈ growProductive automaton
          (reachableStates automaton initial)
          (productiveStates automaton (reachableStates automaton initial)) :=
        (mem_growProductive_iff _ _ _ _).mpr (.inr ⟨reachable, step⟩)
      rwa [grow_productiveStates] at grown

/-- Try all bounds from zero through `maximum`, preferring the shallowest
witness. -/
def buildShallow?
    [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label) :
    Nat → State → Option (Tree Branch Label)
  | 0, state => automaton.buildTree? 0 state
  | maximum + 1, state =>
      match buildShallow? automaton maximum state with
      | some tree => some tree
      | none => automaton.buildTree? (maximum + 1) state

theorem buildShallow?_sound
    [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (maximum : Nat) (state : State) {tree : Tree Branch Label}
    (found : buildShallow? automaton maximum state = some tree) :
    automaton.Accepts state tree := by
  induction maximum with
  | zero =>
      exact automaton.buildTree?_sound 0 state found
  | succ maximum inductionHypothesis =>
      simp only [buildShallow?] at found
      cases shallow : buildShallow? automaton maximum state with
      | some earlier =>
          rw [shallow] at found
          cases found
          exact inductionHypothesis shallow
      | none =>
          rw [shallow] at found
          exact automaton.buildTree?_sound (maximum + 1) state found

/-- Separate exact solver.  Small witnesses are tried first; otherwise an
exact reachable-state/productivity fixed point decides rejection and supplies
a much smaller completeness bound for witness reconstruction. -/
def solve?
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) (shallowBound : Nat := 8) : Option (Tree Branch Label) :=
  match buildShallow? automaton shallowBound initial with
  | some tree => some tree
  | none =>
      let reachable := reachableStates automaton initial
      let productive := productiveStates automaton reachable
      if initial ∈ productive then
        automaton.buildTree? reachable.card initial
      else
        none

theorem solve?_sound
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) (shallowBound : Nat := 8)
    {tree : Tree Branch Label}
    (found : solve? automaton initial shallowBound = some tree) :
    automaton.Accepts initial tree := by
  unfold solve? at found
  cases shallow : buildShallow? automaton shallowBound initial with
  | some shallowTree =>
      rw [shallow] at found
      cases found
      exact buildShallow?_sound automaton shallowBound initial shallow
  | none =>
      rw [shallow] at found
      dsimp only at found
      by_cases productive : initial ∈ productiveStates automaton
          (reachableStates automaton initial)
      · simp only [productive, ↓reduceIte] at found
        exact automaton.buildTree?_sound _ initial found
      · simp [productive] at found

theorem solve?_complete
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) (shallowBound : Nat := 8)
    (solution : ∃ tree, automaton.Accepts initial tree) :
    ∃ tree, solve? automaton initial shallowBound = some tree := by
  rcases solution with ⟨acceptedTree, accepted⟩
  unfold solve?
  cases shallow : buildShallow? automaton shallowBound initial with
  | some tree => exact ⟨tree, rfl⟩
  | none =>
      let reachable := reachableStates automaton initial
      have reachableInitial : initial ∈ reachable :=
        initial_mem_reachableStates automaton initial
      have productiveInitial : initial ∈ productiveStates automaton reachable :=
        accepts_mem_productiveStates automaton initial initial
          reachableInitial accepted
      simp only [reachable, productiveInitial, ↓reduceIte]
      have staged : initial ∈ productiveSteps automaton reachable reachable.card := by
        simpa [productiveStates_eq_steps] using productiveInitial
      rcases mem_productiveSteps_has_boundedTree automaton reachable
          reachable.card initial staged with ⟨boundedTree, boundedAccepted⟩
      rcases automaton.buildTree?_complete reachable.card initial
          boundedTree boundedAccepted with ⟨tree, found⟩
      exact ⟨tree, found⟩

theorem solve?_eq_none_iff
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : ACUIHE.Solver.Search.Automaton State Branch Label)
    (initial : State) (shallowBound : Nat := 8) :
    solve? automaton initial shallowBound = none ↔
      ¬ ∃ tree, automaton.Accepts initial tree := by
  constructor
  · intro failed solution
    rcases solve?_complete automaton initial shallowBound solution with ⟨tree, found⟩
    rw [failed] at found
    contradiction
  · intro rejected
    cases found : solve? automaton initial shallowBound with
    | none => rfl
    | some tree =>
        exact False.elim (rejected ⟨tree,
          solve?_sound automaton initial shallowBound found⟩)

end Automaton

end ACUIHE.Optimized.Optimized
