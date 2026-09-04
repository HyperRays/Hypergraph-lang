import ACUIHE.Solver.Search.Tree

/-!
A small executable kernel for deterministic top-down automata on finite,
uniformly branching trees.

The later ACUIh construction uses states consisting of pending suffixes.
`accepts` is the semantic relation.  `checkBounded` and `findBounded?` are its
finite executable counterparts.
-/

namespace ACUIHE.Solver.Search

universe u

/-- A deterministic top-down finite-tree automaton. -/
structure Automaton (State : Type u) (Branch : Type u) (Label : Type u) where
  /-- A node label must be locally compatible with the current state. -/
  locallyValid : State → Label → Bool
  /-- A leaf may be used only when omitted descendants carry no obligation. -/
  terminal : State → Label → Bool
  /-- State passed to the child selected by an alphabet symbol. -/
  next : State → Label → Branch → State

namespace Automaton

variable {State : Type u} {Branch : Type u} {Label : Type u}

/-- Exact acceptance of an unbounded finite tree. -/
inductive Accepts (automaton : Automaton State Branch Label) :
    State → Tree Branch Label → Prop where
  | leaf {state label} :
      automaton.locallyValid state label = true →
      automaton.terminal state label = true →
      Accepts automaton state (.leaf label)
  | node {state label children} :
      automaton.locallyValid state label = true →
      (∀ branch, Accepts automaton (automaton.next state label branch)
        (children branch)) →
      Accepts automaton state (.node label children)

/-- Executably check a height-indexed tree. -/
def checkBounded
    [Fintype Branch]
    (automaton : Automaton State Branch Label) :
    (bound : Nat) → State → BoundedTree Branch Label bound → Bool
  | 0, state, label =>
      automaton.locallyValid state label && automaton.terminal state label
  | _bound + 1, state, (label, none) =>
      automaton.locallyValid state label && automaton.terminal state label
  | bound + 1, state, (label, some children) =>
      automaton.locallyValid state label &&
        decide (∀ branch, checkBounded automaton bound
          (automaton.next state label branch) (children branch) = true)

@[simp]
theorem checkBounded_eq_true_iff
    [Fintype Branch]
    (automaton : Automaton State Branch Label)
    (bound : Nat) (state : State) (tree : BoundedTree Branch Label bound) :
    automaton.checkBounded bound state tree = true ↔
      automaton.Accepts state (tree.toTree bound) := by
  induction bound generalizing state with
  | zero =>
      simp only [checkBounded, BoundedTree.toTree, Bool.and_eq_true]
      exact ⟨fun checked => .leaf checked.1 checked.2, fun accepted => by
        cases accepted with
        | leaf valid terminal => exact ⟨valid, terminal⟩⟩
  | succ bound inductionHypothesis =>
      rcases tree with ⟨label, children⟩
      cases children with
      | none =>
          simp only [checkBounded, BoundedTree.toTree, Bool.and_eq_true]
          exact ⟨fun checked => .leaf checked.1 checked.2, fun accepted => by
            cases accepted with
            | leaf valid terminal => exact ⟨valid, terminal⟩⟩
      | some children =>
          simp only [checkBounded, BoundedTree.toTree, Bool.and_eq_true,
            decide_eq_true_eq, inductionHypothesis]
          exact ⟨fun checked => .node checked.1 checked.2, fun accepted => by
            cases accepted with
            | node valid descendants => exact ⟨valid, descendants⟩⟩

/-- Return the first element of a list that passes a Boolean predicate. -/
def firstPassing? {Alpha : Type u} (predicate : Alpha → Bool) :
    List Alpha → Option Alpha
  | [] => none
  | value :: rest =>
      if predicate value then some value else firstPassing? predicate rest

theorem firstPassing?_sound
    {Alpha : Type u} {predicate : Alpha → Bool} {values : List Alpha}
    {value : Alpha} (result : firstPassing? predicate values = some value) :
    value ∈ values ∧ predicate value = true := by
  induction values with
  | nil => simp [firstPassing?] at result
  | cons head tail inductionHypothesis =>
      by_cases passed : predicate head = true
      · simp [firstPassing?, passed] at result
        subst value
        exact ⟨by simp, passed⟩
      · simp [firstPassing?, passed] at result
        exact ⟨by simp [inductionHypothesis result |>.1],
          inductionHypothesis result |>.2⟩

theorem firstPassing?_complete
    {Alpha : Type u} {predicate : Alpha → Bool} {values : List Alpha}
    {value : Alpha} (membership : value ∈ values)
    (passed : predicate value = true) :
    ∃ result, firstPassing? predicate values = some result := by
  induction values with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      by_cases headPassed : predicate head = true
      · exact ⟨head, by simp [firstPassing?, headPassed]⟩
      · have valueInTail : value ∈ tail := by
          rcases List.mem_cons.mp membership with equality | inTail
          · subst value
            exact False.elim (headPassed passed)
          · exact inTail
        rcases inductionHypothesis valueInTail with ⟨result, found⟩
        exact ⟨result, by simp [firstPassing?, headPassed, found]⟩

/-- Search every tree up to an internally selected height. -/
def findBounded?
    [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (bound : Nat) (state : State) : Option (Tree Branch Label) :=
  (firstPassing? (fun tree => automaton.checkBounded bound state tree)
      (FinEnum.toList (BoundedTree Branch Label bound))) |>.map
        (BoundedTree.toTree bound)

/-- A tree returned by finite automaton search is genuinely accepted. -/
theorem findBounded?_sound
    [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (bound : Nat) (state : State) {tree : Tree Branch Label}
    (result : automaton.findBounded? bound state = some tree) :
    automaton.Accepts state tree := by
  unfold findBounded? at result
  cases found : firstPassing?
      (fun candidate => automaton.checkBounded bound state candidate)
      (FinEnum.toList (BoundedTree Branch Label bound)) with
  | none => simp [found] at result
  | some candidate =>
      simp only [found, Option.map_some] at result
      cases result
      apply (checkBounded_eq_true_iff automaton bound state candidate).mp
      exact firstPassing?_sound found |>.2

/-- Every accepted indexed tree is found by finite search at that height. -/
theorem findBounded?_complete
    [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (bound : Nat) (state : State) (tree : BoundedTree Branch Label bound)
    (accepted : automaton.Accepts state (tree.toTree bound)) :
    ∃ result, automaton.findBounded? bound state = some result := by
  have checked : automaton.checkBounded bound state tree = true :=
    (checkBounded_eq_true_iff automaton bound state tree).mpr accepted
  unfold findBounded?
  cases found : firstPassing?
      (fun candidate => automaton.checkBounded bound state candidate)
      (FinEnum.toList (BoundedTree Branch Label bound)) with
  | none =>
      rcases firstPassing?_complete
          (value := tree) (FinEnum.mem_toList tree) checked with
        ⟨result, resultFound⟩
      rw [found] at resultFound
      contradiction
  | some candidate =>
      exact ⟨candidate.toTree bound, rfl⟩

/-- Return the first successful optional result in a finite list. -/
def firstResult? {Alpha Beta : Type u} (attempt : Alpha → Option Beta) :
    List Alpha → Option Beta
  | [] => none
  | value :: rest =>
      match attempt value with
      | some result => some result
      | none => firstResult? attempt rest

theorem firstResult?_sound
    {Alpha Beta : Type u} (attempt : Alpha → Option Beta)
    (candidates : List Alpha) {result : Beta}
    (found : firstResult? attempt candidates = some result) :
    ∃ candidate ∈ candidates, attempt candidate = some result := by
  induction candidates with
  | nil => simp [firstResult?] at found
  | cons candidate candidates inductionHypothesis =>
      simp only [firstResult?] at found
      cases candidateResult : attempt candidate with
      | none =>
          rw [candidateResult] at found
          rcases inductionHypothesis found with ⟨witness, membership, result⟩
          exact ⟨witness, by simp [membership], result⟩
      | some value =>
          rw [candidateResult] at found
          cases found
          exact ⟨candidate, by simp, candidateResult⟩

theorem firstResult?_complete
    {Alpha Beta : Type u} (attempt : Alpha → Option Beta)
    (candidates : List Alpha) {candidate : Alpha} {result : Beta}
    (membership : candidate ∈ candidates)
    (found : attempt candidate = some result) :
    ∃ returned, firstResult? attempt candidates = some returned := by
  induction candidates with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at membership
      rcases membership with equality | membership
      · subst head
        simp [firstResult?, found]
      · cases headResult : attempt head with
        | none =>
            simpa [firstResult?, headResult] using
              inductionHypothesis membership
        | some value => exact ⟨value, by simp [firstResult?, headResult]⟩

/-- Search directly for an accepted tree of depth at most `bound`.  Unlike
enumerating the entire finite type of bounded trees, this explores one label
and its independently solved children at a time. -/
def buildTree?
    [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) :
    Nat → State → Option (Tree Branch Label)
  | 0, state =>
      firstResult? (fun label =>
        if automaton.locallyValid state label = true ∧
            automaton.terminal state label = true then
          some (.leaf label)
        else
          none) (FinEnum.toList Label)
  | bound + 1, state =>
      firstResult? (fun label =>
        if _valid : automaton.locallyValid state label = true then
          if _terminal : automaton.terminal state label = true then
            some (.leaf label)
          else if complete : ∀ branch,
              (buildTree? automaton bound
                (automaton.next state label branch)).isSome then
            some (.node label fun branch =>
              (buildTree? automaton bound
                (automaton.next state label branch)).get (complete branch))
          else
            none
        else
          none) (FinEnum.toList Label)

/-- Direct bounded search only returns accepted trees. -/
theorem buildTree?_sound
    [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (bound : Nat) (state : State)
    {tree : Tree Branch Label}
    (found : automaton.buildTree? bound state = some tree) :
    automaton.Accepts state tree := by
  induction bound generalizing state tree with
  | zero =>
      unfold buildTree? at found
      rcases firstResult?_sound _ _ found with ⟨label, _, labelFound⟩
      split at labelFound
      next accepted =>
        cases labelFound
        exact .leaf accepted.1 accepted.2
      next rejected => simp at labelFound
  | succ bound inductionHypothesis =>
      unfold buildTree? at found
      rcases firstResult?_sound _ _ found with ⟨label, _, labelFound⟩
      split at labelFound
      next valid =>
        split at labelFound
        next terminal =>
          cases labelFound
          exact .leaf valid terminal
        next nonterminal =>
          split at labelFound
          next complete =>
            cases labelFound
            apply Accepts.node valid
            intro branch
            have childFound : automaton.buildTree? bound
                (automaton.next state label branch) = some
                  ((automaton.buildTree? bound
                    (automaton.next state label branch)).get
                      (complete branch)) :=
              (Option.some_get (complete branch)).symm
            exact inductionHypothesis _ childFound
          next incomplete => simp at labelFound
      next invalid => simp at labelFound

/-- Every accepted height-indexed tree is found by direct bounded search. -/
theorem buildTree?_complete
    [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label) (bound : Nat) (state : State)
    (tree : BoundedTree Branch Label bound)
    (accepted : automaton.Accepts state (tree.toTree bound)) :
    ∃ result, automaton.buildTree? bound state = some result := by
  induction bound generalizing state with
  | zero =>
      cases accepted with
      | leaf valid terminal =>
          exact firstResult?_complete _ _
            (result := .leaf tree) (FinEnum.mem_toList tree)
            (by simp [valid, terminal])
  | succ bound inductionHypothesis =>
      rcases tree with ⟨label, children⟩
      cases children with
      | none =>
          cases accepted with
          | leaf valid terminal =>
              exact firstResult?_complete _ _
                (result := .leaf label) (FinEnum.mem_toList label)
                (by simp [valid, terminal])
      | some children =>
          cases accepted with
          | node valid descendants =>
              have childResults : ∀ branch,
                  (automaton.buildTree? bound
                    (automaton.next state label branch)).isSome := by
                intro branch
                rcases inductionHypothesis
                    (automaton.next state label branch) (children branch)
                    (descendants branch) with ⟨result, found⟩
                rw [found]
                trivial
              by_cases terminal : automaton.terminal state label = true
              · exact firstResult?_complete _ _
                  (result := .leaf label) (FinEnum.mem_toList label)
                  (by simp [valid, terminal])
              · exact firstResult?_complete _ _
                  (result := .node label fun branch =>
                    (automaton.buildTree? bound
                      (automaton.next state label branch)).get
                        (childResults branch))
                  (FinEnum.mem_toList label)
                  (by simp [valid, terminal, childResults])

end Automaton

end ACUIHE.Solver.Search
