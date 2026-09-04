import ACUIHE.Optimized.Optimized.Automaton
import Mathlib.Data.Finset.Sort

/-!
Witness-carrying shortcut saturation for finite tree automata.

This is the paper-inspired core of the shortcut backend.  A shortcut entry
records an accepted tree for one automaton state.  New entries are resolved
only from entries produced at earlier rounds, so the table is an acyclic
derivation graph.  State lookup uses the numeric `FinEnum` identifier instead
of equality on the (often function-valued) state itself.
-/

namespace ACUIHE.Optimized.Shortcut

universe u

open ACUIHE.Solver.Search
open ACUIHE.Optimized.Optimized

abbrev StateId (State : Type u) [FinEnum State] :=
  Fin (FinEnum.card State)

def stateId {State : Type u} [FinEnum State] (state : State) : StateId State :=
  FinEnum.equiv state

/-- Enumerate only the supplied candidates, ordered by their canonical numeric
identifier.  In particular, this never enumerates the full `FinEnum` state
space, which can be enormous when states contain functions. -/
def candidateList {State : Type u} [FinEnum State]
    (candidates : Finset State) : List State := by
  let _ : LinearOrder State :=
    LinearOrder.lift' stateId
      (FinEnum.equiv : State ≃ StateId State).injective
  exact candidates.sort

@[simp]
theorem mem_candidateList {State : Type u} [FinEnum State]
    {candidates : Finset State} {state : State} :
    state ∈ candidateList candidates ↔ state ∈ candidates := by
  unfold candidateList
  let _ : LinearOrder State :=
    LinearOrder.lift' stateId
      (FinEnum.equiv : State ≃ StateId State).injective
  exact Finset.mem_sort (s := candidates) (fun a b : State => a ≤ b)

/-- An accepted-tree witness associated with its cheaply comparable state
identifier.  `state` is retained for the correctness invariant. -/
structure Entry (State Branch Label : Type u) [FinEnum State] where
  id : StateId State
  state : State
  tree : Tree Branch Label

def makeEntry {State Branch Label : Type u} [FinEnum State]
    (state : State) (tree : Tree Branch Label) : Entry State Branch Label :=
  { id := stateId state, state, tree }

/-- Lookup with an identifier that has already been computed. -/
def lookupId?
    {State Branch Label : Type u} [FinEnum State] :
    List (Entry State Branch Label) → StateId State → Option (Tree Branch Label)
  | [], _ => none
  | entry :: rest, id =>
      if entry.id = id then some entry.tree else lookupId? rest id

/-- Lookup an accepted-tree witness for a state. -/
def lookup?
    {State Branch Label : Type u} [FinEnum State]
    (entries : List (Entry State Branch Label)) (state : State) :
    Option (Tree Branch Label) :=
  lookupId? entries (stateId state)

/-- Every table entry has its canonical identifier and is a genuine accepted
tree for the stored state. -/
def TableValid
    {State Branch Label : Type u} [FinEnum State]
    (automaton : Automaton State Branch Label)
    (entries : List (Entry State Branch Label)) : Prop :=
  ∀ entry ∈ entries,
    entry.id = stateId entry.state ∧
      automaton.Accepts entry.state entry.tree

theorem lookupId?_isSome_of_mem
    {State Branch Label : Type u} [FinEnum State]
    {entries : List (Entry State Branch Label)}
    {entry : Entry State Branch Label} (membership : entry ∈ entries) :
    (lookupId? entries entry.id).isSome := by
  induction entries with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp membership with equality | inTail
      · subst head
        simp [lookupId?]
      · by_cases sameId : head.id = entry.id
        · simp [lookupId?, sameId]
        · simpa [lookupId?, sameId] using inductionHypothesis inTail

theorem lookup?_makeEntry_isSome_of_mem
    {State Branch Label : Type u} [FinEnum State]
    {entries : List (Entry State Branch Label)}
    {state : State} {tree : Tree Branch Label}
    (membership : makeEntry state tree ∈ entries) :
    (lookup? entries state).isSome := by
  exact lookupId?_isSome_of_mem membership

theorem lookup?_append_left
    {State Branch Label : Type u} [FinEnum State]
    (first second : List (Entry State Branch Label)) (state : State)
    {tree : Tree Branch Label}
    (found : lookup? first state = some tree) :
    lookup? (first ++ second) state = some tree := by
  unfold lookup? at found ⊢
  induction first with
  | nil => simp [lookupId?] at found
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append]
      by_cases sameId : head.id = stateId state
      · simpa [lookupId?, sameId] using found
      · simp only [lookupId?, sameId, ↓reduceIte] at found ⊢
        exact inductionHypothesis found

theorem lookup?_sound
    {State Branch Label : Type u} [FinEnum State]
    (automaton : Automaton State Branch Label)
    {entries : List (Entry State Branch Label)}
    (valid : TableValid automaton entries)
    {state : State} {tree : Tree Branch Label}
    (found : lookup? entries state = some tree) :
    automaton.Accepts state tree := by
  unfold lookup? at found
  induction entries with
  | nil => simp [lookupId?] at found
  | cons head tail inductionHypothesis =>
      have headValid := valid head (by simp)
      have tailValid : TableValid automaton tail := by
        intro entry membership
        exact valid entry (by simp [membership])
      by_cases sameId : head.id = stateId state
      · simp [lookupId?, sameId] at found
        subst tree
        have encoded : stateId head.state = stateId state := by
          rw [← headValid.1]
          exact sameId
        have stateEquality : head.state = state :=
          (FinEnum.equiv : State ≃ StateId State).injective encoded
        subst state
        exact headValid.2
      · simp [lookupId?, sameId] at found
        exact inductionHypothesis tailValid found

/-- Resolve one new shortcut from an already valid table.  A terminal label
produces a leaf; otherwise every successor must already have a cached
witness. -/
def resolve?
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (known : List (Entry State Branch Label))
    (state : State) : Option (Tree Branch Label) :=
  Automaton.firstResult? (fun label =>
    if _valid : automaton.locallyValid state label = true then
      if _terminal : automaton.terminal state label = true then
        some (.leaf label)
      else if resolved : ∀ branch,
          (lookup? known (automaton.next state label branch)).isSome then
        some (.node label fun branch =>
          (lookup? known (automaton.next state label branch)).get
            (resolved branch))
      else
        none
    else
      none) (FinEnum.toList Label)

theorem resolve?_sound
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    {known : List (Entry State Branch Label)}
    (knownValid : TableValid automaton known)
    (state : State) {tree : Tree Branch Label}
    (found : resolve? automaton known state = some tree) :
    automaton.Accepts state tree := by
  unfold resolve? at found
  rcases Automaton.firstResult?_sound _ _ found with
    ⟨label, _, labelFound⟩
  split at labelFound
  next locallyValid =>
    split at labelFound
    next terminal =>
      cases labelFound
      exact .leaf locallyValid terminal
    next nonterminal =>
      split at labelFound
      next resolved =>
        cases labelFound
        apply Automaton.Accepts.node locallyValid
        intro branch
        have childFound : lookup? known
            (automaton.next state label branch) = some
              ((lookup? known
                (automaton.next state label branch)).get
                  (resolved branch)) :=
          (Option.some_get (resolved branch)).symm
        exact lookup?_sound automaton knownValid childFound
      next unresolved => simp at labelFound
  next invalid => simp at labelFound

theorem resolve?_complete
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (known : List (Entry State Branch Label))
    (state : State) (label : Label)
    (locallyValid : automaton.locallyValid state label = true)
    (justification : automaton.terminal state label = true ∨
      ∀ branch,
        (lookup? known (automaton.next state label branch)).isSome) :
    ∃ tree, resolve? automaton known state = some tree := by
  unfold resolve?
  rcases justification with terminal | children
  · exact Automaton.firstResult?_complete _ _
      (result := .leaf label) (FinEnum.mem_toList label)
      (by simp [locallyValid, terminal])
  · by_cases terminal : automaton.terminal state label = true
    · exact Automaton.firstResult?_complete _ _
        (result := .leaf label) (FinEnum.mem_toList label)
        (by simp [locallyValid, terminal])
    · exact Automaton.firstResult?_complete _ _
        (result := .node label fun branch =>
          (lookup? known (automaton.next state label branch)).get
            (children branch))
        (FinEnum.mem_toList label)
        (by simp [locallyValid, terminal, children])

/-- Try to add one candidate.  Existing entries are retained; a new entry is
created only when it resolves from the baseline table. -/
def newEntry?
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (known : List (Entry State Branch Label))
    (state : State) : Option (Entry State Branch Label) :=
  match lookup? known state with
  | some _ => none
  | none => (resolve? automaton known state).map (makeEntry state)

/-- Add every candidate resolvable from the previous round.  All resolutions
use `known`, rather than entries added in this round, making derivation height
explicit and the witness graph acyclic. -/
def grow
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State)
    (known : List (Entry State Branch Label)) :
    List (Entry State Branch Label) :=
  known ++ (candidateList candidates).filterMap
    (newEntry? automaton known)

theorem newEntry?_sound
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    {known : List (Entry State Branch Label)}
    (knownValid : TableValid automaton known)
    (state : State) {entry : Entry State Branch Label}
    (found : newEntry? automaton known state = some entry) :
    ∃ tree, entry = makeEntry state tree ∧
      automaton.Accepts state tree := by
  unfold newEntry? at found
  cases existing : lookup? known state with
  | some tree => simp [existing] at found
  | none =>
      simp only [existing] at found
      cases resolved : resolve? automaton known state with
      | none => simp [resolved] at found
      | some tree =>
          simp [resolved] at found
          subst entry
          exact ⟨tree, rfl,
            resolve?_sound automaton knownValid state resolved⟩

theorem grow_valid
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State)
    {known : List (Entry State Branch Label)}
    (knownValid : TableValid automaton known) :
    TableValid automaton (grow automaton candidates known) := by
  intro entry membership
  rcases List.mem_append.mp membership with old | added
  · exact knownValid entry old
  · rcases List.mem_filterMap.mp added with
      ⟨state, _, generated⟩
    rcases newEntry?_sound automaton knownValid state generated with
      ⟨tree, rfl, accepted⟩
    exact ⟨rfl, accepted⟩

theorem lookup?_grow_of_lookup
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State)
    (known : List (Entry State Branch Label))
    (state : State)
    (present : (lookup? known state).isSome) :
    (lookup? (grow automaton candidates known) state).isSome := by
  cases found : lookup? known state with
  | none => simp [found] at present
  | some tree =>
      unfold grow
      rw [lookup?_append_left known
        ((candidateList candidates).filterMap
          (newEntry? automaton known)) state found]
      trivial

theorem lookup?_grow_of_resolve
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State)
    (known : List (Entry State Branch Label))
    (state : State) (candidate : state ∈ candidates)
    {tree : Tree Branch Label}
    (resolved : resolve? automaton known state = some tree) :
    (lookup? (grow automaton candidates known) state).isSome := by
  cases existing : lookup? known state with
  | some oldTree =>
      exact lookup?_grow_of_lookup automaton candidates known state (by
        rw [existing]
        trivial)
  | none =>
      have generated : newEntry? automaton known state =
          some (makeEntry state tree) := by
        simp [newEntry?, existing, resolved]
      have added : makeEntry state tree ∈
          (candidateList candidates).filterMap
            (newEntry? automaton known) := by
        apply List.mem_filterMap.mpr
        exact ⟨state, mem_candidateList.mpr candidate, generated⟩
      have inGrowth : makeEntry state tree ∈ grow automaton candidates known :=
        List.mem_append_right known added
      exact lookup?_makeEntry_isSome_of_mem inGrowth

/-- Witness tables after an exact number of bottom-up resolution rounds. -/
def stages
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State) : Nat →
      List (Entry State Branch Label)
  | 0 => []
  | round + 1 => grow automaton candidates (stages automaton candidates round)

theorem stages_valid
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State) :
    ∀ round, TableValid automaton (stages automaton candidates round) := by
  intro round
  induction round with
  | zero => simp [TableValid, stages]
  | succ round inductionHypothesis =>
      exact grow_valid automaton candidates inductionHypothesis

theorem productiveSteps_lookup
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State) :
    ∀ round state,
      state ∈ Automaton.productiveSteps automaton candidates round →
        (lookup? (stages automaton candidates round) state).isSome := by
  intro round
  induction round with
  | zero =>
      intro state membership
      simp [Automaton.productiveSteps, Automaton.iterateSteps] at membership
  | succ round inductionHypothesis =>
      intro state membership
      rw [Automaton.productiveSteps,
        Automaton.iterateSteps_succ_right,
        Automaton.mem_growProductive_iff] at membership
      rcases membership with old | ⟨candidate, step⟩
      · exact lookup?_grow_of_lookup automaton candidates
          (stages automaton candidates round) state
          (inductionHypothesis state (by
            simpa [Automaton.productiveSteps] using old))
      · rcases step with ⟨label, locallyValid, terminal | children⟩
        · rcases resolve?_complete automaton
            (stages automaton candidates round) state label locallyValid
            (.inl terminal) with ⟨tree, resolved⟩
          exact lookup?_grow_of_resolve automaton candidates
            (stages automaton candidates round) state candidate resolved
        · have childLookups : ∀ branch,
              (lookup? (stages automaton candidates round)
                (automaton.next state label branch)).isSome := by
            intro branch
            apply inductionHypothesis
            simpa [Automaton.productiveSteps] using children branch
          rcases resolve?_complete automaton
            (stages automaton candidates round) state label locallyValid
            (.inr childLookups) with ⟨tree, resolved⟩
          exact lookup?_grow_of_resolve automaton candidates
            (stages automaton candidates round) state candidate resolved

theorem stages_eq_iterateSteps
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State) : ∀ round,
    stages automaton candidates round =
      Automaton.iterateSteps (grow automaton candidates) round [] := by
  intro round
  induction round with
  | zero => rfl
  | succ round inductionHypothesis =>
      rw [stages, Automaton.iterateSteps_succ_right,
        inductionHypothesis]

theorem grow_eq_self_of_length_eq
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State)
    (known : List (Entry State Branch Label))
    (sameLength : (grow automaton candidates known).length = known.length) :
    grow automaton candidates known = known := by
  let added := (candidateList candidates).filterMap
    (newEntry? automaton known)
  have lengthEquation : known.length + added.length = known.length := by
    simpa [grow, added] using sameLength
  have addedLength : added.length = 0 := by omega
  have addedEmpty : added = [] := by
    simpa only [List.length_eq_zero_iff] using addedLength
  simp [grow, added, addedEmpty]

/-- Search the witness stages while retaining the current table.  Successful
search stops as soon as the initial state is resolved.  Failed search stops at
a table-size fixed point; `grow` only appends genuinely new entries, so equal
lengths imply an actual fixed point. -/
def searchRounds?
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State) (initial : State) : Nat →
      List (Entry State Branch Label) → Option (Tree Branch Label)
  | 0, known => lookup? known initial
  | remaining + 1, known =>
      match lookup? known initial with
      | some tree => some tree
      | none =>
          let next := grow automaton candidates known
          if next.length = known.length then
            none
          else
            searchRounds? automaton candidates initial remaining next

theorem searchRounds?_sound
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State) (initial : State) :
    ∀ rounds known {tree : Tree Branch Label},
      TableValid automaton known →
      searchRounds? automaton candidates initial rounds known = some tree →
      automaton.Accepts initial tree := by
  intro rounds
  induction rounds with
  | zero =>
      intro known tree valid found
      exact lookup?_sound automaton valid found
  | succ rounds inductionHypothesis =>
      intro known tree valid found
      simp only [searchRounds?] at found
      cases cached : lookup? known initial with
      | none =>
          rw [cached] at found
          dsimp only at found
          by_cases stable : (grow automaton candidates known).length =
              known.length
          · simp [stable] at found
          · simp only [stable, ↓reduceIte] at found
            exact inductionHypothesis
              (grow automaton candidates known) (tree := tree)
              (grow_valid automaton candidates valid) found
      | some cachedTree =>
          rw [cached] at found
          cases found
          exact lookup?_sound automaton valid cached

theorem searchRounds?_complete_of_final_lookup
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (candidates : Finset State) (initial : State) :
    ∀ rounds known,
      (lookup? (Automaton.iterateSteps (grow automaton candidates)
        rounds known) initial).isSome →
      (searchRounds? automaton candidates initial rounds known).isSome := by
  intro rounds
  induction rounds with
  | zero =>
      intro known finalLookup
      simpa [Automaton.iterateSteps, searchRounds?] using finalLookup
  | succ rounds inductionHypothesis =>
      intro known finalLookup
      simp only [Automaton.iterateSteps] at finalLookup
      simp only [searchRounds?]
      cases cached : lookup? known initial with
      | some tree => simp
      | none =>
          simp only
          by_cases stable : (grow automaton candidates known).length =
              known.length
          · simp only [stable, ↓reduceIte]
            have fixed : grow automaton candidates known = known :=
              grow_eq_self_of_length_eq automaton candidates known stable
            have finalNone : lookup?
                (Automaton.iterateSteps (grow automaton candidates)
                  rounds (grow automaton candidates known)) initial = none := by
              rw [fixed,
                Automaton.iterateSteps_fixed
                  (grow automaton candidates) fixed rounds]
              exact cached
            rw [finalNone] at finalLookup
            contradiction
          · simp only [stable, ↓reduceIte]
            exact inductionHypothesis
              (grow automaton candidates known) finalLookup

/-- Height used only by the fast prepass.  Failure of this prepass falls
through to exact fixed-point saturation, so this value cannot affect the
solver's answer. -/
def prepassHeight : Nat := 8

/-- Exact witness-producing automaton solver.  A small prepass handles common
shallow witnesses.  On the exact path, the cheap productive-state fixed point
decides rejection before witness construction.  The witness table itself also
stops at a fixed point; the reachable-set cardinality is only its proved
fallback bound, not a caller-selected cutoff. -/
def solve?
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (initial : State) : Option (Tree Branch Label) :=
  match Automaton.buildShallow? automaton prepassHeight initial with
  | some tree => some tree
  | none =>
      let reachable := Automaton.reachableStates automaton initial
      let productive := Automaton.productiveStates automaton reachable
      if initial ∈ productive then
        searchRounds? automaton reachable initial reachable.card []
      else
        none

theorem solve?_sound
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (initial : State) {tree : Tree Branch Label}
    (found : solve? automaton initial = some tree) :
    automaton.Accepts initial tree := by
  unfold solve? at found
  cases shallow : Automaton.buildShallow? automaton prepassHeight initial with
  | some shallowTree =>
      rw [shallow] at found
      cases found
      exact Automaton.buildShallow?_sound automaton prepassHeight initial shallow
  | none =>
      rw [shallow] at found
      dsimp only at found
      by_cases productive : initial ∈ Automaton.productiveStates automaton
          (Automaton.reachableStates automaton initial)
      · simp only [productive, ↓reduceIte] at found
        exact searchRounds?_sound automaton
          (Automaton.reachableStates automaton initial) initial _ []
          (by simp [TableValid]) found
      · simp [productive] at found

theorem solve?_complete
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (initial : State)
    (solution : ∃ tree, automaton.Accepts initial tree) :
    ∃ tree, solve? automaton initial = some tree := by
  rcases solution with ⟨tree, accepted⟩
  unfold solve?
  cases shallow : Automaton.buildShallow? automaton prepassHeight initial with
  | some shallowTree => exact ⟨shallowTree, rfl⟩
  | none =>
      let reachable := Automaton.reachableStates automaton initial
      have reachableInitial : initial ∈ reachable :=
        Automaton.initial_mem_reachableStates automaton initial
      have productiveInitial : initial ∈
          Automaton.productiveStates automaton reachable :=
        Automaton.accepts_mem_productiveStates automaton initial initial
          reachableInitial accepted
      simp only [reachable, productiveInitial, ↓reduceIte]
      have staged : initial ∈
          Automaton.productiveSteps automaton reachable reachable.card := by
        simpa [Automaton.productiveStates_eq_steps] using productiveInitial
      have cached := productiveSteps_lookup automaton reachable
        reachable.card initial staged
      rw [stages_eq_iterateSteps] at cached
      have searched := searchRounds?_complete_of_final_lookup automaton
        reachable initial reachable.card [] cached
      cases found : searchRounds? automaton reachable initial reachable.card [] with
      | none => simp [found] at searched
      | some result => exact ⟨result, rfl⟩

theorem solve?_eq_none_iff
    {State Branch Label : Type u}
    [FinEnum State] [FinEnum Branch] [FinEnum Label]
    (automaton : Automaton State Branch Label)
    (initial : State) :
    solve? automaton initial = none ↔
      ¬ ∃ tree, automaton.Accepts initial tree := by
  constructor
  · intro failed solution
    rcases solve?_complete automaton initial solution with ⟨tree, found⟩
    rw [failed] at found
    contradiction
  · intro rejected
    cases found : solve? automaton initial with
    | none => rfl
    | some tree =>
        exact False.elim (rejected ⟨tree,
          solve?_sound automaton initial found⟩)

end ACUIHE.Optimized.Shortcut
