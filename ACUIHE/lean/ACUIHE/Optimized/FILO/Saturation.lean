import ACUIHE.Optimized.FILO.Completeness

/-!
# Bottom-up FILO saturation

This is the production search.  Stage zero is empty.  Each following stage
adds every valid height-zero shortcut and every shortcut whose role children
were witnessed in the preceding stage.  Stored trees make dependencies
acyclic and provide reconstruction witnesses directly.
-/

namespace ACUIHE.Solver.Search.FiniteLanguageSystem

open ACUIHE.Optimized.FILO
open ACUIHE.Solver.Search

universe u

local instance encodableDecidableEqSaturation
    {Alpha : Type*} [Encodable Alpha] : DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

variable {Row Variable Hom : Type u}
  [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]

abbrev SaturationEntry (Variable Hom : Type u) :=
  Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))

/-- Find the witness stored for an exact shortcut. -/
def lookupShortcut? :
    List (SaturationEntry Variable Hom) →
      Shortcut (Variable := Variable) (Hom := Hom) →
      Option (SaturationEntry Variable Hom)
  | [], _ => none
  | tree :: rest, shortcut =>
      if tree.root = shortcut then some tree
      else lookupShortcut? rest shortcut

def SaturationTableValid
    (problem : FiniteLanguageSystem Row Variable Hom)
    (entries : List (SaturationEntry Variable Hom)) : Prop :=
  ∀ tree ∈ entries, problem.Derivation tree

omit [FinEnum Hom] in
theorem lookupShortcut?_mem
    {entries : List (SaturationEntry Variable Hom)}
    {shortcut : Shortcut (Variable := Variable) (Hom := Hom)} {tree}
    (found : lookupShortcut? entries shortcut = some tree) :
    tree ∈ entries ∧ tree.root = shortcut := by
  induction entries with
  | nil => simp [lookupShortcut?] at found
  | cons head tail inductionHypothesis =>
      by_cases equality : head.root = shortcut
      · simp [lookupShortcut?, equality] at found
        subst tree
        exact ⟨by simp, equality⟩
      · simp [lookupShortcut?, equality] at found
        exact ⟨by simp [inductionHypothesis found |>.1],
          inductionHypothesis found |>.2⟩

theorem lookupShortcut?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {entries : List (SaturationEntry Variable Hom)}
    (valid : problem.SaturationTableValid entries)
    {shortcut : Shortcut (Variable := Variable) (Hom := Hom)} {tree}
    (found : lookupShortcut? entries shortcut = some tree) :
    tree.root = shortcut ∧ problem.Derivation tree := by
  induction entries with
  | nil => simp [lookupShortcut?] at found
  | cons head tail inductionHypothesis =>
      by_cases equality : head.root = shortcut
      · simp [lookupShortcut?, equality] at found
        subst tree
        exact ⟨equality, valid head (by simp)⟩
      · simp [lookupShortcut?, equality] at found
        exact inductionHypothesis (fun tree membership =>
          valid tree (by simp [membership])) found

omit [FinEnum Hom] in
theorem lookupShortcut?_complete
    {entries : List (SaturationEntry Variable Hom)}
    {tree : SaturationEntry Variable Hom}
    (membership : tree ∈ entries) :
    ∃ result, lookupShortcut? entries tree.root = some result := by
  induction entries with
  | nil => simp at membership
  | cons head rest inductionHypothesis =>
      by_cases equality : head.root = tree.root
      · exact ⟨head, by simp [lookupShortcut?, equality]⟩
      · have inRest : tree ∈ rest := by
          rcases List.mem_cons.mp membership with headEquality | inRest
          · subst head
            exact False.elim (equality rfl)
          · exact inRest
        rcases inductionHypothesis inRest with ⟨result, found⟩
        exact ⟨result, by simp [lookupShortcut?, equality, found]⟩

omit [FinEnum Hom] in
theorem lookupShortcut?_append_left
    (first second : List (SaturationEntry Variable Hom))
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom))
    {tree} (found : lookupShortcut? first shortcut = some tree) :
    lookupShortcut? (first ++ second) shortcut = some tree := by
  induction first with
  | nil => simp [lookupShortcut?] at found
  | cons head tail inductionHypothesis =>
      by_cases equality : head.root = shortcut
      · simpa [lookupShortcut?, equality] using found
      · simp only [List.cons_append, lookupShortcut?, equality,
          ↓reduceIte] at found ⊢
        exact inductionHypothesis found

/-- Find one already witnessed resolving child for a role. -/
def resolvedChild?
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) : Option (SaturationEntry Variable Hom) :=
  Automaton.firstResult? (lookupShortcut? known)
    (problem.resolvingChildList parent role)

theorem resolvedChild?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {known : List (SaturationEntry Variable Hom)}
    (valid : problem.SaturationTableValid known)
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) {tree}
    (found : problem.resolvedChild? known parent role = some tree) :
    problem.Resolves parent role tree.root ∧ problem.Derivation tree := by
  unfold resolvedChild? at found
  rcases Automaton.firstResult?_sound _ _ found with
    ⟨candidate, membership, candidateFound⟩
  have resolves := problem.resolves_of_mem_resolvingChildList
    parent candidate role membership
  have stored := problem.lookupShortcut?_sound valid candidateFound
  rw [stored.1]
  exact ⟨resolves, stored.2⟩

theorem resolvedChild?_complete
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) {tree}
    (membership : tree ∈ known)
    (resolves : problem.Resolves parent role tree.root) :
    ∃ result, problem.resolvedChild? known parent role = some result := by
  unfold resolvedChild?
  have candidate := problem.mem_resolvingChildList_of_resolves
    parent tree.root role resolves
  rcases lookupShortcut?_complete membership with ⟨result, found⟩
  exact Automaton.firstResult?_complete _
    (problem.resolvingChildList parent role)
    (candidate := tree.root) (result := result) candidate found

/-- Resolve one shortcut from the preceding stage. -/
def resolveShortcut?
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    Option (SaturationEntry Variable Hom) :=
  if _valid : problem.ShortcutValid shortcut then
    if _terminal : problem.Terminal shortcut then
      some (.leaf shortcut)
    else if complete : ∀ role,
        (problem.resolvedChild? known shortcut role).isSome then
      some (.node shortcut fun role =>
        (problem.resolvedChild? known shortcut role).get (complete role))
    else
      none
  else
    none

theorem resolveShortcut?_root
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom))
    {tree} (found : problem.resolveShortcut? known shortcut = some tree) :
    tree.root = shortcut := by
  unfold resolveShortcut? at found
  split at found
  next valid =>
    split at found
    next terminal => cases found; rfl
    next nonterminal =>
      split at found
      next complete => cases found; rfl
      next incomplete => simp at found
  next invalid => simp at found

theorem resolveShortcut?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {known : List (SaturationEntry Variable Hom)}
    (knownValid : problem.SaturationTableValid known)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom))
    {tree} (found : problem.resolveShortcut? known shortcut = some tree) :
    problem.Derivation tree := by
  unfold resolveShortcut? at found
  split at found
  next valid =>
    split at found
    next terminal =>
      cases found
      exact .leaf valid terminal
    next nonterminal =>
      split at found
      next complete =>
        cases found
        apply Derivation.node valid
        · intro role
          have childFound := Option.some_get (complete role) |>.symm
          exact (problem.resolvedChild?_sound knownValid shortcut role
            childFound).1
        · intro role
          have childFound := Option.some_get (complete role) |>.symm
          exact (problem.resolvedChild?_sound knownValid shortcut role
            childFound).2
      next incomplete => simp at found
  next invalid => simp at found

theorem resolveShortcut?_complete
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom))
    (valid : problem.ShortcutValid shortcut)
    (justification : problem.Terminal shortcut ∨
      ∀ role, ∃ tree ∈ known,
        problem.Resolves shortcut role tree.root) :
    ∃ tree, problem.resolveShortcut? known shortcut = some tree := by
  rcases justification with terminal | children
  · exact ⟨.leaf shortcut, by simp [resolveShortcut?, valid, terminal]⟩
  · by_cases terminal : problem.Terminal shortcut
    · exact ⟨.leaf shortcut, by simp [resolveShortcut?, valid, terminal]⟩
    · have complete : ∀ role,
          (problem.resolvedChild? known shortcut role).isSome := by
        intro role
        rcases children role with ⟨tree, membership, resolves⟩
        rcases problem.resolvedChild?_complete known shortcut role membership
            resolves with ⟨result, found⟩
        rw [found]
        trivial
      let child? := problem.resolvedChild? known shortcut
      exact ⟨.node shortcut fun role =>
          (child? role).get (complete role), by
        simp [resolveShortcut?, valid, terminal, complete, child?]⟩

/-- Do not insert a duplicate shortcut; otherwise add its newly resolved
witness if one exists. -/
def newSaturationEntry?
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    Option (SaturationEntry Variable Hom) :=
  match lookupShortcut? known shortcut with
  | some _ => none
  | none => problem.resolveShortcut? known shortcut

theorem newSaturationEntry?_eq_none_of_invalid
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom))
    (invalid : ¬ problem.ShortcutValid shortcut) :
    problem.newSaturationEntry? known shortcut = none := by
  unfold newSaturationEntry?
  cases found : lookupShortcut? known shortcut with
  | some tree => simp
  | none => simp [resolveShortcut?, invalid]

/-- Remove locally invalid shortcuts once before fixed-point iteration. -/
def validShortcutCandidates
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom))) :
    List (Shortcut (Variable := Variable) (Hom := Hom)) :=
  candidates.filter fun shortcut => decide (problem.ShortcutValid shortcut)

def growSaturation
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom)) :
    List (SaturationEntry Variable Hom) :=
  known ++ problem.shortcutList.filterMap
    (problem.newSaturationEntry? known)

/-- One saturation round over an explicitly cached candidate universe. -/
def growSaturationFrom
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom)))
    (known : List (SaturationEntry Variable Hom)) :
    List (SaturationEntry Variable Hom) :=
  known ++ candidates.filterMap (problem.newSaturationEntry? known)

@[simp]
theorem growSaturationFrom_shortcutList
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom)) :
    problem.growSaturationFrom problem.shortcutList known =
      problem.growSaturation known := rfl

theorem growSaturationFrom_validShortcutCandidates
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom)))
    (known : List (SaturationEntry Variable Hom)) :
    problem.growSaturationFrom
        (problem.validShortcutCandidates candidates) known =
      problem.growSaturationFrom candidates known := by
  unfold growSaturationFrom validShortcutCandidates
  congr 1
  induction candidates with
  | nil => rfl
  | cons shortcut rest inductionHypothesis =>
      by_cases valid : problem.ShortcutValid shortcut
      · simp [valid, List.filterMap_cons, inductionHypothesis]
      · have rejected := problem.newSaturationEntry?_eq_none_of_invalid
          known shortcut valid
        simp [valid, rejected, inductionHypothesis]

theorem newSaturationEntry?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {known : List (SaturationEntry Variable Hom)}
    (knownValid : problem.SaturationTableValid known)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom))
    {tree} (found : problem.newSaturationEntry? known shortcut = some tree) :
    tree.root = shortcut ∧ problem.Derivation tree := by
  unfold newSaturationEntry? at found
  cases existing : lookupShortcut? known shortcut with
  | some old => simp [existing] at found
  | none =>
      simp only [existing] at found
      exact ⟨problem.resolveShortcut?_root known shortcut found,
        problem.resolveShortcut?_sound knownValid shortcut found⟩

theorem growSaturation_valid
    (problem : FiniteLanguageSystem Row Variable Hom)
    {known : List (SaturationEntry Variable Hom)}
    (knownValid : problem.SaturationTableValid known) :
    problem.SaturationTableValid (problem.growSaturation known) := by
  intro tree membership
  rcases List.mem_append.mp membership with old | added
  · exact knownValid tree old
  · rcases List.mem_filterMap.mp added with
      ⟨shortcut, _, generated⟩
    exact (problem.newSaturationEntry?_sound knownValid shortcut generated).2

theorem growSaturation_has_of_resolve
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom))
    (candidate : shortcut ∈ problem.shortcutList)
    {tree} (resolved : problem.resolveShortcut? known shortcut = some tree) :
    ∃ result ∈ problem.growSaturation known, result.root = shortcut := by
  cases existing : lookupShortcut? known shortcut with
  | some old =>
      exact ⟨old, List.mem_append_left _ (lookupShortcut?_mem existing).1,
        (lookupShortcut?_mem existing).2⟩
  | none =>
      have generated : problem.newSaturationEntry? known shortcut = some tree := by
        simp [newSaturationEntry?, existing, resolved]
      refine ⟨tree, List.mem_append_right known ?_,
        problem.resolveShortcut?_root known shortcut resolved⟩
      exact List.mem_filterMap.mpr ⟨shortcut, candidate, generated⟩

/-- Bottom-up witness tables after an exact number of height layers. -/
def saturationStages
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Nat → List (SaturationEntry Variable Hom)
  | 0 => []
  | round + 1 => problem.growSaturation (problem.saturationStages round)

theorem saturationStages_valid
    (problem : FiniteLanguageSystem Row Variable Hom) :
    ∀ round, problem.SaturationTableValid (problem.saturationStages round) := by
  intro round
  induction round with
  | zero => simp [SaturationTableValid, saturationStages]
  | succ round inductionHypothesis =>
      exact problem.growSaturation_valid inductionHypothesis

/-!
## Early fixed-point evaluation

The cardinality bound remains the completeness specification, but production
must not rescan an already closed table for every remaining round.  The
following forward iterator stops as soon as `growSaturation` adds no shortcut.
It is proved extensionally equal to the original bounded stages.
-/

/-- Forward iteration of the saturation transformer from an arbitrary table. -/
def saturationIterations
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Nat → List (SaturationEntry Variable Hom) →
      List (SaturationEntry Variable Hom)
  | 0, known => known
  | rounds + 1, known =>
      problem.saturationIterations rounds (problem.growSaturation known)

theorem growSaturation_eq_self_of_length_eq
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (sameLength : (problem.growSaturation known).length = known.length) :
    problem.growSaturation known = known := by
  unfold growSaturation at sameLength ⊢
  have additionsEmpty :
      (problem.shortcutList.filterMap
        (problem.newSaturationEntry? known)).length = 0 := by
    simp only [List.length_append] at sameLength
    omega
  have additionsNil : problem.shortcutList.filterMap
      (problem.newSaturationEntry? known) = [] :=
    List.eq_nil_of_length_eq_zero additionsEmpty
  simp [additionsNil]

theorem saturationIterations_of_grow_eq_self
    (problem : FiniteLanguageSystem Row Variable Hom)
    (known : List (SaturationEntry Variable Hom))
    (closed : problem.growSaturation known = known) :
    ∀ rounds, problem.saturationIterations rounds known = known := by
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      simp [saturationIterations, closed, inductionHypothesis]

/-- Evaluate at most the completeness bound, returning immediately once the
table is closed under the saturation transformer. -/
def saturationFixedPoint
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Nat → List (SaturationEntry Variable Hom) →
      List (SaturationEntry Variable Hom)
  | 0, known => known
  | rounds + 1, known =>
      let next := problem.growSaturation known
      if next.length = known.length then
        known
      else
        problem.saturationFixedPoint rounds next

/-- Fixed-point evaluation with the shortcut universe supplied once and
shared by all rounds. -/
def saturationFixedPointFrom
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom))) :
    Nat → List (SaturationEntry Variable Hom) →
      List (SaturationEntry Variable Hom)
  | 0, known => known
  | rounds + 1, known =>
      let next := problem.growSaturationFrom candidates known
      if next.length = known.length then
        known
      else
        problem.saturationFixedPointFrom candidates rounds next

theorem saturationFixedPointFrom_shortcutList
    (problem : FiniteLanguageSystem Row Variable Hom) :
    ∀ rounds known,
      problem.saturationFixedPointFrom problem.shortcutList rounds known =
        problem.saturationFixedPoint rounds known := by
  intro rounds
  induction rounds with
  | zero => intro known; rfl
  | succ rounds inductionHypothesis =>
      intro known
      simp [saturationFixedPointFrom, saturationFixedPoint,
        growSaturationFrom, growSaturation, inductionHypothesis]

theorem saturationFixedPointFrom_validShortcutCandidates
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom))) :
    ∀ rounds known,
      problem.saturationFixedPointFrom
          (problem.validShortcutCandidates candidates) rounds known =
        problem.saturationFixedPointFrom candidates rounds known := by
  intro rounds
  induction rounds with
  | zero => intro known; rfl
  | succ rounds inductionHypothesis =>
      intro known
      simp only [saturationFixedPointFrom]
      rw [problem.growSaturationFrom_validShortcutCandidates]
      by_cases sameLength :
          (problem.growSaturationFrom candidates known).length = known.length
      · rw [if_pos sameLength, if_pos sameLength]
      · rw [if_neg sameLength, if_neg sameLength,
          inductionHypothesis]

theorem saturationFixedPoint_eq_iterations
    (problem : FiniteLanguageSystem Row Variable Hom) :
    ∀ rounds known,
      problem.saturationFixedPoint rounds known =
        problem.saturationIterations rounds known := by
  intro rounds
  induction rounds with
  | zero => intro known; rfl
  | succ rounds inductionHypothesis =>
      intro known
      simp only [saturationFixedPoint]
      by_cases sameLength :
          (problem.growSaturation known).length = known.length
      · rw [if_pos sameLength]
        have closed := growSaturation_eq_self_of_length_eq
          problem known sameLength
        rw [saturationIterations, closed]
        exact (saturationIterations_of_grow_eq_self
          problem known closed rounds).symm
      · rw [if_neg sameLength, saturationIterations,
          inductionHypothesis]

theorem saturationIterations_grow
    (problem : FiniteLanguageSystem Row Variable Hom) :
    ∀ rounds known,
      problem.saturationIterations rounds (problem.growSaturation known) =
        problem.growSaturation
          (problem.saturationIterations rounds known) := by
  intro rounds
  induction rounds with
  | zero => intro known; rfl
  | succ rounds inductionHypothesis =>
      intro known
      simpa [saturationIterations] using
        inductionHypothesis (problem.growSaturation known)

theorem saturationIterations_nil_eq_stages
    (problem : FiniteLanguageSystem Row Variable Hom) :
    ∀ rounds,
      problem.saturationIterations rounds [] =
        problem.saturationStages rounds := by
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [saturationIterations, saturationIterations_grow problem,
        inductionHypothesis]
      rfl

theorem saturationFixedPoint_nil_eq_stages
    (problem : FiniteLanguageSystem Row Variable Hom)
    (rounds : Nat) :
    problem.saturationFixedPoint rounds [] =
      problem.saturationStages rounds := by
  rw [saturationFixedPoint_eq_iterations problem,
    saturationIterations_nil_eq_stages problem]

theorem buildChild?_components
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom)))
    (build : Shortcut (Variable := Variable) (Hom := Hom) →
      Option (Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))))
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) {tree}
    (found : problem.buildChild? candidates build parent role = some tree) :
    ∃ child ∈ candidates,
      problem.Resolves parent role child ∧ build child = some tree := by
  unfold buildChild? at found
  rcases Automaton.firstResult?_sound _ _ found with
    ⟨child, membership, childFound⟩
  split at childFound
  next resolves => exact ⟨child, membership, resolves, childFound⟩
  next rejected => simp at childFound

/-- A depth-`bound` recursive witness is present after `bound + 1`
bottom-up height layers.  This theorem is the bridge from the finite-state
small-model proof to the production saturation algorithm. -/
theorem build?_mem_saturationStages
    (problem : FiniteLanguageSystem Row Variable Hom) :
    ∀ bound (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) {tree},
      problem.build? problem.shortcutList bound shortcut = some tree →
      shortcut ∈ problem.shortcutList →
      ∃ result ∈ problem.saturationStages (bound + 1),
        result.root = shortcut := by
  intro bound
  induction bound with
  | zero =>
      intro shortcut tree built candidate
      simp only [build?] at built
      split at built
      next accepted =>
        rcases problem.resolveShortcut?_complete [] shortcut accepted.1
            (.inl accepted.2) with ⟨resolvedTree, resolved⟩
        have added := problem.growSaturation_has_of_resolve [] shortcut
          candidate resolved
        simpa [saturationStages] using added
      next rejected => simp at built
  | succ bound inductionHypothesis =>
      intro shortcut tree built candidate
      simp only [build?] at built
      split at built
      next valid =>
        split at built
        next terminal =>
          rcases problem.resolveShortcut?_complete
              (problem.saturationStages (bound + 1)) shortcut valid
              (.inl terminal) with ⟨resolvedTree, resolved⟩
          have added := problem.growSaturation_has_of_resolve
            (problem.saturationStages (bound + 1)) shortcut candidate resolved
          simpa [saturationStages, Nat.add_assoc] using added
        next nonterminal =>
          split at built
          next complete =>
            have children : ∀ role, ∃ childTree ∈
                problem.saturationStages (bound + 1),
                problem.Resolves shortcut role childTree.root := by
              intro role
              have childFound := Option.some_get (complete role) |>.symm
              rcases problem.buildChild?_components problem.shortcutList
                  (problem.build? problem.shortcutList bound)
                  shortcut role childFound with
                ⟨child, childCandidate, resolves, childBuilt⟩
              rcases inductionHypothesis child childBuilt childCandidate with
                ⟨stagedTree, stagedMembership, rootEquality⟩
              exact ⟨stagedTree, stagedMembership,
                rootEquality ▸ resolves⟩
            rcases problem.resolveShortcut?_complete
                (problem.saturationStages (bound + 1)) shortcut valid
                (.inr children) with ⟨resolvedTree, resolved⟩
            have added := problem.growSaturation_has_of_resolve
              (problem.saturationStages (bound + 1)) shortcut candidate resolved
            simpa [saturationStages, Nat.add_assoc] using added
          next incomplete => simp at built
      next invalid => simp at built

theorem buildRoot?_components
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (found : problem.buildRoot? = some tree) :
    ∃ shortcut ∈ problem.shortcutList,
      problem.RootCompatible shortcut ∧
      problem.build? problem.shortcutList problem.shortcutList.length shortcut =
        some tree := by
  unfold buildRoot? at found
  rcases Automaton.firstResult?_sound _ _ found with
    ⟨shortcut, membership, shortcutFound⟩
  split at shortcutFound
  next rootCompatible =>
    exact ⟨shortcut, membership, rootCompatible, shortcutFound⟩
  next incompatible => simp at shortcutFound

/-- Find a root-compatible derivation in a completed table. -/
def findSaturatedRoot?
    (problem : FiniteLanguageSystem Row Variable Hom)
    (entries : List (SaturationEntry Variable Hom)) :
    Option (SaturationEntry Variable Hom) :=
  Automaton.firstResult? (fun tree =>
    if problem.RootCompatible tree.root then some tree else none) entries

theorem findSaturatedRoot?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {entries : List (SaturationEntry Variable Hom)}
    (valid : problem.SaturationTableValid entries)
    {tree} (found : problem.findSaturatedRoot? entries = some tree) :
    problem.RootCompatible tree.root ∧ problem.Derivation tree := by
  unfold findSaturatedRoot? at found
  rcases Automaton.firstResult?_sound _ _ found with
    ⟨candidate, membership, candidateFound⟩
  split at candidateFound
  next compatible =>
    have equality : candidate = tree := Option.some.inj candidateFound
    subst tree
    exact ⟨compatible, valid candidate membership⟩
  next incompatible => simp at candidateFound

theorem findSaturatedRoot?_complete
    (problem : FiniteLanguageSystem Row Variable Hom)
    (entries : List (SaturationEntry Variable Hom))
    {tree} (membership : tree ∈ entries)
    (compatible : problem.RootCompatible tree.root) :
    ∃ result, problem.findSaturatedRoot? entries = some result := by
  unfold findSaturatedRoot?
  exact Automaton.firstResult?_complete _ entries
    (candidate := tree) (result := tree) membership (by simp [compatible])

/-- Production FILO search: saturate height layers bottom-up, then select a
root-compatible witness. -/
def saturateRoot?
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Option (SaturationEntry Variable Hom) :=
  problem.findSaturatedRoot?
    (problem.saturationStages (problem.shortcutList.length + 1))

theorem saturateRoot?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree} (found : problem.saturateRoot? = some tree) :
    problem.RootCompatible tree.root ∧ problem.Derivation tree := by
  exact problem.findSaturatedRoot?_sound
    (problem.saturationStages_valid (problem.shortcutList.length + 1)) found

theorem saturateRoot?_complete
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → ACUIHE.Solver.Linear.HomContext Hom)
    (solution : problem.IsSolution values) :
    ∃ tree, problem.saturateRoot? = some tree := by
  rcases problem.buildRoot?_complete values solution with ⟨tree, found⟩
  rcases problem.buildRoot?_components found with
    ⟨shortcut, candidate, compatible, built⟩
  rcases problem.build?_mem_saturationStages problem.shortcutList.length
      shortcut built candidate with ⟨stagedTree, membership, rootEquality⟩
  have stagedCompatible : problem.RootCompatible stagedTree.root := by
    rw [rootEquality]
    exact compatible
  exact problem.findSaturatedRoot?_complete
    (problem.saturationStages (problem.shortcutList.length + 1))
    membership stagedCompatible

/-- Production fixed-point search.  This computes the same complete table as
`saturateRoot?`, but stops growing it as soon as a round adds no shortcut. -/
def saturateRootFast?
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Option (SaturationEntry Variable Hom) :=
  let candidates := problem.shortcutList
  let validCandidates := problem.validShortcutCandidates candidates
  problem.findSaturatedRoot?
    (problem.saturationFixedPointFrom validCandidates
      (candidates.length + 1) [])

theorem saturateRootFast?_eq_saturateRoot?
    (problem : FiniteLanguageSystem Row Variable Hom) :
    problem.saturateRootFast? = problem.saturateRoot? := by
  simp only [saturateRootFast?, saturateRoot?]
  rw [problem.saturationFixedPointFrom_validShortcutCandidates,
    problem.saturationFixedPointFrom_shortcutList,
    problem.saturationFixedPoint_nil_eq_stages]

theorem saturateRootFast?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree} (found : problem.saturateRootFast? = some tree) :
    problem.RootCompatible tree.root ∧ problem.Derivation tree := by
  rw [problem.saturateRootFast?_eq_saturateRoot?] at found
  exact problem.saturateRoot?_sound found

theorem saturateRootFast?_complete
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → ACUIHE.Solver.Linear.HomContext Hom)
    (solution : problem.IsSolution values) :
    ∃ tree, problem.saturateRootFast? = some tree := by
  rw [problem.saturateRootFast?_eq_saturateRoot?]
  exact problem.saturateRoot?_complete values solution

end ACUIHE.Solver.Search.FiniteLanguageSystem
