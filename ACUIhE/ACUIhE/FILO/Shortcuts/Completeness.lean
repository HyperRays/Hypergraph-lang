import ACUIhE.FILO.Shortcuts.Definition

/-!
# Completeness of shortcut saturation

Every finite-language solution induces a shortcut at each word. Induction
downwards from the longest word puts every noninitial shortcut into the
computed closure. No minimal-unifier assumption or guessed depth is used.
-/

namespace ACUIhE.FILO.Shortcuts

open Components ACUIh.Linear

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def atWord (s : System Var Hom) (iv : Column Var Hom) (word : List Hom) : Node Var Hom :=
  (atoms s).toFinset.filter (fun a => word ∈ (atomValue iv a).words)

@[simp] theorem mem_atWord (s : System Var Hom) (iv : Column Var Hom)
    (word : List Hom) (a : Atom Var Hom) :
    a ∈ atWord s iv word ↔ a ∈ atoms s ∧ word ∈ (atomValue iv a).words := by
  simp [atWord]

theorem var_in_atoms (s : System Var Hom) (x : Variable Var Hom) :
    .var x ∈ atoms s ↔ x ∈ s.names := by simp [atoms]

theorem atWord_local (s : System Var Hom) (iv : Column Var Hom) (solution : s.Solution iv)
    (word : List Hom) : Local s (decide (word = [])) (atWord s iv word) := by
  refine ⟨Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · intro q hq a ha hw
    have hwa := (mem_atWord _ _ _ _).mp hw |>.2
    have sub := (inequality_iff iv q).mp (solution.2 q hq)
    obtain ⟨b, hb, hwb⟩ := (mem_value _ _ _).mp (sub ((mem_value _ _ _).mpr ⟨a, ha, hwa⟩))
    refine ⟨b, hb, (mem_atWord _ _ _ _).mpr ⟨?_, hwb⟩⟩
    cases b with
    | const c => cases c; simp [atoms]
    | var x => exact (var_in_atoms _ _).mpr (s.name_of_mem hq (List.mem_append_right _ hb))
  · intro x hx
    cases x with
    | base v | constant p => trivial
    | role r p =>
      intro hw
      have hw := (mem_atWord _ _ _ _).mp hw |>.2
      have member := (Language.mem_derivative r (interpret iv p) word).mp hw
      exact List.mem_toFinset.mp (interpret_supported s.roles.toFinset iv solution.1 p
        (r :: word) member r (by simp))
  · constructor
    · simp [mem_atWord, atoms, atomValue]
    · intro x hx
      cases x with
      | base v | role r p => trivial
      | constant p =>
        have hp := s.parent_constant hx
        simp only [mem_atWord, var_in_atoms, hx, hp, true_and, atomValue, interpret,
          Language.mem_constantPart, decide_eq_true_eq]
        exact and_congr_right (fun h => by rw [h])

theorem atWord_resolves (s : System Var Hom) (iv : Column Var Hom) (word : List Hom) (r : Hom) :
    Resolves s (atWord s iv word) r (atWord s iv (r :: word)) := by
  intro x hx
  cases x with
  | base v | constant p => trivial
  | role t p =>
    intro eq
    subst t
    have hp := s.parent_role hx
    simp [mem_atWord, var_in_atoms, hx, hp, atomValue, interpret]

def maximumLength (s : System Var Hom) (iv : Column Var Hom) : Nat :=
  ((atoms s).toFinset.biUnion (fun a => (atomValue iv a).words)).sup List.length

theorem length_le_maximum (s : System Var Hom) (iv : Column Var Hom) (word : List Hom)
    (a : Atom Var Hom) (h : a ∈ atWord s iv word) : word.length ≤ maximumLength s iv := by
  obtain ⟨ha, hw⟩ := (mem_atWord _ _ _ _).mp h
  exact Finset.le_sup (f := List.length)
    (Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hw⟩)

theorem empty_mem_closure (s : System Var Hom) : ∅ ∈ (rules s).closure := by
  apply (Saturation.Rules.mem_closure (rules s)).mpr
  refine ⟨(mem_candidates s false ∅).mpr (local_empty s), ?_⟩
  intro r hr hn
  obtain ⟨x, hx, hn⟩ := hn
  cases x <;> simp_all

theorem noninitial_mem_closure (s : System Var Hom) (iv : Column Var Hom)
    (solution : s.Solution iv) (word : List Hom) (nonempty : word ≠ []) :
    atWord s iv word ∈ (rules s).closure := by
  have bounded : ∀ n word, maximumLength s iv < word.length + n → word ≠ [] →
      atWord s iv word ∈ (rules s).closure := by
    intro n
    induction n with
    | zero =>
      intro word bound _
      have empty : atWord s iv word = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have := length_le_maximum s iv word a ha
        omega
      rw [empty]
      exact empty_mem_closure s
    | succ n ih =>
      intro word bound nonempty
      apply (Saturation.Rules.mem_closure (rules s)).mpr
      refine ⟨(mem_candidates s false _).mpr ?_, ?_⟩
      · simpa [nonempty] using atWord_local s iv solution word
      · intro r hr _
        refine ⟨atWord s iv (r :: word), ih (r :: word) ?_ (by simp),
          atWord_resolves s iv word r⟩
        simp only [List.length_cons]
        omega
  exact bounded (maximumLength s iv + 1) word (by omega) nonempty

/-- A genuine solution always supplies a successful initial shortcut. -/
theorem solution_has_root (s : System Var Hom) (iv : Column Var Hom) (solution : s.Solution iv) :
    ∃ root ∈ candidates s true, (rules s).Ready (rules s).closure root := by
  refine ⟨atWord s iv [], (mem_candidates s true _).mpr ?_, ?_⟩
  · simpa using atWord_local s iv solution []
  · intro r _ _
    exact ⟨atWord s iv [r], noninitial_mem_closure s iv solution [r] (by simp),
      atWord_resolves s iv [] r⟩

end ACUIhE.FILO.Shortcuts
