import ACUIHE.Solver.Search.FiniteLanguageSystem.Completeness

/-!
# The finite-language FILO core

This module gives the finite flat presentation used by the FILO backend.
An atom `variable X p` denotes the language `p * X`; `constant p` denotes
the singleton language containing `p`.  Only words up to the largest input
coefficient are retained, so the atom universe is finite and closed under
taking tails.

A shortcut records the atoms containing one word.  The resolving relation is
exact: in the child selected by `r`, membership of `(X, r :: p)` is equivalent
to membership of `(X, p)` in the parent.  Bare variables are deliberately
unconstrained in a child, since they choose whether the newly reached word is
in the unknown language.
-/

namespace ACUIHE.Optimized.FILO

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

local instance encodableDecidableEq {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

local instance boolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

/-- A particle in the finite flat presentation. -/
inductive Atom (Variable Hom : Type u) where
  | var (index : Variable) (path : List Hom)
  | constant (path : List Hom)
deriving DecidableEq

namespace Atom

/-- The homomorphism prefix carried by an atom. -/
def path : Atom Variable Hom → List Hom
  | .var _ path => path
  | .constant path => path

@[simp]
theorem path_var (index : Variable) (word : List Hom) :
    path (.var index word : Atom Variable Hom) = word := rfl

@[simp]
theorem path_constant (word : List Hom) :
    path (.constant word : Atom Variable Hom) = word := rfl

end Atom

/-- One flattened anti-Horn subsumption.  Its meaning is that membership of
`target` forces membership of at least one atom in `sources`. -/
structure FlatClause (Variable Hom : Type u) where
  sources : Finset (Atom Variable Hom)
  target : Atom Variable Hom
deriving DecidableEq

end ACUIHE.Optimized.FILO

namespace ACUIHE.Solver.Search.FiniteLanguageSystem

open ACUIHE.Optimized.FILO
open ACUIHE.Solver.Linear

local instance encodableDecidableEq' {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

variable {Row Variable Hom : Type u}
  [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]

/-- All atoms occurring on one side of one row before suffix closure. -/
def sideAtoms (problem : FiniteLanguageSystem Row Variable Hom)
    (side : Bool) (row : Row) : Finset (Atom Variable Hom) :=
  (Finset.univ.biUnion fun index =>
      (problem.coefficient side row index).paths.image
        (Atom.var index)) ∪
    (problem.constant side row).paths.image Atom.constant

/-- The atom universe as an explicit list.  Keeping this list is important:
it lets the executable solver enumerate subsets without invoking the
noncomputable quotient-based `Finset.toList`. -/
def atomList (problem : FiniteLanguageSystem Row Variable Hom) :
    List (Atom Variable Hom) :=
  ((FinEnum.toList Variable).flatMap fun index =>
      (wordsUpTo (Alpha := Hom) problem.pathBound).map (Atom.var index)) ++
    (wordsUpTo (Alpha := Hom) problem.pathBound).map Atom.constant

/-- The finite suffix-closed atom universe. -/
def atoms (problem : FiniteLanguageSystem Row Variable Hom) :
    Finset (Atom Variable Hom) :=
  problem.atomList.toFinset

@[simp]
theorem var_mem_atoms_iff
    (problem : FiniteLanguageSystem Row Variable Hom)
    (index : Variable) (path : List Hom) :
    Atom.var index path ∈ problem.atoms ↔
      path.length ≤ problem.pathBound := by
  simp [atoms, atomList]

@[simp]
theorem constant_mem_atoms_iff
    (problem : FiniteLanguageSystem Row Variable Hom)
    (path : List Hom) :
    Atom.constant path ∈ problem.atoms ↔
      path.length ≤ problem.pathBound := by
  simp [atoms, atomList]

/-- The input system as flat anti-Horn clauses. -/
def flatClauses (problem : FiniteLanguageSystem Row Variable Hom) :
    Finset (FlatClause Variable Hom) :=
  Finset.univ.biUnion fun row =>
    (problem.sideAtoms false row).image fun target =>
      { sources := problem.sideAtoms true row, target := target }

/-- A shortcut is a membership pattern over the finite atom universe. -/
abbrev Shortcut := Finset (Atom Variable Hom)

/-- Exact semantic validity of a shortcut for all flat clauses. -/
def ShortcutValid (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) : Prop :=
  shortcut ⊆ problem.atoms ∧
    ∀ clause ∈ problem.flatClauses,
      clause.target ∈ shortcut →
        ∃ source ∈ clause.sources, source ∈ shortcut

/-- Executable local root condition for one atom. -/
def rootAtomCompatible
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    Atom Variable Hom → Bool
  | .var _ [] => true
  | .var index (head :: tail) =>
      decide (Atom.var index (head :: tail) ∉ shortcut)
  | .constant [] => decide (Atom.constant [] ∈ shortcut)
  | .constant (head :: tail) =>
      decide (Atom.constant (head :: tail) ∉ shortcut)

/-- At the root, constants have their fixed interpretation and no nonempty
prefix can contain the empty word.  Bare variables remain free. -/
def RootCompatible (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) : Prop :=
  shortcut ⊆ problem.atoms ∧
    ∀ atom ∈ problem.atoms,
      rootAtomCompatible shortcut atom = true

/-- Executable local resolver condition for one atom. -/
def resolveAtom
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom)
    (child : Shortcut (Variable := Variable) (Hom := Hom)) :
    Atom Variable Hom → Bool
  | .var _ [] => true
  | .var index (head :: tail) =>
      decide (Atom.var index (head :: tail) ∈ child ↔
        head = role ∧ Atom.var index tail ∈ parent)
  | .constant [] => decide (Atom.constant [] ∉ child)
  | .constant (head :: tail) =>
      decide (Atom.constant (head :: tail) ∈ child ↔
        head = role ∧ Atom.constant tail ∈ parent)

/-- `child` resolves `parent` with respect to the homomorphism `role`.
The equivalences are deliberately biconditionals: this exactness is the key
coherence property used in both soundness and completeness. -/
def Resolves (problem : FiniteLanguageSystem Row Variable Hom)
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom)
    (child : Shortcut (Variable := Variable) (Hom := Hom)) : Prop :=
  child ⊆ problem.atoms ∧
    ∀ atom ∈ problem.atoms,
      resolveAtom parent role child atom = true

/-- Executable membership condition for a directly constructed child. -/
def resolvingChildContains
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) (bare : Finset Variable) : Atom Variable Hom → Bool
    | .var index [] => decide (index ∈ bare)
    | .var index (head :: tail) =>
        decide (head = role ∧ Atom.var index tail ∈ parent)
    | .constant [] => false
    | .constant (head :: tail) =>
        decide (head = role ∧ Atom.constant tail ∈ parent)

/-- Construct the unique resolving child determined by a choice of bare
variable memberships.  All nonempty-path atoms are forced by the exact FILO
resolver equations. -/
def resolvingChild
    (problem : FiniteLanguageSystem Row Variable Hom)
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) (bare : Finset Variable) :
    Shortcut (Variable := Variable) (Hom := Hom) :=
  problem.atoms.filter fun atom =>
    resolvingChildContains parent role bare atom

/-- The complete, directly generated set of children resolving one
parent/role pair.  Its size is `2 ^ |Variable|`, independently of the number
of path atoms. -/
def resolvingChildList
    (problem : FiniteLanguageSystem Row Variable Hom)
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) :
    List (Shortcut (Variable := Variable) (Hom := Hom)) :=
  (FinEnum.Finset.enum (FinEnum.toList Variable)).map
    (problem.resolvingChild parent role)

theorem resolvingChild_resolves
    (problem : FiniteLanguageSystem Row Variable Hom)
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) (bare : Finset Variable) :
    problem.Resolves parent role
      (problem.resolvingChild parent role bare) := by
  constructor
  · exact Finset.filter_subset _ _
  · intro atom atomInUniverse
    cases atom with
    | var index path =>
        cases path with
        | nil => simp [resolveAtom]
        | cons head tail =>
            simp [resolvingChild, resolvingChildContains, resolveAtom,
              atomInUniverse]
    | constant path =>
        cases path with
        | nil => simp [resolvingChild, resolvingChildContains, resolveAtom,
            atomInUniverse]
        | cons head tail =>
            simp [resolvingChild, resolvingChildContains, resolveAtom,
              atomInUniverse]

theorem mem_resolvingChildList_of_resolves
    (problem : FiniteLanguageSystem Row Variable Hom)
    (parent child : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) (resolves : problem.Resolves parent role child) :
    child ∈ problem.resolvingChildList parent role := by
  let bare : Finset Variable :=
    Finset.univ.filter fun index => Atom.var index [] ∈ child
  have childEquality :
      problem.resolvingChild parent role bare = child := by
    ext atom
    by_cases atomInUniverse : atom ∈ problem.atoms
    · have resolved := resolves.2 atom atomInUniverse
      cases atom with
      | var index path =>
          cases path with
          | nil =>
              simp [resolvingChild, resolvingChildContains,
                atomInUniverse, bare]
          | cons head tail =>
              change decide (Atom.var index (head :: tail) ∈ child ↔
                head = role ∧ Atom.var index tail ∈ parent) = true at resolved
              have resolvedIff := of_decide_eq_true resolved
              simp [resolvingChild, resolvingChildContains,
                atomInUniverse, resolvedIff]
      | constant path =>
          cases path with
          | nil =>
              change decide (Atom.constant [] ∉ child) = true at resolved
              have missing := of_decide_eq_true resolved
              simp [resolvingChild, resolvingChildContains,
                atomInUniverse, missing]
          | cons head tail =>
              change decide (Atom.constant (head :: tail) ∈ child ↔
                head = role ∧ Atom.constant tail ∈ parent) = true at resolved
              have resolvedIff := of_decide_eq_true resolved
              simp [resolvingChild, resolvingChildContains,
                atomInUniverse, resolvedIff]
    · have atomNotInChild : atom ∉ child := fun membership =>
        atomInUniverse (resolves.1 membership)
      simp [resolvingChild, resolvingChildContains,
        atomInUniverse, atomNotInChild]
  apply List.mem_map.mpr
  refine ⟨bare, ?_, childEquality⟩
  simp [FinEnum.Finset.mem_enum, bare]

theorem resolves_of_mem_resolvingChildList
    (problem : FiniteLanguageSystem Row Variable Hom)
    (parent child : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom)
    (membership : child ∈ problem.resolvingChildList parent role) :
    problem.Resolves parent role child := by
  rcases List.mem_map.mp membership with ⟨bare, _, rfl⟩
  exact problem.resolvingChild_resolves parent role bare

/-- A shortcut may label a leaf exactly when every omitted child can be the
empty shortcut. -/
def Terminal (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) : Prop :=
  ∀ role, problem.Resolves shortcut role ∅

/-- All potential shortcuts.  Clause validity is tested during search rather
than baked into this list, which lets later search code prune incrementally. -/
def shortcutCandidates (problem : FiniteLanguageSystem Row Variable Hom) :
    Finset (Shortcut (Variable := Variable) (Hom := Hom)) :=
  problem.atoms.powerset

/-- Executable enumeration of the shortcut powerset. -/
def shortcutList (problem : FiniteLanguageSystem Row Variable Hom) :
    List (Shortcut (Variable := Variable) (Hom := Hom)) :=
  FinEnum.Finset.enum problem.atomList

@[simp]
theorem mem_shortcutList_iff
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    shortcut ∈ problem.shortcutList ↔ shortcut ⊆ problem.atoms := by
  simp only [shortcutList, FinEnum.Finset.mem_enum, atoms]
  constructor
  · intro membership atom atomInShortcut
    simpa using membership atom atomInShortcut
  · intro subset atom atomInShortcut
    simpa using subset atomInShortcut

@[simp]
theorem mem_shortcutCandidates_iff
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    shortcut ∈ problem.shortcutCandidates ↔ shortcut ⊆ problem.atoms := by
  simp [shortcutCandidates]

theorem sideAtoms_subset_atoms
    (problem : FiniteLanguageSystem Row Variable Hom)
    (side : Bool) (row : Row) :
    problem.sideAtoms side row ⊆ problem.atoms := by
  intro atom membership
  rcases Finset.mem_union.mp membership with variableMembership | constantMembership
  · rcases Finset.mem_biUnion.mp variableMembership with
      ⟨index, _, coefficient⟩
    rcases Finset.mem_image.mp coefficient with
      ⟨path, pathMembership, rfl⟩
    apply (problem.var_mem_atoms_iff index path).mpr
    exact problem.coefficient_path_length_le_pathBound
      side row index pathMembership
  · rcases Finset.mem_image.mp constantMembership with
      ⟨path, pathMembership, rfl⟩
    apply (problem.constant_mem_atoms_iff path).mpr
    exact problem.constant_path_length_le_pathBound side row pathMembership

theorem flatClause_target_mem_atoms
    (problem : FiniteLanguageSystem Row Variable Hom)
    {clause : FlatClause Variable Hom}
    (membership : clause ∈ problem.flatClauses) :
    clause.target ∈ problem.atoms := by
  rcases Finset.mem_biUnion.mp membership with ⟨row, _, inRow⟩
  rcases Finset.mem_image.mp inRow with ⟨target, inLeft, equality⟩
  subst clause
  exact problem.sideAtoms_subset_atoms false row inLeft

theorem flatClause_sources_subset_atoms
    (problem : FiniteLanguageSystem Row Variable Hom)
    {clause : FlatClause Variable Hom}
    (membership : clause ∈ problem.flatClauses) :
    clause.sources ⊆ problem.atoms := by
  rcases Finset.mem_biUnion.mp membership with ⟨row, _, inRow⟩
  rcases Finset.mem_image.mp inRow with ⟨target, inLeft, equality⟩
  subst clause
  exact problem.sideAtoms_subset_atoms true row

/-- Interpretation of one flat atom at one word under an assignment. -/
def AtomHolds (values : Variable → HomContext Hom) (word : List Hom) :
    Atom Variable Hom → Prop
  | .var index path =>
      ∃ suffix ∈ (values index).paths, path ++ suffix = word
  | .constant path => path = word

instance atomHoldsDecidable
    (values : Variable → HomContext Hom) (word : List Hom) :
    DecidablePred (AtomHolds values word) := by
  intro atom
  cases atom with
  | var index path =>
      simp only [AtomHolds]
      infer_instance
  | constant path =>
      simp only [AtomHolds]
      infer_instance

/-- The shortcut induced by a concrete assignment at a concrete word. -/
def semanticShortcut (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom) :
    Shortcut (Variable := Variable) (Hom := Hom) :=
  problem.atoms.filter (AtomHolds values word)

@[simp]
theorem mem_semanticShortcut_iff
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom)
    (atom : Atom Variable Hom) :
    atom ∈ problem.semanticShortcut values word ↔
      atom ∈ problem.atoms ∧ AtomHolds values word atom := by
  simp [semanticShortcut]

theorem semanticShortcut_subset_atoms
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom) :
    problem.semanticShortcut values word ⊆ problem.atoms := by
  intro atom membership
  exact (problem.mem_semanticShortcut_iff values word atom).mp membership |>.1

omit [FinEnum Row] [FinEnum Hom] in
/-- Membership in one evaluated side is exactly membership in one of its
flat atoms. -/
theorem mem_evaluate_iff_atom
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (side : Bool) (row : Row)
    (word : List Hom) :
    word ∈ (problem.evaluate side values row).paths ↔
      ∃ atom ∈ problem.sideAtoms side row,
        AtomHolds values word atom := by
  simp [FiniteLanguageSystem.evaluate, sideAtoms, AtomHolds,
    mem_paths_finset_sum]
  constructor
  · rintro (⟨index, coefficient, coefficientMembership,
        suffix, suffixMembership⟩ | constantMembership)
    rcases suffixMembership with ⟨suffixMembership, equality⟩
    subst word
    · exact ⟨Atom.var index coefficient,
        Or.inl ⟨index, coefficient, coefficientMembership, rfl⟩,
        suffix, suffixMembership, rfl⟩
    · exact ⟨Atom.constant word,
        Or.inr ⟨word, constantMembership, rfl⟩, rfl⟩
  · rintro ⟨atom, variableMembership | constantMembership, holds⟩
    · rcases variableMembership with
        ⟨index, coefficient, coefficientMembership, rfl⟩
      rcases holds with ⟨suffix, suffixMembership, equality⟩
      subst word
      exact Or.inl ⟨index, coefficient, coefficientMembership,
        suffix, suffixMembership, rfl⟩
    · rcases constantMembership with ⟨path, pathMembership, rfl⟩
      subst word
      exact Or.inr pathMembership

theorem semanticShortcut_valid
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom)
    (solution : problem.IsSolution values)
    (word : List Hom) :
    problem.ShortcutValid (problem.semanticShortcut values word) := by
  refine ⟨problem.semanticShortcut_subset_atoms values word, ?_⟩
  intro clause clauseMembership targetMembership
  rcases Finset.mem_biUnion.mp clauseMembership with ⟨row, _, inRow⟩
  rcases Finset.mem_image.mp inRow with ⟨target, targetInLeft, equality⟩
  subst clause
  have targetHolds :=
    (problem.mem_semanticShortcut_iff values word target).mp targetMembership |>.2
  have leftMembership : word ∈ (problem.evaluate false values row).paths :=
    (problem.mem_evaluate_iff_atom values false row word).mpr
      ⟨target, targetInLeft, targetHolds⟩
  have rightMembership :=
    (HomContext.le_iff_paths_subset _ _).mp (solution row) leftMembership
  rcases (problem.mem_evaluate_iff_atom values true row word).mp rightMembership with
    ⟨source, sourceInRight, sourceHolds⟩
  refine ⟨source, sourceInRight, ?_⟩
  apply (problem.mem_semanticShortcut_iff values word source).mpr
  exact ⟨problem.sideAtoms_subset_atoms true row sourceInRight, sourceHolds⟩

theorem semanticShortcut_rootCompatible
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) :
    problem.RootCompatible (problem.semanticShortcut values []) := by
  refine ⟨problem.semanticShortcut_subset_atoms values [], ?_⟩
  intro atom atomInUniverse
  cases atom with
  | var index path =>
      cases path with
      | nil => trivial
      | cons head tail =>
          simp [rootAtomCompatible, mem_semanticShortcut_iff,
            AtomHolds, atomInUniverse]
  | constant path =>
      cases path with
      | nil => simp [rootAtomCompatible, mem_semanticShortcut_iff,
          AtomHolds, atomInUniverse]
      | cons head tail =>
          simp [rootAtomCompatible, mem_semanticShortcut_iff,
            AtomHolds, atomInUniverse]

theorem semanticShortcut_resolves
    (problem : FiniteLanguageSystem Row Variable Hom)
    (values : Variable → HomContext Hom) (word : List Hom) (role : Hom) :
    problem.Resolves (problem.semanticShortcut values word) role
      (problem.semanticShortcut values (role :: word)) := by
  refine ⟨problem.semanticShortcut_subset_atoms values (role :: word), ?_⟩
  intro atom atomInUniverse
  cases atom with
  | var index path =>
      cases path with
      | nil => trivial
      | cons head tail =>
          simp only [resolveAtom, decide_eq_true_eq,
            mem_semanticShortcut_iff, atomInUniverse, true_and, AtomHolds]
          constructor
          · rintro ⟨suffix, suffixMembership, equality⟩
            have parts := List.cons.inj equality
            refine ⟨parts.1, ?_⟩
            refine ⟨?_, suffix, suffixMembership, parts.2⟩
            rw [problem.var_mem_atoms_iff] at atomInUniverse ⊢
            exact le_trans (Nat.le_succ tail.length) atomInUniverse
          · rintro ⟨rfl, tailMembership⟩
            rcases tailMembership with
              ⟨_, suffix, suffixMembership, equality⟩
            exact ⟨suffix, suffixMembership, by simp [equality]⟩
  | constant path =>
      cases path with
      | nil => simp [resolveAtom, mem_semanticShortcut_iff,
          AtomHolds, atomInUniverse]
      | cons head tail =>
          simp only [resolveAtom, decide_eq_true_eq,
            mem_semanticShortcut_iff, atomInUniverse, true_and, AtomHolds]
          constructor
          · intro equality
            have parts := List.cons.inj equality
            refine ⟨parts.1, ?_⟩
            refine ⟨?_, parts.2⟩
            rw [problem.constant_mem_atoms_iff] at atomInUniverse ⊢
            exact le_trans (Nat.le_succ tail.length) atomInUniverse
          · rintro ⟨rfl, tailMembership⟩
            exact congrArg (List.cons head) tailMembership.2

end FiniteLanguageSystem
