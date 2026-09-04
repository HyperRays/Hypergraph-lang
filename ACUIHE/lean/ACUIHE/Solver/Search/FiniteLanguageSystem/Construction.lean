import ACUIHE.Solver.Search.Saturation
import ACUIHE.Solver.Search.FiniteLanguageSystem.Problem

/-!
The exact finite-tree automaton for a finite-language inequality system.

Candidate values are finite languages.  The tree stores their mirrored words:
at a node reached by `reverse word`, its label records precisely the variables
whose value contains `word`.  Mirroring puts each fixed coefficient after the
unknown word.  Automaton states therefore only need to remember suffixes of
input coefficients, a finite input-derived state space.
-/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u

local instance finiteLanguageDecidableEq {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

local instance finiteLanguageBoolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

/-- The finite pending-suffix alphabet for a language system. -/
abbrev PendingWord
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :=
  BoundedWord Hom (problem.pathBound)

/-- A state stores pending coefficient suffixes for every row and side.
`false` is the left side and `true` is the right side. -/
abbrev PendingState
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :=
  Row → Bool → Finset (PendingWord problem)

instance pendingStateFinEnum
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) : FinEnum (PendingState problem) :=
  inferInstanceAs (FinEnum
    (Row → Bool → Finset (PendingWord problem)))

/-- A node label records membership in every unknown finite language. -/
abbrev VariableLabel (Variable : Type u) := Finset Variable

private def reverseWords
    {Hom : Type u} [FinEnum Hom] [Encodable Hom] {bound : Nat}
    (context : HomContext Hom)
    (bounded : ∀ path ∈ context.paths, path.length ≤ bound) :
    Finset (BoundedWord Hom bound) :=
  context.paths.attach.image fun path =>
    BoundedWord.reverseOf path.1 (bounded path.1 path.2)

private theorem mem_reverseWords_iff
    {Hom : Type u} [FinEnum Hom] [Encodable Hom] {bound : Nat}
    (context : HomContext Hom)
    (bounded : ∀ path ∈ context.paths, path.length ≤ bound)
    (word : BoundedWord Hom bound) :
    word ∈ reverseWords context bounded ↔ word.1.reverse ∈ context.paths := by
  constructor
  · intro membership
    rcases Finset.mem_image.mp membership with ⟨path, _, equality⟩
    have valueEquality := congrArg Subtype.val equality
    have restored : word.1.reverse = path.1 := by
      rw [← valueEquality]
      simp [BoundedWord.reverseOf]
    rw [restored]
    exact path.2
  · intro membership
    let path : {candidate // candidate ∈ context.paths} :=
      ⟨word.1.reverse, membership⟩
    apply Finset.mem_image.mpr
    refine ⟨path, by simp, ?_⟩
    apply Subtype.ext
    simp [path, BoundedWord.reverseOf]

/-- Mirrored variable-coefficient suffixes on a selected side. -/
def variableCoefficientWords
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (side : Bool) (row : Row) (index : Variable) :
    Finset (PendingWord problem) :=
  reverseWords (problem.coefficient side row index) fun _path membership =>
    problem.coefficient_path_length_le_pathBound side row index membership

theorem mem_variableCoefficientWords_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (side : Bool) (row : Row) (index : Variable)
    (word : PendingWord problem) :
    word ∈ variableCoefficientWords problem side row index ↔
      word.1.reverse ∈ (problem.coefficient side row index).paths := by
  exact mem_reverseWords_iff (problem.coefficient side row index)
    (fun path membership =>
      problem.coefficient_path_length_le_pathBound side row index membership) word

/-- Mirrored inhomogeneous coefficient suffixes on a selected side. -/
def constantCoefficientWords
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (side : Bool) (row : Row) :
    Finset (PendingWord problem) :=
  reverseWords (problem.constant side row) fun _path membership =>
    problem.constant_path_length_le_pathBound side row membership

theorem mem_constantCoefficientWords_iff
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (side : Bool) (row : Row)
    (word : PendingWord problem) :
    word ∈ constantCoefficientWords problem side row ↔
      word.1.reverse ∈ (problem.constant side row).paths := by
  exact mem_reverseWords_iff (problem.constant side row)
    (fun path membership =>
      problem.constant_path_length_le_pathBound side row membership) word

/-- Initial pending suffixes are exactly the inhomogeneous coefficients. -/
def initialPendingState
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) : PendingState problem :=
  fun row side => constantCoefficientWords problem side row

/-- Coefficients started by variables whose unknown language contains the
current tree word. -/
def coefficientSeeds
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (label : VariableLabel Variable)
    (row : Row) (side : Bool) : Finset (PendingWord problem) :=
  label.biUnion fun index => variableCoefficientWords problem side row index

/-- Pending suffixes after starting the coefficients selected by a label. -/
def activePendingWords
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) (state : PendingState problem)
    (label : VariableLabel Variable) (row : Row) (side : Bool) :
    Finset (PendingWord problem) :=
  state row side ∪ coefficientSeeds problem label row side

/-- Whether some active suffix ends at the current node. -/
def hasEndpoint
    {Hom : Type u} [FinEnum Hom] [Encodable Hom] {bound : Nat}
    (words : Finset (BoundedWord Hom bound)) : Bool :=
  decide (∃ word ∈ words, word.1 = [])

@[simp]
theorem hasEndpoint_eq_true_iff
    {Hom : Type u} [FinEnum Hom] [Encodable Hom] {bound : Nat}
    (words : Finset (BoundedWord Hom bound)) :
    hasEndpoint words = true ↔ ∃ word ∈ words, word.1 = [] := by
  simp [hasEndpoint]

/-- Consume one branch symbol from every active suffix. -/
def consumePendingWords
    {Hom : Type u} [FinEnum Hom] [Encodable Hom] {bound : Nat}
    (branch : Hom) (words : Finset (BoundedWord Hom bound)) :
    Finset (BoundedWord Hom bound) :=
  words.biUnion fun word =>
    match word.consume branch with
    | none => ∅
    | some suffix => {suffix}

@[simp]
theorem mem_consumePendingWords_iff
    {Hom : Type u} [FinEnum Hom] [Encodable Hom] {bound : Nat}
    (branch : Hom) (words : Finset (BoundedWord Hom bound))
    (suffix : BoundedWord Hom bound) :
    suffix ∈ consumePendingWords branch words ↔
      ∃ word ∈ words, word.1 = branch :: suffix.1 := by
  simp only [consumePendingWords, Finset.mem_biUnion]
  constructor
  · rintro ⟨word, membership, selected⟩
    cases consumed : word.consume branch with
    | none => simp [consumed] at selected
    | some next =>
        simp only [consumed, Finset.mem_singleton] at selected
        subst next
        exact ⟨word, membership,
          (BoundedWord.consume_eq_some_iff branch word suffix).mp consumed⟩
  · rintro ⟨word, membership, equality⟩
    refine ⟨word, membership, ?_⟩
    have consumed : word.consume branch = some suffix :=
      (BoundedWord.consume_eq_some_iff branch word suffix).mpr equality
    simp [consumed]

/-- The pending-suffix automaton for a complete finite-language system. -/
def finiteLanguageAutomaton
    {Row Variable Hom : Type u}
    [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Automaton (PendingState problem) Hom (VariableLabel Variable) where
  locallyValid state label := decide (∀ row,
    hasEndpoint (activePendingWords problem state label row false) = true →
      hasEndpoint (activePendingWords problem state label row true) = true)
  terminal state label := decide (∀ row side word,
    word ∈ activePendingWords problem state label row side →
      word.1 = [])
  next state label branch := fun row side =>
    consumePendingWords branch
      (activePendingWords problem state label row side)


end ACUIHE.Solver.Search
