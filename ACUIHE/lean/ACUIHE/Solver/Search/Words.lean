import ACUIHE.Solver.Linear.Columns
import Mathlib.Data.FinEnum

/-! Finite words and coefficient-derived path bounds for the ACUIh automaton. -/

namespace ACUIHE.Solver.Search

open ACUIHE.Solver.Linear

universe u v w x

local instance wordEncodableDecidableEq {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

/-- Every word over a finite alphabet whose length is at most `bound`. -/
def wordsUpTo {Alpha : Type u} [FinEnum Alpha] : Nat → List (List Alpha)
  | 0 => [[]]
  | bound + 1 =>
      [] :: (FinEnum.toList Alpha).flatMap fun letter =>
        (wordsUpTo bound).map (List.cons letter)

@[simp]
theorem mem_wordsUpTo_iff {Alpha : Type u} [FinEnum Alpha]
    (bound : Nat) (word : List Alpha) :
    word ∈ wordsUpTo bound ↔ word.length ≤ bound := by
  induction bound generalizing word with
  | zero => simp [wordsUpTo]
  | succ bound inductionHypothesis =>
      cases word with
      | nil => simp [wordsUpTo]
      | cons letter word => simp [wordsUpTo, inductionHypothesis]

/-- Words in the finite automaton state space. -/
abbrev BoundedWord (Alpha : Type u) [FinEnum Alpha] (bound : Nat) :=
  {word : List Alpha // word ∈ wordsUpTo bound}

/-- Explicit finite enumeration of bounded words. -/
instance boundedWordFinEnum {Alpha : Type u} [FinEnum Alpha] (bound : Nat) :
    FinEnum (BoundedWord Alpha bound) :=
  FinEnum.ofList (wordsUpTo bound).attach (by simp)

/-- The empty word belongs to every bounded-word space. -/
def BoundedWord.nil {Alpha : Type u} [FinEnum Alpha] (bound : Nat) :
    BoundedWord Alpha bound :=
  ⟨[], by simp⟩

/-- Reverse a path known to lie under a length bound. -/
def BoundedWord.reverseOf
    {Alpha : Type u} [FinEnum Alpha] {bound : Nat}
    (word : List Alpha) (lengthBound : word.length ≤ bound) :
    BoundedWord Alpha bound :=
  ⟨word.reverse, by simpa using lengthBound⟩

/-- Consume the first symbol of a pending suffix. -/
def BoundedWord.consume
    {Alpha : Type u} [FinEnum Alpha] {bound : Nat}
    (letter : Alpha) (word : BoundedWord Alpha bound) :
    Option (BoundedWord Alpha bound) :=
  match equality : word.1 with
  | [] => none
  | head :: tail =>
      if head = letter then
        some ⟨tail, (mem_wordsUpTo_iff bound tail).mpr (by
          have bounded := (mem_wordsUpTo_iff bound word.1).mp word.2
          rw [equality] at bounded
          exact le_trans (Nat.le_succ tail.length) bounded)⟩
      else none

@[simp]
theorem BoundedWord.consume_eq_some_iff
    {Alpha : Type u} [FinEnum Alpha] {bound : Nat}
    (letter : Alpha) (word next : BoundedWord Alpha bound) :
    word.consume letter = some next ↔ word.1 = letter :: next.1 := by
  rcases word with ⟨word, bounded⟩
  rcases next with ⟨next, nextBounded⟩
  cases word with
  | nil => simp [BoundedWord.consume]
  | cons head tail =>
      constructor
      · intro consumed
        by_cases headEquality : head = letter
        · subst head
          have tailEquality : tail = next := by
            simpa [BoundedWord.consume] using consumed
          exact congrArg (List.cons letter) tailEquality
        · simp [BoundedWord.consume, headEquality] at consumed
      · intro wordEquality
        have headEquality : head = letter := List.cons.inj wordEquality |>.1
        have tailEquality : tail = next := List.cons.inj wordEquality |>.2
        subst head
        subst next
        simp [BoundedWord.consume]

/-- Maximum length of a path in a homomorphism context. -/
def contextPathBound {Hom : Type w} [Encodable Hom]
    (context : HomContext Hom) : Nat :=
  context.paths.sup List.length

theorem path_length_le_contextPathBound
    {Hom : Type w} [Encodable Hom]
    (context : HomContext Hom) {path : List Hom}
    (membership : path ∈ context.paths) :
    path.length ≤ contextPathBound context := by
  exact Finset.le_sup (f := List.length) membership

/-- Maximum coefficient length in one side of a selected matrix column. -/
def representationPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) : Nat :=
  max
    (Finset.univ.sup fun row =>
      Finset.univ.sup fun index =>
        contextPathBound (representation.1 row index))
    (Finset.univ.sup fun row =>
      contextPathBound (representation.2 row basis))

/-- Maximum coefficient length on both sides of a selected column problem. -/
def columnPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) : Nat :=
  max (representationPathBound left basis) (representationPathBound right basis)

theorem variable_path_length_le_representationPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (row : Row) (index : Variable) {path : List Hom}
    (membership : path ∈ (representation.1 row index).paths) :
    path.length ≤ representationPathBound representation basis := by
  apply le_trans (path_length_le_contextPathBound _ membership)
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun index => contextPathBound (representation.1 row index))
    (Finset.mem_univ index))
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun row => Finset.univ.sup fun index =>
      contextPathBound (representation.1 row index))
    (Finset.mem_univ row))
  exact Nat.le_max_left _ _

theorem constant_path_length_le_representationPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (representation :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (row : Row) {path : List Hom}
    (membership : path ∈ (representation.2 row basis).paths) :
    path.length ≤ representationPathBound representation basis := by
  apply le_trans (path_length_le_contextPathBound _ membership)
  apply le_trans (Finset.le_sup (s := Finset.univ)
    (f := fun row => contextPathBound (representation.2 row basis))
    (Finset.mem_univ row))
  exact Nat.le_max_right _ _

theorem left_variable_path_length_le_columnPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (row : Row) (index : Variable) {path : List Hom}
    (membership : path ∈ (left.1 row index).paths) :
    path.length ≤ columnPathBound left right basis :=
  le_trans (variable_path_length_le_representationPathBound
    left basis row index membership) (Nat.le_max_left _ _)

theorem right_variable_path_length_le_columnPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (row : Row) (index : Variable) {path : List Hom}
    (membership : path ∈ (right.1 row index).paths) :
    path.length ≤ columnPathBound left right basis :=
  le_trans (variable_path_length_le_representationPathBound
    right basis row index membership) (Nat.le_max_right _ _)

theorem left_constant_path_length_le_columnPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (row : Row) {path : List Hom}
    (membership : path ∈ (left.2 row basis).paths) :
    path.length ≤ columnPathBound left right basis :=
  le_trans (constant_path_length_le_representationPathBound
    left basis row membership) (Nat.le_max_left _ _)

theorem right_constant_path_length_le_columnPathBound
    {Row : Type x} {Variable : Type v} {Basis : Type u} {Hom : Type w}
    [FinEnum Row] [FinEnum Variable] [Encodable Hom]
    (left right :
      Matrix Row Variable (HomContext Hom) ×
        Matrix Row Basis (HomContext Hom))
    (basis : Basis) (row : Row) {path : List Hom}
    (membership : path ∈ (right.2 row basis).paths) :
    path.length ≤ columnPathBound left right basis :=
  le_trans (constant_path_length_le_representationPathBound
    right basis row membership) (Nat.le_max_right _ _)

end ACUIHE.Solver.Search
