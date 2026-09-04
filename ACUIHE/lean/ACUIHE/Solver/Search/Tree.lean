import Mathlib.Data.FinEnum
import Mathlib.Data.FinEnum.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Encodable.Basic

/-!
Finite, uniformly branching trees used to represent finite languages.

`Tree Branch Label` is deliberately an ordinary inductive tree.  The
executable search uses `BoundedTree`, whose index is an internally computed
automaton-state bound; callers of the final solver never supply this index.
-/

namespace ACUIHE.Solver.Search

universe u

/-- A finite tree.  An internal node has one child for every alphabet symbol;
leaves omit a suffix on which every represented language is empty. -/
inductive Tree (Branch : Type u) (Label : Type u) where
  | leaf (label : Label)
  | node (label : Label) (children : Branch → Tree Branch Label)

namespace Tree

/-- The label at the root of a tree. -/
def root {Branch : Type u} {Label : Type u} : Tree Branch Label → Label
  | .leaf label => label
  | .node label _ => label

/-- The set of words whose endpoint label satisfies `accept`. -/
def language
    {Branch : Type u} {Label : Type u} [Fintype Branch] [DecidableEq Branch]
    (accept : Label → Bool) : Tree Branch Label → Finset (List Branch)
  | .leaf label => if accept label then {[]} else ∅
  | .node label children =>
      (if accept label then {[]} else ∅) ∪
        Finset.univ.biUnion fun branch =>
          (language accept (children branch)).image (List.cons branch)

@[simp]
theorem nil_mem_language_iff
    {Branch : Type u} {Label : Type u} [Fintype Branch] [DecidableEq Branch]
    (accept : Label → Bool) (tree : Tree Branch Label) :
    [] ∈ tree.language accept ↔ accept tree.root = true := by
  cases tree with
  | leaf label => by_cases checked : accept label = true <;> simp [language, root, checked]
  | node label children =>
      by_cases checked : accept label = true <;> simp [language, root, checked]

@[simp]
theorem cons_mem_language_node_iff
    {Branch : Type u} {Label : Type u} [Fintype Branch] [DecidableEq Branch]
    (accept : Label → Bool) (label : Label)
    (children : Branch → Tree Branch Label) (branch : Branch)
    (word : List Branch) :
    branch :: word ∈ (Tree.node label children).language accept ↔
      word ∈ (children branch).language accept := by
  by_cases checked : accept label = true <;> simp [language, checked]

@[simp]
theorem cons_not_mem_language_leaf
    {Branch : Type u} {Label : Type u} [Fintype Branch] [DecidableEq Branch]
    (accept : Label → Bool) (label : Label) (branch : Branch)
    (word : List Branch) :
    branch :: word ∉ (Tree.leaf label).language accept := by
  by_cases checked : accept label = true <;> simp [language, checked]

/-- The complete tree of a prescribed depth, labelled as a function of the
path from the original root. -/
def completeAt
    {Branch : Type u} {Label : Type u}
    (labelAt : List Branch → Label) : Nat → List Branch → Tree Branch Label
  | 0, pathPrefix => .leaf (labelAt pathPrefix)
  | depth + 1, pathPrefix =>
      .node (labelAt pathPrefix) fun branch =>
        completeAt labelAt depth (pathPrefix ++ [branch])

/-- A complete tree contains exactly the words under its depth bound, with
the label prescribed at the corresponding absolute path. -/
@[simp]
theorem mem_language_completeAt_iff
    {Branch : Type u} {Label : Type u} [Fintype Branch] [DecidableEq Branch]
    (labelAt : List Branch → Label) (accept : Label → Bool)
    (depth : Nat) (pathPrefix word : List Branch) :
    word ∈ (completeAt labelAt depth pathPrefix).language accept ↔
      word.length ≤ depth ∧ accept (labelAt (pathPrefix ++ word)) = true := by
  induction depth generalizing pathPrefix word with
  | zero =>
      cases word <;>
        (by_cases checked : accept (labelAt pathPrefix) = true) <;>
        simp [completeAt, language, checked]
  | succ depth inductionHypothesis =>
      cases word with
      | nil =>
          by_cases checked : accept (labelAt pathPrefix) = true <;>
            simp [completeAt, language, checked]
      | cons branch word =>
          by_cases checked : accept (labelAt pathPrefix) = true <;>
            simp [completeAt, language, checked, inductionHypothesis,
              List.append_assoc]

end Tree

/-- Trees of height at most the index.  At height zero only a leaf is
available; at a successor height one may either stop or provide every child. -/
def BoundedTree (Branch : Type u) (Label : Type u) : Nat → Type u
  | 0 => Label
  | bound + 1 => Label × Option (Branch → BoundedTree Branch Label bound)

namespace BoundedTree

/-- Forget the height index. -/
def toTree {Branch : Type u} {Label : Type u} :
    (bound : Nat) → BoundedTree Branch Label bound → Tree Branch Label
  | 0, label => .leaf label
  | _bound + 1, (label, none) => .leaf label
  | bound + 1, (label, some children) =>
      .node label fun branch => toTree bound (children branch)

/-- Regard a tree of height at most `bound` as one of height at most
`bound + 1`, without changing the underlying tree. -/
def liftBound {Branch : Type u} {Label : Type u} :
    (bound : Nat) → BoundedTree Branch Label bound →
      BoundedTree Branch Label (bound + 1)
  | 0, label => (label, none)
  | _bound + 1, (label, none) => (label, none)
  | bound + 1, (label, some children) =>
      (label, some fun branch => liftBound bound (children branch))

@[simp]
theorem toTree_liftBound {Branch : Type u} {Label : Type u}
    (bound : Nat) (tree : BoundedTree Branch Label bound) :
    toTree (bound + 1) (liftBound bound tree) = toTree bound tree := by
  induction bound with
  | zero => rfl
  | succ bound inductionHypothesis =>
      rcases tree with ⟨label, children⟩
      cases children with
      | none => rfl
      | some children =>
          simp only [liftBound, toTree]
          congr
          funext branch
          exact inductionHypothesis (children branch)

instance instFinEnum
    {Branch : Type u} {Label : Type u} [FinEnum Branch] [FinEnum Label] :
    (bound : Nat) → FinEnum (BoundedTree Branch Label bound)
  | 0 => inferInstanceAs (FinEnum Label)
  | bound + 1 => by
      let childFinEnum : FinEnum (BoundedTree Branch Label bound) :=
        instFinEnum (Branch := Branch) (Label := Label) bound
      letI : FinEnum (BoundedTree Branch Label bound) := childFinEnum
      letI : ∀ _ : Branch, FinEnum (BoundedTree Branch Label bound) :=
        fun _ => childFinEnum
      exact inferInstanceAs
        (FinEnum (Label × Option (Branch → BoundedTree Branch Label bound)))

end BoundedTree

end ACUIHE.Solver.Search
