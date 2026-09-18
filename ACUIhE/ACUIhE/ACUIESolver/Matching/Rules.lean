import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Basic

/-!
# E-matching conditions, independent of the layer algebra

An E root is a sum of unprefixed names. A restriction on its child's
coordinates is a different operation: it does not bound the words carried by
those coordinates. Both the finite-set and word-valued interpretations use
these same conditions.
-/

namespace ACUIhE.ACUIESolver.Matching.Rules

universe u v

inductive Expr (Layer : Type u) (n : Nat) where
  | layer : Layer → Expr Layer n
  | atoms : Finset (Fin n) → Expr Layer n

inductive Condition (Layer : Type u) (n : Nat) where
  | equal : Expr Layer n → Expr Layer n → Condition Layer n
  | below : Expr Layer n → Expr Layer n → Condition Layer n
  | supported : Layer → Finset (Fin n) → Condition Layer n

abbrev System (Layer : Type u) (n : Nat) := List (Condition Layer n)

variable {Layer : Type u} {Value : Type v} {n : Nat}

/-- The names of one positive group, restricted to actual E occurrences. -/
def group (eligible : Finset (Fin n)) (labels : Fin n → Fin (n + 1)) (i : Fin n) :
    Finset (Fin n) := eligible.filter (fun j => labels j = labels i ∧ labels i ≠ 0)

@[simp] theorem mem_group (eligible : Finset (Fin n)) (labels : Fin n → Fin (n + 1))
    (i j : Fin n) : j ∈ group eligible labels i ↔
      j ∈ eligible ∧ labels j = labels i ∧ labels i ≠ 0 := by simp [group]

/-- Interpretation of layer expressions, named atoms, and coordinate support. -/
structure Interpretation (Layer : Type u) (Value : Type v) (n : Nat) where
  layer : Layer → Value
  atoms : Finset (Fin n) → Value
  below : Value → Value → Prop
  support : Value → Finset (Fin n)

def Expr.eval (m : Interpretation Layer Value n) : Expr Layer n → Value
  | .layer e => m.layer e
  | .atoms names => m.atoms names

def Condition.Holds (m : Interpretation Layer Value n) : Condition Layer n → Prop
  | .equal a b => a.eval m = b.eval m
  | .below a b => m.below (a.eval m) (b.eval m)
  | .supported e allowed => m.support (m.layer e) ⊆ allowed

def Holds (m : Interpretation Layer Value n) (cs : System Layer n) : Prop :=
  ∀ c ∈ cs, c.Holds m

@[simp] theorem holds_nil (m : Interpretation Layer Value n) : Holds m [] := by
  simp [Holds]

@[simp] theorem holds_cons (m : Interpretation Layer Value n)
    (c : Condition Layer n) (cs : System Layer n) :
    Holds m (c :: cs) ↔ c.Holds m ∧ Holds m cs := by
  simp [Holds]

@[simp] theorem holds_append (m : Interpretation Layer Value n) (a b : System Layer n) :
    Holds m (a ++ b) ↔ Holds m a ∧ Holds m b := by
  simp [Holds, or_imp, forall_and]

@[simp] theorem holds_map {ι : Type*} (m : Interpretation Layer Value n)
    (xs : List ι) (f : ι → Condition Layer n) :
    Holds m (xs.map f) ↔ ∀ i ∈ xs, (f i).Holds m := by
  simp [Holds]

@[simp] theorem holds_flatMap {ι : Type*} (m : Interpretation Layer Value n)
    (xs : List ι) (f : ι → System Layer n) :
    Holds m (xs.flatMap f) ↔ ∀ i ∈ xs, Holds m (f i) := by
  simp only [Holds, List.forall_mem_flatMap]

/-- The complete conditions of one E edge. The caller supplies its group
and the strictly lower coordinates; no layer solver chooses E rules. -/
def complete (self child : Layer) (children : Fin n → Layer)
    (group lower : Finset (Fin n)) : System Layer n :=
  [.equal (.layer self) (.atoms group)] ++
  (if group = ∅ then [.equal (.layer child) (.atoms ∅)] else []) ++
  ((List.finRange n).filter (fun j => j ∈ group)).map
    (fun j => .equal (.layer (children j)) (.layer child)) ++
  [.supported child lower]

theorem complete_iff (m : Interpretation Layer Value n)
    (self child : Layer) (children : Fin n → Layer) (group lower : Finset (Fin n)) :
    Holds m (complete self child children group lower) ↔
      m.layer self = m.atoms group ∧
      (group = ∅ → m.layer child = m.atoms ∅) ∧
      (∀ j ∈ group, m.layer (children j) = m.layer child) ∧
      m.support (m.layer child) ⊆ lower := by
  by_cases empty : group = ∅ <;>
    simp [complete, empty, Condition.Holds, Expr.eval]

/-- Necessary conditions for an edge whose positive group is still pending.
Its root contains its own name, uses only pending names, and its child cannot
depend on that same name. These are exactly the original ACUIE pruning rules. -/
def pending (self child : Layer) (remaining : Finset (Fin n)) (i : Fin n) :
    System Layer n :=
  [.below (.atoms {i}) (.layer self),
   .below (.layer self) (.atoms remaining),
   .supported child (Finset.univ.erase i)]

theorem pending_iff (m : Interpretation Layer Value n)
    (self child : Layer) (remaining : Finset (Fin n)) (i : Fin n) :
    Holds m (pending self child remaining i) ↔
      m.below (m.atoms {i}) (m.layer self) ∧
      m.below (m.layer self) (m.atoms remaining) ∧
      i ∉ m.support (m.layer child) := by
  simp only [pending, holds_cons, holds_nil, and_true, Condition.Holds, Expr.eval]
  simp [Finset.subset_iff]

/-- Every completed edge satisfies the pending conditions on the path to it.
Only monotonicity of named sums is needed; no assumption about word lengths,
nonzero reconstructed names, or distinct reconstructed groups is made. -/
theorem pending_of_complete (m : Interpretation Layer Value n)
    (atoms_mono : ∀ a b, a ⊆ b → m.below (m.atoms a) (m.atoms b))
    (self child : Layer) (children : Fin n → Layer)
    (group lower remaining : Finset (Fin n)) (i : Fin n)
    (full : Holds m (complete self child children group lower))
    (own : i ∈ group) (within : group ⊆ remaining) (strict : i ∉ lower) :
    Holds m (pending self child remaining i) := by
  obtain ⟨root, _, _, support⟩ := (complete_iff m self child children group lower).mp full
  apply (pending_iff m self child remaining i).mpr
  rw [root]
  exact ⟨atoms_mono _ _ (Finset.singleton_subset_iff.mpr own),
    atoms_mono _ _ within, fun member => strict (support member)⟩

end ACUIhE.ACUIESolver.Matching.Rules
