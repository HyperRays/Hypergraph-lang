import ACUIhE.ACUIESolver.Layers.Horn
import Mathlib.Data.Fintype.Prod

/-!
# Exact compilation and decision of flat set constraints

A layer is a union of fixed atom names and unknown rows. All coordinates are
compiled to one finite Horn system on absent memberships. No rows are guessed.
-/

namespace ACUIhE.ACUIESolver.Layers

structure Expr (n : Nat) where
  fixed : Finset (Fin n)
  vars : Finset (Fin n)
  deriving DecidableEq

abbrev Rows (n : Nat) := Fin n → Finset (Fin n)

namespace Expr

variable {n : Nat}

def eval (r : Rows n) (e : Expr n) : Finset (Fin n) := e.fixed ∪ e.vars.biUnion r
def atoms (s : Finset (Fin n)) : Expr n := ⟨s, ∅⟩
def union (a b : Expr n) : Expr n := ⟨a.fixed ∪ b.fixed, a.vars ∪ b.vars⟩

@[simp] theorem eval_atoms (r : Rows n) (s : Finset (Fin n)) : eval r (atoms s) = s := by
  simp [eval, atoms]

@[simp] theorem eval_union (r : Rows n) (a b : Expr n) :
    eval r (union a b) = eval r a ∪ eval r b := by
  ext i
  simp [eval, union]
  aesop

end Expr

abbrev Constraint (n : Nat) := Expr n × Expr n
abbrev System (n : Nat) := List (Constraint n)

def Holds {n : Nat} (cs : System n) (r : Rows n) : Prop :=
  ∀ c ∈ cs, c.1.eval r ⊆ c.2.eval r

def equation {n : Nat} (l r : Expr n) : System n := [(l, r), (r, l)]

@[simp] theorem holds_nil {n : Nat} (r : Rows n) : Holds [] r := by simp [Holds]

@[simp] theorem holds_append {n : Nat} (a b : System n) (r : Rows n) :
    Holds (a ++ b) r ↔ Holds a r ∧ Holds b r := by simp [Holds, or_imp, forall_and]

@[simp] theorem holds_equation {n : Nat} (l r : Expr n) (s : Rows n) :
    Holds (equation l r) s ↔ l.eval s = r.eval s := by
  simp only [Holds, equation, List.mem_cons, List.not_mem_nil, or_false, Prod.forall,
    Prod.mk.injEq]
  constructor
  · intro h
    exact Finset.Subset.antisymm (h l r (Or.inl ⟨rfl, rfl⟩)) (h r l (Or.inr ⟨rfl, rfl⟩))
  · intro h a b hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [h]

@[simp] theorem holds_flatMap {n : Nat} {α : Type*} (xs : List α)
    (f : α → System n) (r : Rows n) :
    Holds (xs.flatMap f) r ↔ ∀ x ∈ xs, Holds (f x) r := by
  simp [Holds]
  aesop

abbrev Bit (n : Nat) := Fin n × Fin n

def rows {n : Nat} (absent : Finset (Bit n)) : Rows n :=
  fun v => Finset.univ.filter (fun a => (v, a) ∉ absent)

def absent {n : Nat} (r : Rows n) : Finset (Bit n) :=
  Finset.univ.filter (fun p => p.2 ∉ r p.1)

@[simp] theorem rows_absent {n : Nat} (r : Rows n) : rows (absent r) = r := by
  funext v
  ext a
  simp [rows, absent]

def coordinate {n : Nat} (e : Expr n) (a : Fin n) : Horn.Coordinate (Bit n) :=
  ⟨decide (a ∈ e.fixed), e.vars.image (fun v => (v, a))⟩

theorem coordinate_exact {n : Nat} (e : Expr n) (a : Fin n) (s : Finset (Bit n)) :
    (coordinate e a).Present s ↔ a ∈ e.eval (rows s) := by
  simp [coordinate, Horn.Coordinate.Present, Expr.eval, rows]

def compile {n : Nat} (cs : System n) : Finset (Horn.Rule (Bit n)) :=
  cs.toFinset.biUnion (fun c => Finset.univ.biUnion (fun a =>
    Horn.compileInclusion (coordinate c.1 a) (coordinate c.2 a)))

theorem model_biUnion {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (xs : Finset β) (f : β → Finset (Horn.Rule α)) (s : Finset α) :
    Horn.Model (xs.biUnion f) s ↔ ∀ x ∈ xs, Horn.Model (f x) s := by
  simp [Horn.Model]
  aesop

theorem compile_exact {n : Nat} (cs : System n) (s : Finset (Bit n)) :
    Horn.Model (compile cs) s ↔ Holds cs (rows s) := by
  simp only [compile, model_biUnion, List.mem_toFinset, Finset.mem_univ, forall_true_left,
    Horn.compileInclusion_exact, coordinate_exact, Holds, Finset.subset_iff]

def solve {n : Nat} (cs : System n) : Option (Rows n) := (Horn.solve (compile cs)).map rows

/-- The compiled n-by-n membership system stabilizes within n squared rounds. -/
theorem propagation_stable {n : Nat} (cs : System n) :
    Horn.step (compile cs) (Horn.iter (compile cs) (n * n)) =
      Horn.iter (compile cs) (n * n) := by
  simpa [Horn.closure, Bit] using Horn.closure_fixed (compile cs)

theorem solve_sound {n : Nat} (cs : System n) {r : Rows n} (h : solve cs = some r) :
    Holds cs r := by
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (compile_exact cs s).mp (Horn.solve_sound hs)

theorem solve_complete {n : Nat} (cs : System n) {r : Rows n} (h : Holds cs r) :
    ∃ s, solve cs = some s := by
  have hm : Horn.Model (compile cs) (absent r) := by
    rw [compile_exact, rows_absent]
    exact h
  obtain ⟨s, hs⟩ := Horn.solve_complete.mp ⟨absent r, hm⟩
  exact ⟨rows s, by simp [solve, hs]⟩

theorem solve_none_iff {n : Nat} (cs : System n) :
    solve cs = none ↔ ¬ ∃ r, Holds cs r := by
  constructor
  · rintro hn ⟨r, hr⟩
    obtain ⟨s, hs⟩ := solve_complete cs hr
    simp [hn] at hs
  · intro h
    cases hs : solve cs with
    | none => rfl
    | some r => exact (h ⟨r, solve_sound cs hs⟩).elim

end ACUIhE.ACUIESolver.Layers
