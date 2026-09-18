import ACUIhE.ACUIESolver.Finite.Syntax

/-!
# Finite constraints over named input subterms

A row is a set of named constructor atoms, not a candidate term substitution.
E rows refer only to E names whose argument rows agree. Ranked dependencies
make reconstruction finite. Names may decode to zero or coincide: soundness
does not assume that the symbolic names remain distinct after reconstruction.
-/

namespace ACUIhE.ACUIESolver.Finite

structure Table (n : Nat) where
  rows : Fin n → Finset (Fin n)
  rank : Fin n → Fin (n + 1)

namespace Table

universe u v
variable {Const : Type u} {Var : Type v} [DecidableEq Const] [DecidableEq Var]

/-- Equal raw subterms use the union of all their occurrence rows. -/
def lookup (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (t : ACUIE.Term Const Var) : Finset (Fin ts.length) :=
  (Finset.univ.filter (fun i => ts.get i = t)).biUnion d.rows

def Compatible (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (a : ACUIE.Term Const Var) (j : Fin ts.length) : Prop :=
  match ts.get j with
  | .free b => lookup ts d b = lookup ts d a
  | _ => False

instance decidableCompatible (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (a : ACUIE.Term Const Var) (j : Fin ts.length) : Decidable (Compatible ts d a j) := by
  unfold Compatible
  split <;> infer_instance

def Row (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) (t : ACUIE.Term Const Var) : Prop :=
  match t with
  | .zero => lookup ts d t = ∅
  | .var _ => True
  | .const c => lookup ts d t = Finset.univ.filter (fun j => ts.get j = .const c)
  | .add a b => lookup ts d t = lookup ts d a ∪ lookup ts d b
  | .free a =>
    (lookup ts d t = ∅ → lookup ts d a = ∅) ∧
    ∀ j ∈ lookup ts d t, Compatible ts d a j

def RankRow (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) (i : Fin ts.length) : Prop :=
  match ts.get i with
    | .free a => ∀ j ∈ lookup ts d a, d.rank j < d.rank i
    | _ => True

instance decidableRankRow (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (i : Fin ts.length) : Decidable (RankRow ts d i) := by
  unfold RankRow
  split <;> infer_instance

def Ranked (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) : Prop := ∀ i, RankRow ts d i

def Valid (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var) (d : Table ts.length) : Prop :=
  (∀ i, Row ts d (ts.get i)) ∧ Ranked ts d ∧
    ∀ q ∈ p, lookup ts d q.left = lookup ts d q.right

instance decidableRow (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (t : ACUIE.Term Const Var) : Decidable (Row ts d t) := by
  cases t <;> unfold Row <;> infer_instance

instance decidableRanked (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    Decidable (Ranked ts d) := by
  unfold Ranked
  infer_instance

instance decidableValid (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (d : Table ts.length) : Decidable (Valid ts p d) := by
  unfold Valid
  infer_instance

theorem row_of_mem {ts : List (ACUIE.Term Const Var)} {p : Problem Const Var}
    {d : Table ts.length} (h : Valid ts p d) {t : ACUIE.Term Const Var} (member : t ∈ ts) :
    Row ts d t := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
  exact h.1 i

theorem rank_child {ts : List (ACUIE.Term Const Var)} {d : Table ts.length}
    (h : Ranked ts d) {i j : Fin ts.length} {a : ACUIE.Term Const Var}
    (hi : ts.get i = .free a) (hj : j ∈ lookup ts d a) : d.rank j < d.rank i := by
  have := h i
  unfold RankRow at this
  rw [hi] at this
  exact this j hj

end Table
end ACUIhE.ACUIESolver.Finite
