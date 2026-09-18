import ACUIhE.ACUIESolver.Finite.Table
import ACUIhE.ACUIESolver.Finite.Height
import ACUIhE.ACUIESolver.Branching.Layer

/-!
# Projecting an arbitrary unifier onto finitely many input names

Only constants and E applications explicitly occurring in the input are named.
Projection forgets other atoms, preserves union, and retains every nonzero
input E application as its own named atom. No bound on the original unifier
or its graph is assumed.
-/

namespace ACUIhE.ACUIESolver.Finite

open Branching (graph)

universe u v w
variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Target]

def namedAtom (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    (i : Fin ts.length) : Option (Graph.Summand Const Target Empty) :=
  match ts.get i with
  | .const c => some ([], .inl (.const c))
  | .free a => if h : graph σ a = 0 then none else some ([], .inr ⟨graph σ a, h⟩)
  | _ => none

def project (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    (g : Graph Const Target Empty) : Finset (Fin ts.length) :=
  Finset.univ.filter (fun i => (namedAtom ts σ i).any (fun atom => decide (atom ∈ g.layer)))

omit [DecidableEq Var] in
@[simp] theorem project_zero (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target) :
    project ts σ 0 = ∅ := by
  ext i
  cases namedAtom ts σ i <;> simp [project]

omit [DecidableEq Var] in
theorem project_add (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    (a b : Graph Const Target Empty) : project ts σ (a + b) = project ts σ a ∪ project ts σ b := by
  ext i
  cases h : namedAtom ts σ i <;> simp [project, h]

theorem project_const (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    (c : Const) : project ts σ (Graph.constant c) = Finset.univ.filter (fun i => ts.get i = .const c) := by
  ext i
  cases hi : ts.get i with
  | zero | const | var | add => simp [project, namedAtom, hi, -List.get_eq_getElem]
  | free a =>
    by_cases h : graph σ a = 0 <;> simp [project, namedAtom, hi, h, -List.get_eq_getElem]

omit [DecidableEq Var] in
theorem mem_project_free (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    (g : Graph Const Target Empty) (i : Fin ts.length) :
    i ∈ project ts σ (Graph.free g) ↔
      ∃ a, ts.get i = .free a ∧ graph σ a ≠ 0 ∧ graph σ a = g := by
  by_cases hg : g = 0
  · subst g
    change i ∈ project ts σ 0 ↔ _
    simp
  · cases hi : ts.get i with
    | zero | const | var | add =>
      simp [project, namedAtom, hi, Graph.layer_free_of_ne_zero g hg, -List.get_eq_getElem]
    | free a =>
      by_cases ha : graph σ a = 0 <;>
        simp [project, namedAtom, hi, ha, Graph.layer_free_of_ne_zero g hg, -List.get_eq_getElem]

def score (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    (i : Fin ts.length) : Nat :=
  match ts.get i with
  | .free a => height (graph σ a) + 1
  | _ => 0

omit [DecidableEq Var] in
theorem score_lt_of_member (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    {i j : Fin ts.length} {a : ACUIE.Term Const Var} (hi : ts.get i = .free a)
    (member : j ∈ project ts σ (graph σ a)) : score ts σ j < score ts σ i := by
  cases hj : ts.get j with
  | zero | var | add => simp [project, namedAtom, hj, -List.get_eq_getElem] at member
  | const c => simp [score, hi, hj, -List.get_eq_getElem]
  | free b =>
    by_cases hb : graph σ b = 0
    · simp [project, namedAtom, hj, hb, -List.get_eq_getElem] at member
    · have edge : ([], .inr ⟨graph σ b, hb⟩) ∈ (graph σ a).layer := by
        simpa [project, namedAtom, hj, hb, -List.get_eq_getElem] using member
      have lower := height_child (show Graph.Child (graph σ b) (graph σ a) from ⟨[], hb, edge⟩)
      simpa only [score, hj, hi, Nat.add_lt_add_iff_right] using lower

/-- Plain finite data extracted for the completeness proof, not supplied to the solver. -/
def extracted (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target) :
    Table ts.length where
  rows := fun i => project ts σ (graph σ (ts.get i))
  rank := compressedRank (score ts σ)

theorem lookup_extracted (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    {t : ACUIE.Term Const Var} (member : t ∈ ts) :
    Table.lookup ts (extracted ts σ) t = project ts σ (graph σ t) := by
  ext j
  simp only [Table.lookup, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    extracted]
  constructor
  · rintro ⟨i, eq, hj⟩
    simpa only [eq] using hj
  · intro hj
    obtain ⟨i, eq⟩ := List.mem_iff_get.mp member
    exact ⟨i, eq, by simpa only [eq] using hj⟩

end ACUIhE.ACUIESolver.Finite
