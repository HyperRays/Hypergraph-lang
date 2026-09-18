import ACUIhE.ACUIESolver.Matching.Constraints
import ACUIhE.ACUIESolver.Matching.Order
import ACUIhE.ACUIESolver.Finite.Completeness

/-!
# Every ACUIE unifier supplies a successful ordered matching branch

The proof starts with an arbitrary unifier, including nonground unifiers of
arbitrary depth. Projection retains named input atoms. Ordered labels identify
equal nonzero E children and respect strict graph-height descent. This proves
completeness of the new search, without calling the previous exhaustive search.
-/

namespace ACUIhE.ACUIESolver.Matching

open ACUIhE.ACUIESolver.Finite
open Branching (graph)

universe u v w
variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Target]

def values (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target)
    (i : Fin ts.length) : Graph Const Target Empty :=
  match ts.get i with
  | .free a => graph σ a
  | _ => 0

def extractedLabels (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target) :
    Labels ts.length := Order.label height (values ts σ)

omit [DecidableEq Var] in
theorem extractedLabels_bound (ts : List (ACUIE.Term Const Var))
    (σ : ACUIE.Substitution Const Var Target) (i : Fin ts.length) :
    (extractedLabels ts σ i).val ≤ edgeCount ts := by
  apply le_trans (Order.label_bound height (values ts σ) i)
  apply Finset.card_le_card
  intro j hj
  change j ∈ Order.active (values ts σ) at hj
  simp only [Order.active, edges, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  cases he : ts.get j <;> simp only [values, he, isEdge, ne_eq, not_true_eq_false,
    eq_self] at hj ⊢

omit [DecidableEq Var] in
theorem extractedLabels_nonedge (ts : List (ACUIE.Term Const Var))
    (σ : ACUIE.Substitution Const Var Target) (i : Fin ts.length)
    (h : isEdge (ts.get i) = false) : extractedLabels ts σ i = 0 := by
  apply (Order.label_zero_iff height (values ts σ) i).mpr
  cases he : ts.get i <;> simp [he, isEdge, -List.get_eq_getElem] at h <;>
    simp [values, he, -List.get_eq_getElem]

omit [DecidableEq Var] in
theorem names_projection (ts : List (ACUIE.Term Const Var))
    (σ : ACUIE.Substitution Const Var Target) (i : Fin ts.length)
    {a : ACUIE.Term Const Var} (hi : ts.get i = .free a) :
    names ts (extractedLabels ts σ) i = project ts σ (Graph.free (graph σ a)) := by
  ext j
  rw [mem_names, mem_project_free]
  simp only [extractedLabels, Order.label_eq_iff, ne_eq, Order.label_zero_iff]
  cases hj : ts.get j <;> simp [values, hi, hj, isEdge, -List.get_eq_getElem]
  aesop

def projectedRows (ts : List (ACUIE.Term Const Var)) (σ : ACUIE.Substitution Const Var Target) :
    Layers.Rows ts.length := (extracted ts σ).rows

theorem lookup_projected (ts : List (ACUIE.Term Const Var))
    (σ : ACUIE.Substitution Const Var Target) (labels : Labels ts.length)
    {t : ACUIE.Term Const Var} (ht : t ∈ ts) :
    Table.lookup ts (table labels (projectedRows ts σ)) t = project ts σ (graph σ t) :=
  lookup_extracted ts σ ht

theorem projected_exactNames (ts : List (ACUIE.Term Const Var))
    (σ : ACUIE.Substitution Const Var Target) :
    ExactNames ts (extractedLabels ts σ) (projectedRows ts σ) := by
  intro i hi
  rw [lookup_projected ts σ _ (List.mem_iff_get.mpr ⟨i, rfl⟩)]
  cases he : ts.get i <;> simp only [he, isEdge, Bool.false_eq_true] at hi
  rename_i a
  rw [Branching.graph_free]
  exact (names_projection ts σ i he).symm

theorem projected_ranked (ts : List (ACUIE.Term Const Var)) (closed : Closed ts)
    (σ : ACUIE.Substitution Const Var Target) :
    Table.Ranked ts (table (extractedLabels ts σ) (projectedRows ts σ)) := by
  intro i
  unfold Table.RankRow
  cases hi : ts.get i with
  | zero | const | var | add => trivial
  | free a =>
    intro j hj
    rw [lookup_projected ts σ _ (closed.free_body (List.mem_iff_get.mpr ⟨i, hi⟩))] at hj
    have hn : graph σ a ≠ 0 := by
      intro hz
      simp [hz] at hj
    have hv : values ts σ i ≠ 0 := by simpa only [values, hi] using hn
    change Order.label height (values ts σ) j < Order.label height (values ts σ) i
    by_cases hz : values ts σ j = 0
    · rw [(Order.label_zero_iff height (values ts σ) j).mpr hz]
      apply Fin.pos_iff_ne_zero.mpr
      exact fun h => hv ((Order.label_zero_iff height (values ts σ) i).mp h)
    · apply Order.label_strict height (values ts σ) hv
      have lower := score_lt_of_member ts σ hi hj
      cases he : ts.get j <;> simp only [values, he, not_true_eq_false] at hz
      rename_i b
      simpa only [values, hi, he, score, Nat.add_lt_add_iff_right] using lower

theorem projected_valid (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target)
    (hσ : p.IsUnifier σ) :
    Table.Valid (pool p) p (table (extractedLabels (pool p) σ) (projectedRows (pool p) σ)) := by
  have old := extracted_valid p σ hσ
  exact ⟨old.1, projected_ranked (pool p) (pool_closed p) σ, old.2.2⟩

/-- Completeness provides a successful matching branch, not a bound on a unifier. -/
theorem successful_branch (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target)
    (hσ : p.IsUnifier σ) :
    ∃ d, solveBranch (pool p) p (extractedLabels (pool p) σ) = some d :=
  solveBranch_complete (pool p) p _ _ (projected_valid p σ hσ) (projected_exactNames (pool p) σ)

end ACUIhE.ACUIESolver.Matching
