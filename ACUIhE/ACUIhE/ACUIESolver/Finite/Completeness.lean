import ACUIhE.ACUIESolver.Finite.Projection
import ACUIhE.ACUIESolver.Finite.Reconstruction

/-!
# Completeness of the finite constraints

Every ordinary unifier, of arbitrary size and with arbitrary remaining
variables, supplies a satisfying finite table. Ranks are compressed from the
heights of its actual graph subtrees, not bounded by an assumption about the
unifier. Together with reconstruction this proves an exact finite reduction.
-/

namespace ACUIhE.ACUIESolver.Finite

open Branching (graph)

universe u v w
variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Target]

theorem extracted_row (ts : List (ACUIE.Term Const Var)) (closed : Closed ts)
    (σ : ACUIE.Substitution Const Var Target) (t : ACUIE.Term Const Var) (member : t ∈ ts) :
    Table.Row ts (extracted ts σ) t := by
  cases t with
  | zero =>
    change Table.lookup ts (extracted ts σ) .zero = ∅
    rw [lookup_extracted ts σ member, Branching.graph_zero, project_zero]
  | var => trivial
  | const c =>
    change Table.lookup ts (extracted ts σ) (.const c) = _
    rw [lookup_extracted ts σ member, Branching.graph_const, project_const]
  | add a b =>
    change Table.lookup ts (extracted ts σ) (.add a b) = _
    rw [lookup_extracted ts σ member,
      lookup_extracted ts σ (closed.add_left member),
      lookup_extracted ts σ (closed.add_right member), Branching.graph_add, project_add]
  | free a =>
    change (_ → _) ∧ _
    constructor
    · intro empty
      rw [lookup_extracted ts σ member, Branching.graph_free] at empty
      have zero : graph σ a = 0 := by
        by_contra nonzero
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp member
        have self := (mem_project_free ts σ (graph σ a) i).mpr ⟨a, hi, nonzero, rfl⟩
        rw [empty] at self
        exact Finset.notMem_empty i self
      rw [lookup_extracted ts σ (closed.free_body member), zero, project_zero]
    · intro j hj
      rw [lookup_extracted ts σ member, Branching.graph_free] at hj
      obtain ⟨b, hb, _, eq⟩ := (mem_project_free ts σ (graph σ a) j).mp hj
      unfold Table.Compatible
      rw [hb]
      have body : b ∈ ts := closed.free_body (List.mem_iff_get.mpr ⟨j, hb⟩)
      change Table.lookup ts (extracted ts σ) b = Table.lookup ts (extracted ts σ) a
      rw [lookup_extracted ts σ body, lookup_extracted ts σ (closed.free_body member), eq]

theorem extracted_ranked (ts : List (ACUIE.Term Const Var)) (closed : Closed ts)
    (σ : ACUIE.Substitution Const Var Target) : Table.Ranked ts (extracted ts σ) := by
  intro i
  unfold Table.RankRow
  cases hi : ts.get i with
  | zero | const | var | add => trivial
  | free a =>
    intro j hj
    have body : a ∈ ts := closed.free_body (List.mem_iff_get.mpr ⟨i, hi⟩)
    rw [lookup_extracted ts σ body] at hj
    exact compressedRank_strict _ (score_lt_of_member ts σ hi hj)

/-- Extraction works for arbitrary unifiers; it does not assume groundness. -/
theorem extracted_valid (p : Problem Const Var) (σ : ACUIE.Substitution Const Var Target)
    (unifier : p.IsUnifier σ) : Table.Valid (pool p) p (extracted (pool p) σ) := by
  refine ⟨fun i => extracted_row _ (pool_closed p) σ _ (List.mem_iff_get.mpr ⟨i, rfl⟩),
    extracted_ranked _ (pool_closed p) σ, ?_⟩
  intro q hq
  rw [lookup_extracted _ σ (pool_left p hq), lookup_extracted _ σ (pool_right p hq),
    (Branching.equal_iff_graph σ q.left q.right).mp (unifier q hq)]

omit [DecidableEq Target] in
/-- Exact reduction of the original semantic unifiability question to finite data. -/
theorem unifiable_iff_exists_valid (p : Problem Const Var) :
    p.Unifiable ↔ ∃ d : Table (pool p).length, Table.Valid (pool p) p d := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨extracted (pool p) σ, extracted_valid p σ hσ⟩
  · rintro ⟨d, hd⟩
    exact ⟨Table.reconstruct (pool p) d, Table.reconstruct_sound p d hd⟩

end ACUIhE.ACUIESolver.Finite
