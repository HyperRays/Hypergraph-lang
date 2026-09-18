import ACUIhE.ACUIESolver.Branching.Plan
import ACUIhE.Graph.Fold

/-! # Canonical-layer facts used to prove exhaustive branching -/

namespace ACUIhE.ACUIESolver.Branching

universe u v w

variable {Const : Type u} {Var : Type v} {Target : Type w}

def graph (σ : ACUIE.Substitution Const Var Target) (t : ACUIE.Term Const Var) :
    Graph Const Target Empty := Graph.normalize (t.substitute σ).toACUIhE

@[simp] theorem free_zero : Graph.free (0 : Graph Const Target Empty) = 0 := rfl

@[simp] theorem graph_zero (σ : ACUIE.Substitution Const Var Target) : graph σ .zero = 0 := rfl
@[simp] theorem graph_const (σ : ACUIE.Substitution Const Var Target) (c : Const) :
    graph σ (.const c) = Graph.constant c := rfl
@[simp] theorem graph_add (σ : ACUIE.Substitution Const Var Target) (a b : ACUIE.Term Const Var) :
    graph σ (.add a b) = graph σ a + graph σ b := rfl
@[simp] theorem graph_free (σ : ACUIE.Substitution Const Var Target) (a : ACUIE.Term Const Var) :
    graph σ (.free a) = Graph.free (graph σ a) := rfl

theorem equal_iff_graph (σ : ACUIE.Substitution Const Var Target) (a b : ACUIE.Term Const Var) :
    (a.substitute σ).Equal (b.substitute σ) ↔ graph σ a = graph σ b :=
  ACUIE.Term.equal_iff_normalize_eq _ _

variable [DecidableEq Const] [DecidableEq Target]

theorem equation_iff_layer (σ : ACUIE.Substitution Const Var Target)
    (a b : ACUIE.Term Const Var) :
    (Plan.equation ⟨a, b⟩).Holds σ ↔ (graph σ a).layer = (graph σ b).layer :=
  (equal_iff_graph σ a b).trans (Graph.layer_eq_iff _ _).symm

theorem below_iff_layer (σ : ACUIE.Substitution Const Var Target)
    (a b : ACUIE.Term Const Var) :
    (Plan.equation ⟨.add a b, b⟩).Holds σ ↔ (graph σ a).layer ⊆ (graph σ b).layer := by
  rw [equation_iff_layer, graph_add, Graph.layer_add, Finset.union_eq_right]

theorem constant_ne_zero (c : Const) : (Graph.constant c : Graph Const Target Empty) ≠ 0 := by
  intro h
  have := congrArg Graph.layer h
  simp at this

theorem constant_eq_constant (c d : Const) :
    (Graph.constant c : Graph Const Target Empty) = Graph.constant d ↔ c = d := by
  rw [← Graph.layer_eq_iff]
  simp

omit [DecidableEq Const] [DecidableEq Target] in
theorem free_eq_zero (g : Graph Const Target Empty) : Graph.free g = 0 ↔ g = 0 :=
  ⟨fun h => Graph.free_injective h, fun h => by rw [h, free_zero]⟩

theorem constant_not_mem_free (c : Const) (g : Graph Const Target Empty) :
    ([], .inl (.const c)) ∉ (Graph.free g).layer := by
  by_cases h : g = 0
  · subst g
    simp
  · rw [Graph.layer_free_of_ne_zero g h]
    simp

theorem constant_ne_free (c : Const) (g : Graph Const Target Empty) : Graph.constant c ≠ Graph.free g := by
  intro h
  have member : ([], .inl (.const c)) ∈ (Graph.free g).layer := by rw [← h]; simp
  exact constant_not_mem_free c g member

theorem free_subset_union (g a b : Graph Const Target Empty) (nonzero : g ≠ 0) :
    (Graph.free g).layer ⊆ a.layer ∪ b.layer ↔
      (Graph.free g).layer ⊆ a.layer ∨ (Graph.free g).layer ⊆ b.layer := by
  rw [Graph.layer_free_of_ne_zero g nonzero]
  simp

theorem free_subset_free (g h : Graph Const Target Empty) (nonzero : g ≠ 0) :
    (Graph.free g).layer ⊆ (Graph.free h).layer ↔ g = h := by
  by_cases zero : h = 0
  · subst h
    simp [Graph.layer_free_of_ne_zero g nonzero, nonzero]
  · rw [Graph.layer_free_of_ne_zero g nonzero, Graph.layer_free_of_ne_zero h zero]
    simp

theorem free_not_subset_constant (g : Graph Const Target Empty) (nonzero : g ≠ 0) (c : Const) :
    ¬ (Graph.free g).layer ⊆ (Graph.constant c).layer := by
  rw [Graph.layer_free_of_ne_zero g nonzero, Graph.layer_constant]
  simp

theorem free_subset_zero (g : Graph Const Target Empty) :
    (Graph.free g).layer ⊆ (0 : Graph Const Target Empty).layer ↔ g = 0 := by
  rw [Graph.layer_zero, Finset.subset_empty, ← Graph.layer_zero, Graph.layer_eq_iff, free_eq_zero]

end ACUIhE.ACUIESolver.Branching
