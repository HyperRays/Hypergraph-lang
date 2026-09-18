import ACUIhE.ACUIESolver.Branching.Compile

/-! # Soundness and exhaustiveness of constructor branching -/

namespace ACUIhE.ACUIESolver.Branching

universe u v w

variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Target]

theorem vanish_correct (σ : ACUIE.Substitution Const Var Target) (t : ACUIE.Term Const Var) :
    (vanish t).Holds σ ↔ graph σ t = 0 := by
  induction t with
  | zero => simp [vanish, Plan.Holds]
  | const c => simp [vanish, Plan.Holds, constant_ne_zero]
  | var v => exact equal_iff_graph σ (.var v) .zero
  | add a b ha hb =>
    simp only [vanish, Plan.Holds, ha, hb, graph_add]
    simp only [← Graph.layer_eq_iff, Graph.layer_add, Graph.layer_zero, Finset.union_eq_empty]
  | free a ha => simpa only [vanish, graph_free, free_eq_zero] using ha

theorem locateConstant_correct (σ : ACUIE.Substitution Const Var Target)
    (c : Const) (t : ACUIE.Term Const Var) :
    (locateConstant c t).Holds σ ↔ (Graph.constant c).layer ⊆ (graph σ t).layer := by
  induction t with
  | zero => simp [locateConstant, Plan.Holds]
  | const d => by_cases h : c = d <;> simp [locateConstant, h, Plan.Holds]
  | var v => exact below_iff_layer σ (.const c) (.var v)
  | add a b ha hb => simp [locateConstant, Plan.Holds, ha, hb]
  | free a => simp [locateConstant, Plan.Holds, constant_not_mem_free]

mutual
  theorem compare_correct (σ : ACUIE.Substitution Const Var Target)
      (a b : ACUIE.Term Const Var) : (compare a b).Holds σ ↔ graph σ a = graph σ b := by
    cases a <;> cases b
    all_goals rw [compare]
    all_goals try solve | simp
    all_goals try first
      | exact (vanish_correct σ _).trans eq_comm
      | exact vanish_correct σ _
      | exact equal_iff_graph σ _ _
    case const.const c d =>
      by_cases h : c = d <;> simp [h, Plan.Holds, constant_eq_constant]
    case const.free c b => simp [Plan.Holds, constant_ne_free]
    case free.const a c => simp [Plan.Holds, ne_comm, constant_ne_free]
    case free.free a b =>
      simpa only [graph_free, Graph.free_injective.eq_iff] using compare_correct σ a b
    all_goals
      rw [Plan.Holds, cover_correct, cover_correct]
      exact ⟨fun h => Graph.layer_injective (Finset.Subset.antisymm h.1 h.2),
        fun h => by rw [h]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩⟩
  termination_by (nodes a + nodes b, 2)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega

  theorem cover_correct (σ : ACUIE.Substitution Const Var Target)
      (a b : ACUIE.Term Const Var) : (cover a b).Holds σ ↔ (graph σ a).layer ⊆ (graph σ b).layer := by
    cases a with
    | zero => simp [cover, Plan.Holds]
    | var v => rw [cover]; exact below_iff_layer σ (.var v) b
    | const c => rw [cover]; exact locateConstant_correct σ c b
    | add a c =>
      rw [cover, Plan.Holds, cover_correct, cover_correct, graph_add, Graph.layer_add,
        Finset.union_subset_iff]
    | free a =>
      rw [cover, Plan.Holds, vanish_correct]
      by_cases h : graph σ a = 0
      · simp [graph_free, h]
      · simp only [h, false_or, locateFree_correct σ a b h, graph_free]
  termination_by (nodes a + nodes b, 1)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega

  theorem locateFree_correct (σ : ACUIE.Substitution Const Var Target)
      (a b : ACUIE.Term Const Var) (nonzero : graph σ a ≠ 0) :
      (locateFree a b).Holds σ ↔ (Graph.free (graph σ a)).layer ⊆ (graph σ b).layer := by
    cases b with
    | zero => simp only [locateFree, Plan.Holds, graph_zero, free_subset_zero, nonzero]
    | const c => simp only [locateFree, Plan.Holds, graph_const, free_not_subset_constant _ nonzero]
    | var v => rw [locateFree]; exact below_iff_layer σ (.free a) (.var v)
    | add b c =>
      rw [locateFree, Plan.Holds, locateFree_correct σ a b nonzero,
        locateFree_correct σ a c nonzero, graph_add, Graph.layer_add, free_subset_union _ _ _ nonzero]
    | free b =>
      rw [locateFree, compare_correct, graph_free, free_subset_free _ _ nonzero]
  termination_by (nodes a + 1 + nodes b, 0)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega
end

omit [DecidableEq Target] in
/-- For every ordinary substitution, a generated branch holds exactly when
the original equality does. No groundness restriction is imposed. -/
theorem compare_branches_iff (σ : ACUIE.Substitution Const Var Target)
    (a b : ACUIE.Term Const Var) :
    (a.substitute σ).Equal (b.substitute σ) ↔
      ∃ p ∈ (compare a b).branches, p.IsUnifier σ := by
  classical
  exact (equal_iff_graph σ a b).trans
    ((compare_correct σ a b).symm.trans (Plan.holds_iff_branch _ σ))

end ACUIhE.ACUIESolver.Branching
