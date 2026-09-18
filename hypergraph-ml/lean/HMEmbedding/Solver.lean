import HMEmbedding.Typing
import ACUIhE.ACUIESolver.Finite.Height

set_option autoImplicit false

namespace HMEmbedding
open ACUIhE

namespace Retraction

abbrev G := Graph Constant Empty Field
abbrev rank := ACUIESolver.Finite.height (Const := Constant) (Var := Empty) (Hom := Field)

def content (i : Op) (a b : G) : G :=
  Graph.constant (.tag i) + (Graph.hom .first a + (Graph.hom .second b + 0))

def node (i : Op) (a b : G) : G := Graph.free (content i a b)

@[simp] theorem tag_member (i j : Op) (a b : G) :
    ([], Sum.inl (ACUIh.Particle.const (.tag j))) ∈ (content i a b).layer ↔ j = i := by
  simp [content, Graph.layer_add, Graph.layer_constant, Graph.layer_hom,
    Finset.mem_image]

@[simp] theorem first_member (i : Op) (a b : G) (w : List Field)
    (p : Graph.Atom Constant Empty Field) :
    (Field.first :: w, p) ∈ (content i a b).layer ↔ (w, p) ∈ a.layer := by
  simp [content, Graph.layer_add, Graph.layer_constant, Graph.layer_hom,
    Finset.mem_image, Prod.exists, Prod.mk.injEq]

@[simp] theorem second_member (i : Op) (a b : G) (w : List Field)
    (p : Graph.Atom Constant Empty Field) :
    (Field.second :: w, p) ∈ (content i a b).layer ↔ (w, p) ∈ b.layer := by
  simp [content, Graph.layer_add, Graph.layer_constant, Graph.layer_hom,
    Finset.mem_image, Prod.exists, Prod.mk.injEq]

theorem content_ne_zero (i : Op) (a b : G) : content i a b ≠ 0 := by
  intro h
  have member := (tag_member i i a b).mpr rfl
  rw [h, Graph.layer_zero] at member
  exact Finset.notMem_empty _ member

/-- O_i decomposes uniquely even when its arguments are arbitrary ACUIhE graphs. -/
theorem node_injective {i j : Op} {a b c d : G} (h : node i a b = node j c d) :
    i = j ∧ a = c ∧ b = d := by
  have same := Graph.free_injective h
  have tags : i = j := by
    have hm := (tag_member i i a b).mpr rfl
    rw [same] at hm
    exact (tag_member j i c d).mp hm
  refine ⟨tags, ?_, ?_⟩
  · apply Graph.layer_injective
    ext s
    rcases s with ⟨w, p⟩
    rw [← first_member i a b w p, same, first_member]
  · apply Graph.layer_injective
    ext s
    rcases s with ⟨w, p⟩
    rw [← second_member i a b w p, same, second_member]

theorem node_ne_base (i : Op) (a b : G) (n : Nat) :
    node i a b ≠ Graph.constant (.base n) := by
  intro h
  have layers := congrArg Graph.layer h
  simp [node, Graph.layer_free_of_ne_zero _ (content_ne_zero i a b),
    Graph.layer_constant] at layers

theorem base_injective {n m : Nat}
    (h : (Graph.constant (.base n) : G) = Graph.constant (.base m)) : n = m := by
  have layers := congrArg Graph.layer h
  simpa [Graph.layer_constant] using layers

theorem rank_layer (g : G) : rank g = g.layer.attach.sup
    (fun s => match s.val.2 with
      | .inl _ => 0
      | .inr child => rank child.val + 1) := by
  unfold rank ACUIESolver.Finite.height
  rw [Graph.fold_eq]
  change g.layer.attach.sup _ = g.layer.attach.sup _
  congr 1
  funext s
  rcases s with ⟨⟨w, p⟩, hs⟩
  cases p <;> rfl

theorem rank_le_of_children (a b : G)
    (h : ∀ w (c : {g : G // g ≠ 0}), (w, .inr c) ∈ a.layer →
      ∃ w', (w', .inr c) ∈ b.layer) : rank a ≤ rank b := by
  rw [rank_layer a]
  apply Finset.sup_le
  intro s _
  rcases s with ⟨⟨w, p⟩, member⟩
  cases p with
  | inl => exact Nat.zero_le _
  | inr child =>
    obtain ⟨w', hm⟩ := h w child member
    exact Nat.succ_le_of_lt (ACUIESolver.Finite.height_child ⟨w', child.property, hm⟩)

theorem rank_content_lt (i : Op) (a b : G) : rank (content i a b) < rank (node i a b) := by
  apply ACUIESolver.Finite.height_child
  refine ⟨[], content_ne_zero i a b, ?_⟩
  rw [node, Graph.layer_free_of_ne_zero _ (content_ne_zero i a b)]
  exact Finset.mem_singleton_self _

theorem rank_first_lt (i : Op) (a b : G) : rank a < rank (node i a b) := by
  apply Nat.lt_of_le_of_lt _ (rank_content_lt i a b)
  apply rank_le_of_children
  intro w c hm
  exact ⟨.first :: w, (first_member i a b w (.inr c)).mpr hm⟩

theorem rank_second_lt (i : Op) (a b : G) : rank b < rank (node i a b) := by
  apply Nat.lt_of_le_of_lt _ (rank_content_lt i a b)
  apply rank_le_of_children
  intro w c hm
  exact ⟨.second :: w, (second_member i a b w (.inr c)).mpr hm⟩

/-- Collapse non-HM leaves to one base type, while retaining EVERY O_i node.
This is a proof construction, not a second unification algorithm. -/
noncomputable def retract (g : G) : Mono Nat := by
  classical
  exact if h : ∃ p : Op × G × G, g = node p.1 p.2.1 p.2.2 then
      let p := Classical.choose h
      .op p.1 (retract p.2.1) (retract p.2.2)
    else if h : ∃ n, g = Graph.constant (.base n) then
      .base (Classical.choose h)
    else .base 0
termination_by rank g
decreasing_by
  · have eq := Classical.choose_spec h
    exact lt_of_lt_of_eq (rank_first_lt _ _ _) (congrArg rank eq.symm)
  · have eq := Classical.choose_spec h
    exact lt_of_lt_of_eq (rank_second_lt _ _ _) (congrArg rank eq.symm)

@[simp] theorem retract_node (i : Op) (a b : G) :
    retract (node i a b) = .op i (retract a) (retract b) := by
  rw [retract]
  split
  · rename_i h
    have same := node_injective (Classical.choose_spec h)
    rcases same with ⟨hi, ha, hb⟩
    simp only [← hi, ← ha, ← hb]
  · rename_i h
    exact (h ⟨(i, a, b), rfl⟩).elim

@[simp] theorem retract_base (n : Nat) : retract (Graph.constant (.base n)) = .base n := by
  rw [retract]
  split
  · rename_i h
    obtain ⟨⟨i, a, b⟩, eq⟩ := h
    exact (node_ne_base i a b n eq.symm).elim
  · split
    · rename_i h
      have eq := base_injective (Classical.choose_spec h)
      rw [← eq]
    · rename_i h
      exact (h ⟨n, rfl⟩).elim

theorem retract_eval (t : Mono Nat) (s : Nat → G) :
    retract (t.encode.eval Graph.constant s) = t.subst (fun v => retract (s v)) := by
  induction t with
  | var => rfl
  | base n => exact retract_base n
  | op i a b ia ib =>
    change retract (node i (a.encode.eval Graph.constant s) (b.encode.eval Graph.constant s)) = _
    rw [retract_node, ia, ib]
    rfl

end Retraction

abbrev Constraints := List (Mono Nat × Mono Nat)

def encodeConstraints (p : Constraints) : Solver.Problem Constant Nat Field :=
  p.map fun q => ⟨q.1.encode, q.2.encode⟩

def HMUnifier (p : Constraints) (s : Nat → Mono Nat) : Prop :=
  ∀ q ∈ p, q.1.subst s = q.2.subst s

def HMUnifiable (p : Constraints) : Prop := ∃ s, HMUnifier p s

theorem unifier_iff (p : Constraints) (s : Nat → Mono Nat) :
    HMUnifier p s ↔ (encodeConstraints p).IsUnifier (fun v => (s v).encode) := by
  constructor
  · intro h q hq
    obtain ⟨q, member, rfl⟩ := List.mem_map.mp hq
    change (q.1.encode.substitute _).Equal (q.2.encode.substitute _)
    rw [← encode_subst, ← encode_subst, encode_equal_iff]
    exact h q member
  · intro h q hq
    have eq : (q.1.encode.substitute (fun v => (s v).encode)).Equal
        (q.2.encode.substitute (fun v => (s v).encode)) :=
      h ⟨q.1.encode, q.2.encode⟩ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    apply (encode_equal_iff _ _).mp
    rw [encode_subst, encode_subst]
    exact eq

/-- Even an unrestricted ACUIhE solution yields an HM substitution. -/
theorem unifiable_iff (p : Constraints) :
    HMUnifiable p ↔ (encodeConstraints p).Unifiable := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨fun v => (s v).encode, (unifier_iff p s).mp hs⟩
  · intro h
    obtain ⟨s, hs⟩ := (Solver.Problem.unifiable_iff_graph _).mp h
    refine ⟨fun v => Retraction.retract (s v), ?_⟩
    intro q hq
    have eq := hs ⟨q.1.encode, q.2.encode⟩ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    have decoded := congrArg Retraction.retract eq
    simpa only [Retraction.retract_eval] using decoded

/-- The existing executable solver decides the translated HM constraint problems.
No most-general unifier is assumed or computed by this theorem. -/
theorem solver_iff (p : Constraints) :
    Solver.isUnifiable (encodeConstraints p) = true ↔ HMUnifiable p :=
  (Solver.isUnifiable_iff _).trans (unifiable_iff p).symm

end HMEmbedding
