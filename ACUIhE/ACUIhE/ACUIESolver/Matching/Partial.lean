import ACUIhE.ACUIESolver.Matching.Canonical

/-!
# Necessary constraints of a partial ordered matching

`remaining` contains undecided positive edges. Their stored zero labels are
placeholders, not decisions that those edges vanish. Finished positive groups
are above all remaining groups. A rejected partial system has no completion.
-/

namespace ACUIhE.ACUIESolver.Matching

open ACUIhE.ACUIESolver.Finite Layers

variable {n : Nat}

structure Completion (remaining : Finset (Fin n)) (labels target : Labels n) : Prop where
  pending : ∀ i ∈ remaining, labels i = 0 ∧ target i ≠ 0
  assigned : ∀ i, i ∉ remaining → labels i = target i
  below : ∀ i ∈ remaining, ∀ j, j ∉ remaining → labels j ≠ 0 → target i < labels j

theorem Completion.lower_eq {r : Finset (Fin n)} {labels target : Labels n}
    (h : Completion r labels target) {i : Fin n} (hi : i ∉ r) :
    lower labels i = lower target i := by
  ext j
  simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j ∈ r
  · have hz := (h.pending j hj).1
    by_cases he : labels i = 0
    · rw [hz, ← h.assigned i hi, he]
      simp
    · have hp : 0 < labels i := Fin.pos_iff_ne_zero.mpr he
      have ht := h.below j hj i hi he
      rw [hz, ← h.assigned i hi]
      exact iff_of_true hp ht
  · rw [h.assigned j hj, h.assigned i hi]

theorem Completion.same_group_assigned {r : Finset (Fin n)} {labels target : Labels n}
    (h : Completion r labels target) {i : Fin n} (hi : i ∉ r) (j : Fin n) :
    (labels j = labels i ∧ labels i ≠ 0) ↔ (target j = target i ∧ target i ≠ 0) := by
  by_cases hj : j ∈ r
  · rw [(h.pending j hj).1, ← h.assigned i hi]
    constructor
    · rintro ⟨eq, nonzero⟩
      exact (nonzero eq.symm).elim
    · rintro ⟨eq, nonzero⟩
      have strict := h.below j hj i hi nonzero
      rw [eq] at strict
      exact (lt_irrefl _ strict).elim
  · rw [h.assigned j hj, h.assigned i hi]

theorem Completion.pending_group_mem {r : Finset (Fin n)} {labels target : Labels n}
    (h : Completion r labels target) {i j : Fin n} (hi : i ∈ r)
    (same : target j = target i) : j ∈ r := by
  by_contra hj
  have nonzero : labels j ≠ 0 := by rw [h.assigned j hj, same]; exact (h.pending i hi).2
  have strict := h.below i hi j hj nonzero
  rw [h.assigned j hj, same] at strict
  exact lt_irrefl _ strict

universe u v
variable {Const : Type u} {Var : Type v} [DecidableEq Const] [DecidableEq Var]

omit [DecidableEq Const] [DecidableEq Var] in
theorem Completion.names_eq {ts : List (ACUIE.Term Const Var)} {r : Finset (Fin ts.length)}
    {labels target : Labels ts.length} (h : Completion r labels target)
    {i : Fin ts.length} (hi : i ∉ r) : names ts labels i = names ts target i := by
  ext j
  simp only [mem_names, h.same_group_assigned hi]

theorem Completion.nodeConstraints_eq {ts : List (ACUIE.Term Const Var)}
    {r : Finset (Fin ts.length)} {labels target : Labels ts.length}
    (h : Completion r labels target) {i : Fin ts.length} (hi : i ∉ r) :
    nodeConstraints ts labels i = nodeConstraints ts target i := by
  unfold nodeConstraints
  cases ts.get i <;> simp only [h.names_eq hi, h.lower_eq hi]

def partialNodeConstraints (ts : List (ACUIE.Term Const Var))
    (r : Finset (Fin ts.length)) (labels : Labels ts.length) (i : Fin ts.length) :
    System ts.length :=
  if i ∈ r then
    match ts.get i with
    | .free a =>
      FiniteRules.compile (Rules.pending (lookupExpr ts (.free a)) (lookupExpr ts a) r i)
    | _ => []
  else nodeConstraints ts labels i

def partialConstraints (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (r : Finset (Fin ts.length)) (labels : Labels ts.length) : System ts.length :=
  (List.finRange ts.length).flatMap (partialNodeConstraints ts r labels) ++
  p.flatMap (fun q => equation (lookupExpr ts q.left) (lookupExpr ts q.right))

@[simp] theorem partialConstraints_empty (ts : List (ACUIE.Term Const Var))
    (p : Problem Const Var) (labels : Labels ts.length) :
    partialConstraints ts p ∅ labels = constraints ts p labels := by
  have hn : partialNodeConstraints ts ∅ labels = nodeConstraints ts labels := by
    funext i
    simp [partialNodeConstraints]
  simp only [partialConstraints, constraints, hn]

theorem partialNodeConstraints_necessary (ts : List (ACUIE.Term Const Var))
    (p : Problem Const Var) {r : Finset (Fin ts.length)} {labels target : Labels ts.length}
    (hc : Completion r labels target) {rows : Rows ts.length}
    (hh : Holds (constraints ts p target) rows) (i : Fin ts.length) :
    Holds (partialNodeConstraints ts r labels i) rows := by
  have hn : Holds (nodeConstraints ts target i) rows := by
    exact (holds_flatMap _ _ _).mp ((holds_append _ _ _).mp hh).1 i (by simp)
  by_cases hi : i ∈ r
  · simp only [partialNodeConstraints, if_pos hi]
    cases he : ts.get i <;> try exact holds_nil rows
    rename_i a
    apply (FiniteRules.compile_exact rows _).mpr
    have full : Rules.Holds (FiniteRules.interpretation rows)
        (Rules.complete (lookupExpr ts (.free a)) (lookupExpr ts a) (childExpr ts)
          (names ts target i) (lower target i)) := by
      apply (FiniteRules.compile_exact rows _).mp
      simpa only [nodeConstraints, he] using hn
    apply Rules.pending_of_complete (FiniteRules.interpretation rows) (fun _ _ h => h)
      _ _ _ _ _ _ _ full
    · exact (mem_names ts target i i).mpr ⟨by simp only [he, isEdge], rfl, (hc.pending i hi).2⟩
    · intro j hj
      exact hc.pending_group_mem hi ((mem_names ts target i j).mp hj).2.1
    · simp [lower]
  · rw [partialNodeConstraints, if_neg hi, hc.nodeConstraints_eq hi]
    exact hn

/-- Every full completion satisfies the partial system, before choosing its remaining groups. -/
theorem partialConstraints_necessary (ts : List (ACUIE.Term Const Var))
    (p : Problem Const Var) {r : Finset (Fin ts.length)} {labels target : Labels ts.length}
    (hc : Completion r labels target) {rows : Rows ts.length}
    (hh : Holds (constraints ts p target) rows) :
    Holds (partialConstraints ts p r labels) rows := by
  apply (holds_append _ _ _).mpr
  constructor
  · apply (holds_flatMap _ _ _).mpr
    intro i _
    exact partialNodeConstraints_necessary ts p hc hh i
  · exact ((holds_append _ _ _).mp hh).2

/-- Pruning rejects all completions, not merely the placeholder assignment. -/
theorem prune_sound (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (r : Finset (Fin ts.length)) (labels : Labels ts.length)
    (h : Layers.solve (partialConstraints ts p r labels) = none)
    (target : Labels ts.length) (hc : Completion r labels target) :
    ¬ ∃ rows, Holds (constraints ts p target) rows := by
  rintro ⟨rows, hh⟩
  exact (Layers.solve_none_iff _).mp h ⟨rows, partialConstraints_necessary ts p hc hh⟩

end ACUIhE.ACUIESolver.Matching
