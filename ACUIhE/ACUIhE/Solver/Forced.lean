import ACUIhE.Solver.Prepared
import ACUIhE.ACUIESolver.Matching.Partial
import ACUIhE.ACUIESolver.Matching.WordRules

/-! Necessary positivity from rigid constants, including prefixed constants.
The test is syntactic, but its consequence holds for every substitution matrix.
No property of a guessed or reconstructed positive group is assumed. -/

namespace ACUIhE.Solver
open ACUIh.Linear ACUIESolver.Matching
universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}

def hasConstant : ACUIh.Term Const Var Hom → Bool
  | .zero | .var _ => false
  | .const _ => true
  | .add a b => hasConstant a || hasConstant b
  | .hom _ a => hasConstant a

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

omit [DecidableEq Var] in
theorem constant_nonempty (t : ACUIh.Term Const Var Hom)
    (m : GroundMatrix Const Var Hom) (h : hasConstant t = true) :
    (instantiateNF m t).Nonempty := by
  induction t with
  | zero | var => simp [hasConstant] at h
  | const c => exact Finset.singleton_nonempty _
  | add a b ia ib =>
    simp only [hasConstant, Bool.or_eq_true] at h
    exact Finset.union_nonempty.mpr (h.elim (fun h => Or.inl (ia h)) (fun h => Or.inr (ib h)))
  | hom f a ih => exact (ih h).map

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
@[simp] theorem hasConstant_lift {n : Nat} (t : ACUIh.Term Const Var Hom) :
    hasConstant (lift (n := n) t) = hasConstant t := by
  induction t <;> simp_all [lift, hasConstant]

def Prepared.required (p : Prepared Const Var Hom) : Finset (Fin p.edges.length) :=
  Finset.univ.filter (fun i => hasConstant (p.edges.get i).child)

def hasVariable (v : Var) : ACUIh.Term Const Var Hom → Bool
  | .zero | .const _ => false
  | .var w => decide (v = w)
  | .add a b => hasVariable v a || hasVariable v b
  | .hom _ a => hasVariable v a

theorem variable_support (t : ACUIh.Term Const Var Hom) (v : Var)
    (m : GroundMatrix Const Var Hom) (c : Const) (h : hasVariable v t = true)
    (present : ∃ word, (word, ACUIh.Particle.const c) ∈ (m v).toNF) :
    ∃ word, (word, ACUIh.Particle.const c) ∈ instantiateNF m t := by
  induction t with
  | zero | const => simp [hasVariable] at h
  | var w =>
    have eq : v = w := by simpa [hasVariable] using h
    subst w
    exact present
  | add a b ia ib =>
    simp only [hasVariable, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨word, hm⟩ := ia h
      exact ⟨word, Finset.mem_union_left _ hm⟩
    · obtain ⟨word, hm⟩ := ib h
      exact ⟨word, Finset.mem_union_right _ hm⟩
  | hom f a ih =>
    obtain ⟨word, hm⟩ := ih h
    exact ⟨f :: word, Finset.mem_map.mpr ⟨(word, .const c), hm, rfl⟩⟩

omit [DecidableEq Const] [DecidableEq Hom] in
@[simp] theorem hasVariable_lift {n : Nat} (v : Var) (t : ACUIh.Term Const Var Hom) :
    hasVariable v (lift (n := n) t) = hasVariable v t := by
  induction t <;> simp_all [lift, hasVariable]

/-- An E child containing another E root requires that root's positive group
to be strictly lower. These pairs are computed once for the whole search. -/
def Prepared.dependencies (p : Prepared Const Var Hom) : List (Fin p.edges.length × Fin p.edges.length) :=
  (List.finRange p.edges.length).flatMap fun i =>
    ((List.finRange p.edges.length).filter fun j =>
      hasVariable (p.edges.get j).root (p.edges.get i).child).map (i, ·)

def dependencyReady {n : Nat} (remaining : Finset (Fin n)) (labels : Labels n)
    (ij : Fin n × Fin n) : Prop :=
  if ij.2 ∈ remaining then ij.1 ∈ remaining ∨ labels ij.1 ≠ 0
  else labels ij.2 = 0 ∨ (ij.1 ∉ remaining ∧ labels ij.2 < labels ij.1)

instance {n : Nat} (r : Finset (Fin n)) (l : Labels n) (ij : Fin n × Fin n) :
    Decidable (dependencyReady r l ij) := by unfold dependencyReady; infer_instance

theorem dependencyReady_of_completion {n : Nat} (r : Finset (Fin n)) (l target : Labels n)
    (completion : Completion r l target) (i j : Fin n)
    (order : target j ≠ 0 → target j < target i) : dependencyReady r l (i, j) := by
  unfold dependencyReady
  dsimp only
  split_ifs with hj
  · by_cases hi : i ∈ r
    · exact Or.inl hi
    · right
      rw [completion.assigned i hi]
      exact Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (order (completion.pending j hj).2))
  · by_cases hz : l j = 0
    · exact Or.inl hz
    · have positive : target j ≠ 0 := by rwa [← completion.assigned j hj]
      have lt := order positive
      have hi : i ∉ r := by
        intro hi
        have above := completion.below i hi j hj hz
        rw [completion.assigned j hj] at above
        exact (lt_asymm lt above)
      exact Or.inr ⟨hi, by rwa [completion.assigned j hj, completion.assigned i hi]⟩

end ACUIhE.Solver
