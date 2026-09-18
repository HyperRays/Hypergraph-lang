import ACUIhE.Solver.Interpretation
import ACUIhE.ACUIESolver.Matching.Iteration

/-!
# Reconstruction of mixed E layers

The cached traversal and finite stabilization theorem are shared with
ACUIESolver. Only the evaluation of a layer differs. Different positive
groups may reconstruct to the same value or to zero.
-/

namespace ACUIhE.Solver.Prepared

open ACUIh.Linear ACUIESolver.Matching

universe u v w x
variable {Const : Type u} {Var : Type v} {Hom : Type w} {α : Type x}
variable [DecidableEq Const] [DecidableEq Hom] [ACUIhE Hom α]
local instance : ACUIh Hom α := reduct

def step (p : Prepared Const Var Hom) (m : p.Matrix) (ic : Const → α)
    (values : Fin p.edges.length → α) (i : Fin p.edges.length) : α :=
  E (Hom := Hom) (decode (Sum.elim ic values) (instantiateNF m (p.child i)))

def values (p : Prepared Const Var Hom) (m : p.Matrix) (ic : Const → α) :
    Fin p.edges.length → α :=
  let cached := Iteration.run (fun _ => 0) (p.step m ic) (p.edges.length + 1)
  fun i => cached[i.val]

def assignment (p : Prepared Const Var Hom) (m : p.Matrix) (ic : Const → α) : Var → α :=
  let cached := p.values m ic
  fun v => decode (Sum.elim ic cached) (m v).toNF

theorem values_fixed (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) (ic : Const → α) (i : Fin p.edges.length) :
    p.values m ic i = p.step m ic (p.values m ic) i := by
  apply Iteration.fixed (fun _ => 0) (p.step m ic) labels
  intro a b i same
  unfold step
  apply congrArg (E (Hom := Hom))
  apply decode_congr
  intro word atom member
  cases atom with
  | inl c => rfl
  | inr j =>
    apply same
    have support := ((Rules.complete_iff _ _ _ _ _ _).mp (((p.matches_iff labels m).mp valid).2 i)).2.2.2
    have nonzero := coefficient_ne_zero_of_mem _ word (Sum.inr j) member
    exact (Finset.mem_filter.mp (support (Finset.mem_filter.mpr ⟨Finset.mem_univ _, nonzero⟩))).2

theorem values_same (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) (ic : Const → α)
    (i j : Fin p.edges.length) (member : j ∈ Rules.group Finset.univ labels i) :
    p.values m ic j = p.values m ic i := by
  have eq := ((Rules.complete_iff _ _ _ _ _ _).mp (((p.matches_iff labels m).mp valid).2 i)).2.2.1 j member
  rw [p.values_fixed labels m valid ic j, p.values_fixed labels m valid ic i]
  exact congrArg (fun nf => E (Hom := Hom) (decode (Sum.elim ic (p.values m ic)) nf)) eq

theorem values_zero (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) (ic : Const → α)
    (i : Fin p.edges.length) (empty : Rules.group Finset.univ labels i = ∅) :
    p.values m ic i = 0 := by
  have eq := ((Rules.complete_iff _ _ _ _ _ _).mp (((p.matches_iff labels m).mp valid).2 i)).2.1 empty
  rw [p.values_fixed labels m valid ic i]
  unfold step
  change instantiateNF m (p.child i) = WordRules.atoms ∅ at eq
  rw [eq]
  change E (Hom := Hom) (0 : α) = 0
  exact ACUIhE.free_zero

theorem assignment_root (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) (ic : Const → α) (i : Fin p.edges.length) :
    p.assignment m ic (p.edges.get i).root = p.values m ic i := by
  have root := ((Rules.complete_iff _ _ _ _ _ _).mp (((p.matches_iff labels m).mp valid).2 i)).1
  change (m (p.edges.get i).root).toNF = WordRules.atoms (Rules.group Finset.univ labels i) at root
  unfold assignment
  rw [root, decode_names _ _ (p.values m ic i) (fun j member => p.values_same labels m valid ic i j member)]
  split_ifs with empty
  · exact (p.values_zero labels m valid ic i empty).symm
  · rfl

theorem decode_child (p : Prepared Const Var Hom) (m : p.Matrix) (ic : Const → α)
    (t : ACUIh.Term Const Var Hom) :
    decode (Sum.elim ic (p.values m ic)) (instantiateNF m (lift t)) =
      t.eval ic (p.assignment m ic) := by
  rw [decode_instantiate, eval_lift]
  rfl

theorem reconstruction_sound (p : Prepared Const Var Hom) (labels : Labels p.edges.length)
    (m : p.Matrix) (valid : p.Matches labels m) (ic : Const → α) :
    p.Holds ic (p.assignment m ic) := by
  obtain ⟨layers, _⟩ := (p.matches_iff labels m).mp valid
  constructor
  · intro q hq
    have same := layers _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    change instantiateNF m (lift q.left) = instantiateNF m (lift q.right) at same
    change q.left.eval ic (p.assignment m ic) = q.right.eval ic (p.assignment m ic)
    rw [← p.decode_child m ic q.left, ← p.decode_child m ic q.right, same]
  · intro edge member
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
    rw [p.assignment_root labels m valid ic i, p.values_fixed labels m valid ic i]
    exact congrArg (E (Hom := Hom)) (p.decode_child m ic (p.edges.get i).child)

end ACUIhE.Solver.Prepared
