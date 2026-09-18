import ACUIhE.Solver.Forced

/-! Necessary constant-provider conditions for E children. A variable may
provide every constant beneath its prefix; a prefixed variable cannot provide
a shorter or differently prefixed word. These tests never choose its value. -/

namespace ACUIhE.Solver
open ACUIh.Linear
universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Hom]

def canSupply (word : List Hom) (c : Const) : ACUIh.Term Const Var Hom → Bool
  | .zero => false
  | .var _ => true
  | .const d => decide (word = [] ∧ c = d)
  | .add a b => canSupply word c a || canSupply word c b
  | .hom h a => match word with
      | [] => false
      | k :: rest => decide (h = k) && canSupply rest c a

theorem canSupply_necessary (t : ACUIh.Term Const Var Hom) (m : GroundMatrix Const Var Hom)
    (word : List Hom) (c : Const) (member : (word, .const c) ∈ instantiateNF m t) :
    canSupply word c t = true := by
  induction t generalizing word with
  | zero => simp [instantiateNF] at member
  | var => rfl
  | const d =>
    have eq := Finset.mem_singleton.mp member
    have hw : word = [] := congrArg Prod.fst eq
    have hc : c = d := ACUIh.Particle.const.inj (congrArg Prod.snd eq)
    exact decide_eq_true ⟨hw, hc⟩
  | add a b ia ib =>
    simp only [instantiateNF, Finset.mem_union] at member
    simp only [canSupply, Bool.or_eq_true]
    exact member.elim (fun h => Or.inl (ia word h)) (fun h => Or.inr (ib word h))
  | hom h a ih =>
    obtain ⟨⟨rest, atom⟩, hm, eq⟩ := Finset.mem_map.mp member
    have parts : h :: rest = word ∧ atom = .const c := Prod.mk.inj eq
    obtain ⟨rfl, rfl⟩ := parts
    simpa [canSupply] using ih rest hm

def rigidConstants : ACUIh.Term Const Var Hom → List (List Hom × Const)
  | .zero | .var _ => []
  | .const c => [([], c)]
  | .add a b => rigidConstants a ++ rigidConstants b
  | .hom h a => (rigidConstants a).map (fun p => (h :: p.1, p.2))

theorem rigidConstants_present (t : ACUIh.Term Const Var Hom) (m : GroundMatrix Const Var Hom)
    (word : List Hom) (c : Const) (member : (word, c) ∈ rigidConstants t) :
    (word, .const c) ∈ instantiateNF m t := by
  induction t generalizing word with
  | zero | var => simp [rigidConstants] at member
  | const d =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
    exact Finset.mem_singleton_self _
  | add a b ia ib =>
    rcases List.mem_append.mp member with ha | hb
    · exact Finset.mem_union_left _ (ia word ha)
    · exact Finset.mem_union_right _ (ib word hb)
  | hom h a ih =>
    obtain ⟨⟨rest, d⟩, hm, eq⟩ := List.mem_map.mp member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact Finset.mem_map.mpr ⟨(rest, .const d), ih rest hm, rfl⟩

def compatible (a b : ACUIh.Term Const Var Hom) : Bool :=
  (rigidConstants a).all (fun p => canSupply p.1 p.2 b) &&
    (rigidConstants b).all (fun p => canSupply p.1 p.2 a)

theorem compatible_necessary (a b : ACUIh.Term Const Var Hom) (m : GroundMatrix Const Var Hom)
    (eq : instantiateNF m a = instantiateNF m b) : compatible a b = true := by
  simp only [compatible, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro p hp
    apply canSupply_necessary b m p.1 p.2
    rw [← eq]
    exact rigidConstants_present a m p.1 p.2 hp
  · intro p hp
    apply canSupply_necessary a m p.1 p.2
    rw [eq]
    exact rigidConstants_present b m p.1 p.2 hp

@[simp] theorem canSupply_lift {n : Nat} (t : ACUIh.Term Const Var Hom) (word : List Hom) (c : Const) :
    canSupply word (.inl c) (lift (n := n) t) = canSupply word c t := by
  induction t generalizing word <;> simp_all [lift, canSupply]

omit [DecidableEq Const] [DecidableEq Hom] in
@[simp] theorem rigidConstants_lift {n : Nat} (t : ACUIh.Term Const Var Hom) :
    rigidConstants (lift (n := n) t) = (rigidConstants t).map (fun p => (p.1, Sum.inl p.2)) := by
  induction t <;> simp_all [lift, rigidConstants, List.map_map, Function.comp_def]

@[simp] theorem compatible_lift {n : Nat} (a b : ACUIh.Term Const Var Hom) :
    compatible (lift (n := n) a) (lift b) = compatible a b := by
  simp [compatible, rigidConstants_lift, Function.comp_def, canSupply_lift]

def Prepared.incompatible (p : Prepared Const Var Hom) : List (Fin p.edges.length × Fin p.edges.length) :=
  (List.finRange p.edges.length).flatMap fun i =>
    ((List.finRange p.edges.length).filter fun j =>
      !compatible (p.edges.get i).child (p.edges.get j).child).map (i, ·)

end ACUIhE.Solver
