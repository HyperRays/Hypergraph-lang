import ACUIhE.Solver.Search
import ACUIhE.ACUIESolver.Finite.Height
import ACUIhE.ACUIESolver.Matching.Order

/-!
# A finite matching extracted from an arbitrary graph solution

This projection is used only in the completeness proof. It keeps every
homomorphism word and names the E children occurring in the input edges.
It is not an input transformation or a fallback executed by the solver.
-/

namespace ACUIhE.Solver.Projection

open ACUIh.Linear ACUIESolver.Matching

universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w} {n : Nat}
variable [DecidableEq Const] [DecidableEq Hom]

abbrev G (Const : Type u) (Hom : Type w) := Graph Const Empty Hom

def summand (values : Fin n → G Const Hom) (s : Graph.Summand Const Empty Hom) :
    ACUIh.NF (Const ⊕ Fin n) Empty Hom :=
  match s.2 with
  | .inl (.const c) => {(s.1, .const (.inl c))}
  | .inl (.var v) => Empty.elim v
  | .inr child => (Finset.univ.filter (fun j => values j = child.val)).image
      (fun j => (s.1, .const (.inr j)))

def project (values : Fin n → G Const Hom) (g : G Const Hom) :
    ACUIh.NF (Const ⊕ Fin n) Empty Hom := g.layer.biUnion (summand values)

@[simp] theorem project_zero (values : Fin n → G Const Hom) : project values 0 = ∅ := by
  simp [project]

@[simp] theorem project_constant (values : Fin n → G Const Hom) (c : Const) :
    project values (Graph.constant c) = {([], .const (.inl c))} := by
  simp [project, summand]

@[simp] theorem project_add (values : Fin n → G Const Hom) (a b : G Const Hom) :
    project values (a + b) = project values a ∪ project values b := by
  simp only [project, Graph.layer_add, Finset.union_biUnion]

@[simp] theorem project_hom (values : Fin n → G Const Hom) (h : Hom) (g : G Const Hom) :
    project values (Graph.hom h g) = ACUIh.NF.prepend h (project values g) := by
  simp only [project, Graph.layer_hom, Finset.image_biUnion, ACUIh.NF.prepend,
    Finset.map_eq_image, Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro s _
  obtain ⟨word, atom⟩ := s
  cases atom with
  | inl particle =>
    cases particle with
    | const c => simp only [summand, Finset.image_singleton]; rfl
    | var v => exact Empty.elim v
  | inr child => simp only [summand, Finset.image_image]; rfl

theorem project_free (values : Fin n → G Const Hom) (g : G Const Hom) :
    project values (Graph.free g) = WordRules.atoms
      (Finset.univ.filter (fun j => values j = g ∧ g ≠ 0)) := by
  by_cases zero : g = 0
  · simp [zero, WordRules.atoms, show Graph.free (0 : G Const Hom) = 0 from rfl]
  · simp [project, Graph.layer_free_of_ne_zero g zero, summand, WordRules.atoms, zero]

theorem child_of_mem (values : Fin n → G Const Hom) (g : G Const Hom)
    (word : List Hom) (j : Fin n)
    (member : (word, ACUIh.Particle.const (.inr j)) ∈ project values g) :
    Graph.Child (values j) g := by
  obtain ⟨⟨w, atom⟩, hs, hm⟩ := Finset.mem_biUnion.mp member
  cases atom with
  | inl particle =>
    cases particle with
    | const c => simp [summand] at hm
    | var v => exact Empty.elim v
  | inr child =>
    obtain ⟨k, hk, eq⟩ := Finset.mem_image.mp hm
    obtain ⟨wordEq, atomEq⟩ := Prod.mk.inj eq
    have indexEq : k = j := Sum.inr.inj (ACUIh.Particle.const.inj atomEq)
    subst k
    have valueEq := (Finset.mem_filter.mp hk).2
    rw [valueEq]
    exact ⟨w, child.property, hs⟩

def matrix (values : Fin n → G Const Hom) (iv : Var → G Const Hom) :
    GroundMatrix (Const ⊕ Fin n) Var Hom := fun v => Row.ofNF (project values (iv v))

local instance : ACUIh Hom (G Const Hom) := reduct

theorem instantiate_lift (values : Fin n → G Const Hom) (iv : Var → G Const Hom)
    (t : ACUIh.Term Const Var Hom) :
    instantiateNF (matrix values iv) (lift t) = project values (t.eval Graph.constant iv) := by
  induction t with
  | zero => exact (project_zero values).symm
  | const c => exact (project_constant values c).symm
  | var v => exact Row.toNF_ofNF _
  | add a b ia ib =>
    simpa only [lift, instantiateNF, ACUIh.Term.eval, project_add] using congrArg₂ (· ∪ ·) ia ib
  | hom h t ih =>
    change ACUIh.NF.prepend h (instantiateNF (matrix values iv) (lift t)) =
      project values (Graph.hom h (t.eval Graph.constant iv))
    rw [project_hom, ih]

end ACUIhE.Solver.Projection

namespace ACUIhE.Solver.Prepared

open ACUIh.Linear ACUIESolver.Matching Projection

universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Hom]
local instance : ACUIh Hom (G Const Hom) := reduct

/-- Every graph solution, at any depth and with any homomorphism words,
supplies a matching and a matrix satisfying all shared E conditions. -/
theorem matching_of_solution (p : Prepared Const Var Hom) (iv : Var → G Const Hom)
    (solution : p.Holds Graph.constant iv) : ∃ labels m, p.Matches labels m := by
  let children : Fin p.edges.length → G Const Hom := fun i => (p.edges.get i).child.eval Graph.constant iv
  let labels : Labels p.edges.length := Order.label ACUIESolver.Finite.height children
  let m : p.Matrix := Projection.matrix children iv
  have group (i : Fin p.edges.length) : Rules.group Finset.univ labels i =
      Finset.univ.filter (fun j => children j = children i ∧ children i ≠ 0) := by
    ext j
    simp [Rules.group, labels, Order.label_eq_iff]
  have child (i : Fin p.edges.length) : instantiateNF m (p.child i) = project children (children i) :=
    instantiate_lift children iv (p.edges.get i).child
  refine ⟨labels, m, (p.matches_iff labels m).mpr ⟨?_, ?_⟩⟩
  · intro rule member
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp member
    change instantiateNF m (lift q.left) = instantiateNF m (lift q.right)
    rw [instantiate_lift, instantiate_lift]
    exact congrArg (project children) (solution.1 q hq)
  · intro i
    apply (Rules.complete_iff _ _ _ _ _ _).mpr
    change instantiateNF m (p.root i) = WordRules.atoms (Rules.group Finset.univ labels i) ∧
      (Rules.group Finset.univ labels i = ∅ → instantiateNF m (p.child i) = WordRules.atoms ∅) ∧
      (∀ j ∈ Rules.group Finset.univ labels i, instantiateNF m (p.child j) = instantiateNF m (p.child i)) ∧
      (WordRules.interpretation m).support (instantiateNF m (p.child i)) ⊆ lower labels i
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (Row.ofNF (project children (iv (p.edges.get i).root))).toNF = _
      rw [Row.toNF_ofNF, solution.2 _ (List.mem_iff_get.mpr ⟨i, rfl⟩)]
      exact (project_free children (children i)).trans (congrArg WordRules.atoms (group i).symm)
    · intro empty
      have zero : children i = 0 := by
        by_contra nonzero
        have own : i ∈ Rules.group Finset.univ labels i := by rw [group]; simp [nonzero]
        rw [empty] at own
        exact Finset.notMem_empty _ own
      rw [child, zero, project_zero]
      simp [WordRules.atoms]
    · intro j member
      rw [child, child]
      exact congrArg (project children) ((Finset.mem_filter.mp (group i ▸ member)).2.1)
    · intro j member
      have nonzero : Row.ofNF (project children (children i)) (.inr j) ≠ 0 := by
        simpa only [WordRules.interpretation, child, Finset.mem_filter, Finset.mem_univ,
          true_and] using member
      have words : ((Row.ofNF (project children (children i))) (.inr j)).words.Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro empty
        exact nonzero (WordPolynomial.ext empty)
      obtain ⟨word, hw⟩ := words
      have dependency := child_of_mem children (children i) word j
        ((mem_coefficient _ _ _).mp hw)
      have positive : children i ≠ 0 := by
        intro zero
        rw [zero, project_zero, Row.ofNF_empty, Finsupp.zero_apply] at nonzero
        exact nonzero rfl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Order.label_strict ACUIESolver.Finite.height children positive
          (ACUIESolver.Finite.height_child dependency)⟩

end ACUIhE.Solver.Prepared
