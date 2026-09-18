import ACUIhE.Graph.Decision

/-!
# The finite-set layer interface

A canonical graph can be inspected as a finite set of `(word, atom)` pairs.
An atom is either an ordinary constant/variable or an E child that is itself
a nonzero canonical graph. `layer_injective` proves that this interface
completely determines the graph: no hidden IDs or presentation data remain.
-/

namespace ACUIhE.Graph

universe u v w

variable {Const : Type u} {Var : Type v} {Hom : Type w}

namespace Presentation

theorem ofPresentation_cons_ne_zero (first : Tree Const Var Hom) (rest : Forest Const Var Hom) :
    Graph.ofPresentation (first :: rest) ≠ 0 := by
  intro h
  have r : Rel (first :: rest) [] := Quotient.exact h
  exact List.cons_ne_nil _ _ ((rel_nil_right _).mp r)

/-- Presentational children become canonical nonzero children at the layer boundary. -/
def Tree.toSummand : Tree Const Var Hom → Graph.Summand Const Var Hom
  | .atom word p => (word, .inl p)
  | .edge word first rest =>
      (word, .inr ⟨Graph.ofPresentation (first :: rest), ofPresentation_cons_ne_zero first rest⟩)

theorem Tree.toSummand_eq_iff (a b : Tree Const Var Hom) :
    a.toSummand = b.toSummand ↔ a.Rel b := by
  cases a <;> cases b <;>
    simp [Tree.toSummand, Tree.Rel, Graph.ofPresentation_eq_iff, Rel, Setwise]

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

def toLayer (xs : Forest Const Var Hom) : Graph.Layer Const Var Hom :=
  (xs.map Tree.toSummand).toFinset

theorem toLayer_eq_iff (xs ys : Forest Const Var Hom) : toLayer xs = toLayer ys ↔ Rel xs ys := by
  constructor
  · intro h
    constructor
    · intro t ht
      have hm : t.toSummand ∈ toLayer ys := h ▸
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)
      obtain ⟨s, hs, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      exact ⟨s, hs, (Tree.toSummand_eq_iff t s).mp he.symm⟩
    · intro s hs
      have hm : s.toSummand ∈ toLayer xs := h.symm ▸
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨s, hs, rfl⟩)
      obtain ⟨t, ht, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      exact ⟨t, ht, (Tree.toSummand_eq_iff t s).mp he⟩
  · intro h
    ext summand
    simp only [toLayer, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨s, hs, hr⟩ := h.1 t ht
      exact ⟨s, hs, ((Tree.toSummand_eq_iff t s).mpr hr).symm⟩
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hr⟩ := h.2 s hs
      exact ⟨t, ht, (Tree.toSummand_eq_iff t s).mpr hr⟩

end Presentation

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- The exact unordered ACUIh layer, with canonical nonzero children at E edges. -/
def layer : Graph Const Var Hom → Layer Const Var Hom :=
  Quotient.lift Presentation.toLayer (fun xs ys h => (Presentation.toLayer_eq_iff xs ys).mpr h)

@[simp] theorem layer_ofPresentation (xs : Presentation.Forest Const Var Hom) :
    layer (ofPresentation xs) = Presentation.toLayer xs := rfl

/-- Literal layer equality determines the whole canonical graph. -/
theorem layer_injective : Function.Injective (layer (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro xs ys h
  exact Quotient.sound ((Presentation.toLayer_eq_iff xs ys).mp h)

theorem layer_eq_iff (a b : Graph Const Var Hom) : a.layer = b.layer ↔ a = b :=
  ⟨fun h => layer_injective h, congrArg layer⟩

@[simp] theorem layer_zero : layer (0 : Graph Const Var Hom) = ∅ := rfl

@[simp] theorem layer_add (a b : Graph Const Var Hom) : layer (a + b) = layer a ∪ layer b := by
  refine Quotient.inductionOn₂ a b ?_
  intro xs ys
  change Presentation.toLayer (xs ++ ys) = Presentation.toLayer xs ∪ Presentation.toLayer ys
  simp only [Presentation.toLayer, List.map_append, List.toFinset_append]

@[simp] theorem layer_constant (name : Const) :
    layer (constant name : Graph Const Var Hom) = {([], .inl (.const name))} := by
  simp [constant, layer_ofPresentation, Presentation.toLayer, Presentation.Tree.toSummand]

@[simp] theorem layer_ofVariable (name : Var) :
    layer (ofVariable name : Graph Const Var Hom) = {([], .inl (.var name))} := by
  simp [ofVariable, layer_ofPresentation, Presentation.toLayer, Presentation.Tree.toSummand]

/-- A homomorphism prefixes the word at this layer, without crossing an E edge. -/
@[simp] theorem layer_hom (h : Hom) (g : Graph Const Var Hom) :
    (hom h g).layer = g.layer.image (fun s => (h :: s.1, s.2)) := by
  refine Quotient.inductionOn g ?_
  intro xs
  have prepend (t : Presentation.Tree Const Var Hom) :
      (t.prepend h).toSummand = (h :: t.toSummand.1, t.toSummand.2) := by
    cases t <;> rfl
  change Presentation.toLayer (Presentation.hom h xs) =
    (Presentation.toLayer xs).image (fun s => (h :: s.1, s.2))
  ext s
  simp only [Presentation.toLayer, Presentation.hom, List.map_map,
    List.mem_toFinset, List.mem_map, Finset.mem_image, Function.comp_def, prepend]
  constructor
  · rintro ⟨t, ht, eq⟩
    exact ⟨t.toSummand, ⟨t, ht, rfl⟩, eq⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, eq⟩
    exact ⟨t, ht, eq⟩

/-- The canonical embedding retains exactly the original edge-free ACUIh layer. -/
@[simp] theorem layer_ofNF (normal : ACUIh.NF Const Var Hom) :
    layer (ofNF normal) = Layer.ofNF normal := by
  induction normal using Finset.induction_on with
  | empty => simp [Layer.ofNF]
  | insert summand normal _ ih =>
      simp [ofNF_insert, layer_add, ih, Layer.ofNF, Presentation.toLayer,
        Presentation.Tree.toSummand, localSummand]
      rfl

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
/-- Embedding the ACUIh fragment loses no information. -/
theorem ofNF_injective : Function.Injective (ofNF (Const := Const) (Var := Var) (Hom := Hom)) := by
  classical
  intro a b h
  apply Layer.ofNF_injective
  simpa only [layer_ofNF] using congrArg layer h

/-- The fragment embedding has no E children. -/
theorem ofNF_no_edges (normal : ACUIh.NF Const Var Hom) (word : List Hom)
    (child : Graph Const Var Hom) (nonzero : child ≠ 0) :
    (word, .inr ⟨child, nonzero⟩) ∉ layer (ofNF normal) := by
  rw [layer_ofNF]
  exact Layer.not_mem_ofNF_edge normal word child nonzero

end ACUIhE.Graph
