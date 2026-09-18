import ACUIhE.Graph.Layers

/-!
# Structural folds over canonical graphs

`FoldAlgebra` describes particles, E edges, and a finite layer. Layer results
are indexed by the original summands: distinct summands are never merged just
because their computed results coincide. No equality or algebra structure on
the result type is required.

`fold` follows only E children and hides the quotient presentation and the
termination argument. Like `layer`, it is executable given decidable equality
of the three label types. It is a pure structural fold, not an ordered traversal
or a promise of memoization across repeated children.
-/

namespace ACUIhE.Graph

universe u v w x y

/-- Handlers for a whole canonical graph. The layer handler receives its
original finite-set keys and one result per key, not a set of result values. -/
structure FoldAlgebra (Const : Type u) (Var : Type v) (Hom : Type w) (Result : Type x) where
  atom : List Hom → ACUIh.Particle Const Var → Result
  edge : List Hom → {child : Graph Const Var Hom // child ≠ 0} → Result → Result
  layer : (entries : Layer Const Var Hom) → (↑entries → Result) → Result

variable {Const : Type u} {Var : Type v} {Hom : Type w} {Result : Type x}

/-- A result transformation that commutes with all three handlers. Layer keys
remain unchanged; only their associated values are transformed. -/
structure FoldAlgebra.Morphism {Other : Type y}
    (source : FoldAlgebra Const Var Hom Result) (target : FoldAlgebra Const Var Hom Other) where
  map : Result → Other
  map_atom : ∀ word particle, map (source.atom word particle) = target.atom word particle
  map_edge : ∀ word child result,
    map (source.edge word child result) = target.edge word child (map result)
  map_layer : ∀ entries values,
    map (source.layer entries values) = target.layer entries (fun s => map (values s))

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- An immediate recursive dependency: the child of an E summand at this layer. -/
def Child (child parent : Graph Const Var Hom) : Prop :=
  ∃ word, ∃ nonzero : child ≠ 0, (word, .inr ⟨child, nonzero⟩) ∈ parent.layer

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
private theorem childForest_le (word : List Hom) (first : Presentation.Tree Const Var Hom)
    (rest : Presentation.Forest Const Var Hom) :
    sizeOf (first :: rest) ≤ sizeOf (Presentation.Tree.edge word first rest) := by
  simp only [List.cons.sizeOf_spec, Presentation.Tree.edge.sizeOf_spec]
  omega

/-- Canonical child edges are well-founded, independently of the chosen presentation. -/
theorem child_wellFounded : WellFounded (Child (Const := Const) (Var := Var) (Hom := Hom)) := by
  constructor
  intro graph
  refine Quotient.inductionOn graph ?_
  intro xs
  induction xs using (measure (fun xs : Presentation.Forest Const Var Hom => sizeOf xs)).wf.induction
  rename_i xs ih
  apply Acc.intro
  intro child member
  obtain ⟨word, nonzero, member⟩ := member
  change (word, .inr ⟨child, nonzero⟩) ∈ Presentation.toLayer xs at member
  obtain ⟨tree, ht, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  cases tree with
  | atom word' particle =>
      have impossible := congrArg Prod.snd equal
      simp only [Presentation.Tree.toSummand] at impossible
      cases impossible
  | edge word' first rest =>
      have same : ofPresentation (first :: rest) = child :=
        congrArg Subtype.val (Sum.inr.inj (congrArg Prod.snd equal))
      rw [← same]
      apply ih (first :: rest)
      exact Nat.lt_of_le_of_lt (childForest_le word' first rest) (List.sizeOf_lt_of_mem ht)

/-- Structural induction over canonical E children, without raw presentations. -/
@[elab_as_elim] theorem inductionOn {P : Graph Const Var Hom → Prop}
    (graph : Graph Const Var Hom)
    (step : ∀ graph, (∀ child, Child child graph → P child) → P graph) : P graph :=
  child_wellFounded.induction graph step

/-- A layer-oriented form of structural induction. -/
@[elab_as_elim] theorem layer_inductionOn {P : Graph Const Var Hom → Prop}
    (graph : Graph Const Var Hom)
    (step : ∀ graph,
      (∀ word (child : {g : Graph Const Var Hom // g ≠ 0}),
        (word, .inr child) ∈ graph.layer → P child.val) → P graph) : P graph := by
  refine inductionOn (P := P) graph ?_
  intro graph ih
  exact step graph (fun word child member => ih child.val ⟨word, child.property, member⟩)

namespace FoldAlgebra

/-- Evaluate one original summand using results for its canonical E children. -/
def summand (algebra : FoldAlgebra Const Var Hom Result) (graph : Graph Const Var Hom)
    (recurse : ∀ child, Child child graph → Result) :
    (s : Summand Const Var Hom) → s ∈ graph.layer → Result
  | (word, .inl particle), _ => algebra.atom word particle
  | (word, .inr child), member =>
      algebra.edge word child (recurse child.val ⟨word, child.property, member⟩)

@[simp] theorem summand_atom (algebra : FoldAlgebra Const Var Hom Result)
    (graph : Graph Const Var Hom) (recurse : ∀ child, Child child graph → Result)
    (word : List Hom) (particle : ACUIh.Particle Const Var)
    (member : (word, .inl particle) ∈ graph.layer) :
    algebra.summand graph recurse (word, .inl particle) member = algebra.atom word particle := rfl

@[simp] theorem summand_edge (algebra : FoldAlgebra Const Var Hom Result)
    (graph : Graph Const Var Hom) (recurse : ∀ child, Child child graph → Result)
    (word : List Hom) (child : {g : Graph Const Var Hom // g ≠ 0})
    (member : (word, .inr child) ∈ graph.layer) :
    algebra.summand graph recurse (word, .inr child) member =
      algebra.edge word child (recurse child.val ⟨word, child.property, member⟩) := rfl

/-- One layer of the fold, retaining the original keys in the indexing type. -/
def step (algebra : FoldAlgebra Const Var Hom Result) (graph : Graph Const Var Hom)
    (recurse : ∀ child, Child child graph → Result) : Result :=
  algebra.layer graph.layer (fun s => algebra.summand graph recurse s.val s.property)

theorem step_congr (algebra : FoldAlgebra Const Var Hom Result) (graph : Graph Const Var Hom)
    {left right : ∀ child, Child child graph → Result}
    (same : ∀ child member, left child member = right child member) :
    algebra.step graph left = algebra.step graph right :=
  congrArg (algebra.step graph) (funext (fun child => funext (same child)))

theorem Morphism.step {Other : Type y} {source : FoldAlgebra Const Var Hom Result}
    {target : FoldAlgebra Const Var Hom Other} (morphism : source.Morphism target)
    (graph : Graph Const Var Hom) (recurse : ∀ child, Child child graph → Result) :
    morphism.map (source.step graph recurse) =
      target.step graph (fun child member => morphism.map (recurse child member)) := by
  unfold FoldAlgebra.step
  rw [morphism.map_layer]
  congr 1
  funext entry
  rcases entry with ⟨⟨word, atom⟩, member⟩
  cases atom with
  | inl particle => exact morphism.map_atom word particle
  | inr child => exact morphism.map_edge word child _

end FoldAlgebra

local instance : WellFoundedRelation (Graph Const Var Hom) where
  rel := Child
  wf := child_wellFounded

/-- An executable, presentation-independent fold over the entire canonical graph. -/
def fold (algebra : FoldAlgebra Const Var Hom Result) (graph : Graph Const Var Hom) : Result :=
  algebra.step graph (fun child _member => fold algebra child)
termination_by graph
decreasing_by exact _member

/-- The defining equation is deliberately not a simp rule: unfolding it on an
unknown graph would recursively expose unknown children without bound. -/
theorem fold_eq (algebra : FoldAlgebra Const Var Hom Result) (graph : Graph Const Var Hom) :
    fold algebra graph = algebra.step graph (fun child _ => fold algebra child) := by
  rw [fold]

/-- Any function satisfying the same layer equation is this fold. -/
theorem fold_unique (algebra : FoldAlgebra Const Var Hom Result)
    (f : Graph Const Var Hom → Result)
    (equation : ∀ graph, f graph = algebra.step graph (fun child _ => f child)) :
    f = fold algebra := by
  funext graph
  refine inductionOn (P := fun graph => f graph = fold algebra graph) graph ?_
  intro graph ih
  rw [equation, fold_eq]
  exact algebra.step_congr graph ih

/-- A handler-preserving postprocessing step can be fused into the whole fold. -/
theorem fold_fusion {Other : Type y} {source : FoldAlgebra Const Var Hom Result}
    {target : FoldAlgebra Const Var Hom Other} (morphism : source.Morphism target)
    (graph : Graph Const Var Hom) :
    morphism.map (fold source graph) = fold target graph := by
  apply congrFun (fold_unique target (fun graph => morphism.map (fold source graph)) ?_) graph
  intro graph
  rw [fold_eq, morphism.step]

/-- A zero graph presents an empty layer; there are no callbacks to supply values for. -/
@[simp] theorem fold_zero (algebra : FoldAlgebra Const Var Hom Result) :
    fold algebra (0 : Graph Const Var Hom) =
      algebra.layer ∅ (fun s => False.elim (Finset.notMem_empty s.val s.property)) := by
  rw [fold_eq]
  unfold FoldAlgebra.step
  congr 1
  funext s
  exact False.elim (Finset.notMem_empty s.val s.property)

/-- A singleton layer contributes exactly its own handler result, indexed by
the original summand. This also covers arbitrary homomorphism words. -/
theorem fold_singleton (algebra : FoldAlgebra Const Var Hom Result)
    (graph : Graph Const Var Hom) (s : Summand Const Var Hom) (singleton : graph.layer = {s}) :
    fold algebra graph = algebra.layer {s}
      (fun _ => algebra.summand graph (fun child _ => fold algebra child) s
        (singleton.symm ▸ Finset.mem_singleton_self s)) := by
  rw [fold_eq]
  unfold FoldAlgebra.step
  have same : (fun entry : ↑graph.layer =>
      algebra.summand graph (fun child _ => fold algebra child) entry.val entry.property) =
      (fun _ : ↑graph.layer => algebra.summand graph (fun child _ => fold algebra child) s
        (singleton.symm ▸ Finset.mem_singleton_self s)) := by
    funext entry
    rcases entry with ⟨entry, member⟩
    have eq : entry = s := Finset.mem_singleton.mp (singleton ▸ member)
    subst entry
    rfl
  rw [same]
  exact congrArg (fun entries => algebra.layer entries
    (fun _ => algebra.summand graph (fun child _ => fold algebra child) s
      (singleton.symm ▸ Finset.mem_singleton_self s))) singleton

@[simp] theorem fold_constant (algebra : FoldAlgebra Const Var Hom Result) (name : Const) :
    fold algebra (constant name) =
      algebra.layer {([], .inl (.const name))} (fun _ => algebra.atom [] (.const name)) :=
  fold_singleton algebra _ _ (layer_constant name)

@[simp] theorem fold_ofVariable (algebra : FoldAlgebra Const Var Hom Result) (name : Var) :
    fold algebra (ofVariable name) =
      algebra.layer {([], .inl (.var name))} (fun _ => algebra.atom [] (.var name)) :=
  fold_singleton algebra _ _ (layer_ofVariable name)

/-- Only nonzero E children contribute an edge to a canonical layer. -/
theorem layer_free_of_ne_zero (graph : Graph Const Var Hom) (nonzero : graph ≠ 0) :
    (free graph).layer = {([], .inr ⟨graph, nonzero⟩)} := by
  revert nonzero
  refine Quotient.inductionOn graph ?_
  intro xs nonzero
  cases xs with
  | nil => exact (nonzero rfl).elim
  | cons first rest =>
      change (free (ofPresentation (first :: rest))).layer =
        {([], .inr ⟨ofPresentation (first :: rest), nonzero⟩)}
      simp [free_ofPresentation, Presentation.free, layer_ofPresentation,
        Presentation.toLayer, Presentation.Tree.toSummand]

@[simp] theorem fold_free_of_ne_zero (algebra : FoldAlgebra Const Var Hom Result)
    (graph : Graph Const Var Hom) (nonzero : graph ≠ 0) :
    fold algebra (free graph) =
      algebra.layer {([], .inr ⟨graph, nonzero⟩)}
        (fun _ => algebra.edge [] ⟨graph, nonzero⟩ (fold algebra graph)) :=
  fold_singleton algebra _ _ (layer_free_of_ne_zero graph nonzero)

@[simp] theorem fold_free_zero (algebra : FoldAlgebra Const Var Hom Result) :
    fold algebra (free (0 : Graph Const Var Hom)) = fold algebra 0 := rfl

end ACUIhE.Graph
