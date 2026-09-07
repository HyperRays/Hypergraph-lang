import ACUIHE.Graph.graph
import ACUIHE.ACUIh.NormalForm
import Mathlib.Data.Finset.Union

/-!
Embedding ACUIh fragments into the generic graph.

Node labels hold ordinary constants and variables. An alien summand becomes
an edge, labelled by its surrounding homomorphism path: `(path, target)`
denotes `path(E(target))`. The graph definition itself has no such semantics.
-/

namespace ACUIHE.Graph

universe u v w x

/-- A generator of an ACUIh fragment before its alien references become edges. -/
inductive Atom (Const : Type u) (Var : Type v) (Alien : Type x) where
  | constant (name : Const)
  | variable (name : Var)
  | alien (reference : Alien)
  deriving DecidableEq

/-- The generator sum underlying graph-fragment atoms. -/
def atomEquiv : Atom Const Var Alien ≃ Const ⊕ (Var ⊕ Alien) where
  toFun
    | .constant name => .inl name
    | .variable name => .inr (.inl name)
    | .alien reference => .inr (.inr reference)
  invFun
    | .inl name => .constant name
    | .inr (.inl name) => .variable name
    | .inr (.inr reference) => .alien reference
  left_inv := by intro atom; cases atom <;> rfl
  right_inv := by intro value; rcases value with name | name | reference <;> rfl

instance [Encodable Const] [Encodable Var] [Encodable Alien] :
    Encodable (Atom Const Var Alien) :=
  Encodable.ofEquiv _ atomEquiv

/-- Regard a constant or variable as a fragment generator. -/
def Atom.ofOrdinary {Const : Type u} {Var : Type v} {Alien : Type x} :
    Const ⊕ Var → Atom Const Var Alien
  | .inl name => .constant name
  | .inr name => .variable name

abbrev Fragment
    (Const : Type u) (Var : Type v) (Hom : Type w) (Alien : Type x) :=
  ACUIh.NormalForm (Atom Const Var Alien) Hom

/-- Specialize graph labels to pure ACUIh particles and homomorphism paths.
Graph equality is storage equality, not canonical expression equality. -/
abbrev TermGraph (Const : Type u) (Var : Type v) (Hom : Type w) :=
  RootedDAG (ACUIh.NormalForm (Const ⊕ Var) Hom) (List Hom)

namespace Fragment

variable {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}

/-- Reassemble a fragment from its ordinary node summands and alien edges. -/
def ofParts [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (nodes : ACUIh.NormalForm (Const ⊕ Var) Hom)
    (edges : Finset (List Hom × Alien)) : Fragment Const Var Hom Alien :=
  nodes.image (fun (path, atom) => (path, Atom.ofOrdinary atom)) ∪
    edges.image (fun (path, target) => (path, .alien target))

/-- The ordinary ACUIh summands become the node label. -/
def nodePart [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (fragment : Fragment Const Var Hom Alien) :
    ACUIh.NormalForm (Const ⊕ Var) Hom :=
  fragment.biUnion fun (path, atom) =>
    match atom with
    | .constant name => {(path, .inl name)}
    | .variable name => {(path, .inr name)}
    | .alien _ => ∅

/-- Alien summands become path-labelled edges. -/
def edgePart [DecidableEq Hom] [DecidableEq Alien]
    (fragment : Fragment Const Var Hom Alien) : Finset (List Hom × Alien) :=
  fragment.biUnion fun (path, atom) =>
    match atom with
    | .constant _ => ∅
    | .variable _ => ∅
    | .alien target => {(path, target)}

/-- Extracting the node label preserves exactly the ordinary summands. -/
@[simp]
theorem mem_nodePart [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (fragment : Fragment Const Var Hom Alien) (path : List Hom) (atom : Const ⊕ Var) :
    (path, atom) ∈ fragment.nodePart ↔ (path, Atom.ofOrdinary atom) ∈ fragment := by
  simp only [nodePart, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨homPath, source⟩, membership, found⟩
    cases source with
    | constant name =>
        have equality := Finset.mem_singleton.mp found
        cases equality
        exact membership
    | «variable» name =>
        have equality := Finset.mem_singleton.mp found
        cases equality
        exact membership
    | alien reference => exact False.elim (Finset.notMem_empty _ found)
  · intro membership
    refine ⟨(path, Atom.ofOrdinary atom), membership, ?_⟩
    cases atom <;> exact Finset.mem_singleton_self _

/-- Extracting edges preserves exactly the alien summands and their paths. -/
@[simp]
theorem mem_edgePart [DecidableEq Hom] [DecidableEq Alien]
    (fragment : Fragment Const Var Hom Alien) (path : List Hom) (target : Alien) :
    (path, target) ∈ fragment.edgePart ↔ (path, .alien target) ∈ fragment := by
  simp only [edgePart, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨homPath, atom⟩, membership, edge⟩
    cases atom with
    | constant name => exact False.elim (Finset.notMem_empty _ edge)
    | «variable» name => exact False.elim (Finset.notMem_empty _ edge)
    | alien reference =>
        have equality := Finset.mem_singleton.mp edge
        cases equality
        exact membership
  · intro membership
    exact ⟨(path, .alien target), membership, Finset.mem_singleton_self _⟩

/-- Splitting a fragment into a node label and edges loses no information. -/
theorem parts_injective
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] [DecidableEq Alien]
    {left right : Fragment Const Var Hom Alien}
    (nodes : left.nodePart = right.nodePart) (edges : left.edgePart = right.edgePart) :
    left = right := by
  apply Finset.ext
  rintro ⟨path, atom⟩
  cases atom with
  | constant name =>
      change (path, Atom.ofOrdinary (.inl name : Const ⊕ Var)) ∈ left ↔
        (path, Atom.ofOrdinary (.inl name : Const ⊕ Var)) ∈ right
      rw [← mem_nodePart, ← mem_nodePart, nodes]
  | «variable» name =>
      change (path, Atom.ofOrdinary (.inr name : Const ⊕ Var)) ∈ left ↔
        (path, Atom.ofOrdinary (.inr name : Const ⊕ Var)) ∈ right
      rw [← mem_nodePart, ← mem_nodePart, nodes]
  | alien reference => rw [← mem_edgePart, ← mem_edgePart, edges]

@[simp]
theorem nodePart_ofParts
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (nodes : ACUIh.NormalForm (Const ⊕ Var) Hom)
    (edges : Finset (List Hom × Alien)) :
    (ofParts nodes edges).nodePart = nodes := by
  ext ⟨path, atom⟩
  rw [mem_nodePart]
  cases atom <;> simp [ofParts, Atom.ofOrdinary]

@[simp]
theorem edgePart_ofParts
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (nodes : ACUIh.NormalForm (Const ⊕ Var) Hom)
    (edges : Finset (List Hom × Alien)) :
    (ofParts nodes edges).edgePart = edges := by
  ext ⟨path, target⟩
  rw [mem_edgePart]
  simp only [ofParts, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨⟨sourcePath, atom⟩, _membership, equality⟩ |
      ⟨⟨sourcePath, sourceTarget⟩, membership, equality⟩)
    · cases atom <;> cases equality
    · cases equality
      exact membership
  · intro membership
    exact Or.inr ⟨(path, target), membership, rfl⟩

/-- Reassembling the extracted parts recovers the original fragment. -/
@[simp]
theorem ofParts_nodePart_edgePart
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (fragment : Fragment Const Var Hom Alien) :
    ofParts fragment.nodePart fragment.edgePart = fragment := by
  apply parts_injective
  · exact nodePart_ofParts _ _
  · exact edgePart_ofParts _ _

end Fragment

namespace TermGraph

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- Embed a pure ACUIh normal form as one node with no edges. -/
def ofNormalForm (form : ACUIh.NormalForm (Const ⊕ Var) Hom) :
    TermGraph Const Var Hom where
  size := 1
  nodes := fun _ => form
  edges := fun _ => ∅
  root := ⟨0, Nat.zero_lt_one⟩

@[simp]
theorem ofNormalForm_root (form : ACUIh.NormalForm (Const ⊕ Var) Hom) :
    (ofNormalForm form).nodes (ofNormalForm form).root = form := rfl

@[simp]
theorem ofNormalForm_edges (form : ACUIh.NormalForm (Const ⊕ Var) Hom)
    (node : (ofNormalForm form).NodeId) :
    (ofNormalForm form).edges node = ∅ := rfl

/-- Distinct pure normal forms remain distinct after embedding. -/
theorem ofNormalForm_injective :
    Function.Injective (ofNormalForm (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro left right equality
  exact congrArg (fun graph : TermGraph Const Var Hom => graph.nodes graph.root) equality

/-- Embed ordered fragments, separating node contents from the `E` edges.
Earlier-node references make every emitted edge acyclic by construction. -/
def ofFragments [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (size : Nat) (fragments : (node : Fin size) → Fragment Const Var Hom (Fin node.val))
    (root : Fin size) : TermGraph Const Var Hom where
  size := size
  nodes := fun node => (fragments node).nodePart
  edges := fun node => (fragments node).edgePart
  root := root

end TermGraph

end ACUIHE.Graph
