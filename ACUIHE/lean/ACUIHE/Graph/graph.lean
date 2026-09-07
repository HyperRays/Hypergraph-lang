import Mathlib.Data.Finset.Basic

/-!
Finite rooted directed acyclic graphs with arbitrary node and edge labels.
Edges point to earlier nodes.
-/

namespace ACUIHE.Graph

universe u v

/-- A finite labelled DAG. The root may be any node; unused nodes are allowed. -/
structure RootedDAG (NodeLabel : Type u) (EdgeLabel : Type v) where
  size : Nat
  nodes : Fin size → NodeLabel
  edges : (source : Fin size) → Finset (EdgeLabel × Fin source.val)
  root : Fin size

namespace RootedDAG

variable {NodeLabel : Type u} {EdgeLabel : Type v}

/-- A node identifier in this graph. -/
abbrev NodeId (graph : RootedDAG NodeLabel EdgeLabel) := Fin graph.size

/-- An edge present in the graph's edge table. -/
structure Edge (graph : RootedDAG NodeLabel EdgeLabel) where
  source : graph.NodeId
  label : EdgeLabel
  target : Fin source.val
  occurs : (label, target) ∈ graph.edges source

/-- View an earlier-node reference as a graph-wide identifier. -/
def Edge.targetNode {graph : RootedDAG NodeLabel EdgeLabel}
    (edge : graph.Edge) : graph.NodeId :=
  ⟨edge.target.val, Nat.lt_trans edge.target.isLt edge.source.isLt⟩

/-- Node indices strictly decrease along every edge. -/
theorem Edge.target_lt_source {graph : RootedDAG NodeLabel EdgeLabel}
    (edge : graph.Edge) : edge.targetNode.val < edge.source.val :=
  edge.target.isLt

/-- In particular, an edge cannot refer to its own source node. -/
theorem Edge.target_ne_source {graph : RootedDAG NodeLabel EdgeLabel}
    (edge : graph.Edge) : edge.targetNode ≠ edge.source := by
  intro equality
  have indicesEqual := congrArg Fin.val equality
  exact (Nat.ne_of_lt edge.target_lt_source) indicesEqual

end RootedDAG

end ACUIHE.Graph
