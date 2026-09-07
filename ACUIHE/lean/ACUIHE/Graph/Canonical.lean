import ACUIHE.Graph.NormalForm

/-! Canonicalization of ACUIhE term graphs. -/

namespace ACUIHE.Graph.TermGraph

universe u v w

/-- Canonicalize a graph by reifying its root and normalizing the result. -/
def canonicalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) : TermGraph Const Var Hom :=
  normalize (reify graph)

/-- A term graph is canonical when reification and normalization preserve it. -/
def IsCanonical
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) : Prop :=
  canonicalize graph = graph

/-- Canonicalization always returns a graph produced by normalization. -/
theorem canonicalize_mem_range
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) :
    canonicalize graph ∈ Set.range
      (normalize : ACUIHE.Term Const Var Hom → TermGraph Const Var Hom) := by
  exact ⟨reify graph, rfl⟩

/-- Graphs produced by term normalization are fixed by canonicalization. -/
@[simp]
theorem canonicalize_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (term : ACUIHE.Term Const Var Hom) :
    canonicalize (normalize term) = normalize term := by
  unfold canonicalize
  apply normalize_eq_of_solver_normalize_eq
  exact normalize_reify_normalize term

/-- Canonicalizing a term graph twice makes no further change. -/
@[simp]
theorem canonicalize_idempotent
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) :
    canonicalize (canonicalize graph) = canonicalize graph := by
  exact canonicalize_normalize (reify graph)

/-- Canonicalization always returns a canonical graph. -/
@[simp]
theorem isCanonical_canonicalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) : IsCanonical (canonicalize graph) := by
  exact canonicalize_idempotent graph

end ACUIHE.Graph.TermGraph
