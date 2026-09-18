import ACUIhE.Solver
import ACUIhE.Graph.Layers

/-!
# Native ACUIhE API, ABI version 1

Labels are nonnegative machine-sized symbol IDs. Constants, variables, and
homomorphisms have separate namespaces. All exported object arguments are
owned (consumed); returned objects carry one owned reference. C clients use
only these exports and the standard Lean runtime representations of Array,
Prod, Option, List/Finset, Sum, and Nat. Terms, graphs, and substitutions are
otherwise opaque.

This adapter specializes the verified solver; it does not replace its search
or assume any additional algebraic laws. The OCaml/C ownership adapter is
outside Lean's proof boundary.
-/

namespace HypergraphFFI
open ACUIhE

abbrev T := Term Nat Nat Nat
abbrev G := Graph Nat Nat Nat
abbrev Solution := Nat → Graph Nat Empty Nat
abbrev Equations := Array (T × T)

def problem (equations : Equations) : Solver.Problem Nat Nat Nat :=
  equations.toList.map fun (left, right) => ⟨left, right⟩

@[export acuihe_v1_abi_version]
def abiVersion (_ : Unit) : UInt32 := 1

@[export acuihe_v1_zero]
def zero (_ : Unit) : T := .zero

@[export acuihe_v1_constant]
def constant (name : USize) : T := .const name.toNat

@[export acuihe_v1_variable]
def variableTerm (name : USize) : T := .var name.toNat

@[export acuihe_v1_add]
def add (left right : T) : T := .add left right

@[export acuihe_v1_hom]
def hom (name : USize) (body : T) : T := .hom name.toNat body

@[export acuihe_v1_free]
def free (body : T) : T := .free body

@[export acuihe_v1_equal]
def equal (left right : T) : Bool := Graph.equivalent left right

@[export acuihe_v1_below]
def below (left right : T) : Bool := Graph.equivalent (.add left right) right

@[export acuihe_v1_normalize]
def normalize (term : T) : G := Graph.normalize term

@[export acuihe_v1_graph_equal]
def graphEqual (left right : G) : Bool := decide (left = right)

@[export acuihe_v1_graph_below]
def graphBelow (left right : G) : Bool := decide (left + right = right)

/-- An unordered layer of (outermost-first homomorphism word, atom) entries.
    A Finset has an erased List representation at the native boundary. The C
    adapter copies that enumeration; callers must not depend on its order.
    Sum.inl holds a constant/variable Particle; Sum.inr holds a nonzero E child
    (whose proof field is erased). No raw Graph presentation is inspected. -/
@[export acuihe_v1_graph_layer]
def graphLayer (graph : G) : Graph.Layer Nat Nat Nat := graph.layer

@[export acuihe_v1_is_unifiable]
def isUnifiable (equations : Equations) : Bool := Solver.isUnifiable (problem equations)

@[export acuihe_v1_solve]
def solve (equations : Equations) : Option Solution := Solver.solve (problem equations)

/-- Embed a ground answer into the same graph type used by normalization.
    This preserves the canonical value and introduces no variables. -/
@[export acuihe_v1_solution_get]
def solutionGet (solution : Solution) (name : USize) : G :=
  Graph.eval Graph.constant Empty.elim (solution name.toNat)

theorem solve_sound (equations : Equations) {solution : Solution}
    (found : solve equations = some solution) : (problem equations).IsSolution solution :=
  Solver.solve_sound (problem equations) found

theorem solve_none_iff (equations : Equations) :
    solve equations = none ↔ ¬ (problem equations).Unifiable :=
  Solver.solve_none_iff (problem equations)

theorem isUnifiable_iff (equations : Equations) :
    isUnifiable equations = true ↔ (problem equations).Unifiable :=
  Solver.isUnifiable_iff (problem equations)

end HypergraphFFI
