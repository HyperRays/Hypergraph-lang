import ACUIhE.Equation
import ACUIhE.ACUIhNF.linear.Semantics

/-!
# Coupled ACUIh layers and E edges

An edge records an equation `root = E(child)`. Variables are shared across all
layers and edges. This is a mathematical presentation of a mixed system, not
an assumption that its layers can be unified independently.
-/

namespace ACUIhE.Solver

universe u v w x

structure Edge (Const : Type u) (Var : Type v) (Hom : Type w) where
  root : Var
  child : ACUIh.Term Const Var Hom

structure Prepared (Const : Type u) (Var : Type v) (Hom : Type w) where
  equations : List (ACUIh.Equation Const Var Hom)
  edges : List (Edge Const Var Hom)

variable {Const : Type u} {Var : Type v} {Hom : Type w} {α : Type x}

/-- A full algebra supplies its ACUIh reduct, without modifying any term. -/
@[instance_reducible] def reduct [ACUIhE Hom α] : ACUIh Hom α where
  hom := ACUIhE.hom
  add_assoc := ACUIhE.add_assoc
  add_comm := ACUIhE.add_comm
  add_zero := ACUIhE.add_zero
  add_idem := ACUIhE.add_idem
  hom_add := ACUIhE.hom_add
  hom_zero := ACUIhE.hom_zero

section Semantics
variable [ACUIhE Hom α]
local instance : ACUIh Hom α := reduct

def Prepared.Holds (p : Prepared Const Var Hom) (ic : Const → α) (iv : Var → α) : Prop :=
  (∀ q ∈ p.equations, q.Holds ic iv) ∧
  ∀ edge ∈ p.edges, iv edge.root = E (Hom := Hom) (edge.child.eval ic iv)

end Semantics

/-- Solvability of the coupled presentation in the ground free algebra. -/
def Prepared.Unifiable (p : Prepared Const Var Hom) : Prop :=
  ∃ iv : Var → Graph Const Empty Hom, p.Holds Graph.constant iv

/-- Add a namespace of formal E names; every homomorphism is retained. -/
def lift {n : Nat} : ACUIh.Term Const Var Hom → ACUIh.Term (Const ⊕ Fin n) Var Hom
  | .zero => .zero
  | .const c => .const (.inl c)
  | .var v => .var v
  | .add a b => .add (lift a) (lift b)
  | .hom h a => .hom h (lift a)

theorem eval_lift {n : Nat} [ACUIh Hom α] (ic : Const ⊕ Fin n → α) (iv : Var → α)
    (t : ACUIh.Term Const Var Hom) :
    (lift t).eval ic iv = t.eval (fun c => ic (.inl c)) iv := by
  induction t <;> simp_all [lift, ACUIh.Term.eval]

end ACUIhE.Solver
