import ACUIhE.Equation
import ACUIhE.Graph.Graph

/-! # Full-signature equations and ordinary unification -/

namespace ACUIhE

universe u v w x y
variable {Const : Type u} {Var : Type v} {Hom : Type w} {Target : Type x}

deriving instance DecidableEq for Term

/-- Ordinary simultaneous substitution, preserving both unary operators. -/
def Term.substitute (σ : Var → Term Const Target Hom) : Term Const Var Hom → Term Const Target Hom
  | .zero => .zero
  | .const c => .const c
  | .var v => σ v
  | .add a b => .add (a.substitute σ) (b.substitute σ)
  | .hom h a => .hom h (a.substitute σ)
  | .free a => .free (a.substitute σ)

@[simp] theorem Term.eval_substitute {α : Type y} [ACUIhE Hom α]
    (σ : Var → Term Const Target Hom) (ic : Const → α) (iv : Target → α)
    (t : Term Const Var Hom) :
    (t.substitute σ).eval ic iv = t.eval ic (fun v => (σ v).eval ic iv) := by
  induction t <;> simp_all [substitute, eval]

namespace Solver

abbrev Problem (Const : Type u) (Var : Type v) (Hom : Type w) := List (Equation Const Var Hom)

namespace Problem

def Holds {α : Type y} [ACUIhE Hom α] (p : Problem Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Prop := ∀ q ∈ p, q.Holds ic iv

def IsUnifier (p : Problem Const Var Hom) (σ : Var → Term Const Target Hom) : Prop :=
  ∀ q ∈ p, (q.left.substitute σ).Equal (q.right.substitute σ)

/-- Unifiability is defined using ordinary substitutions and equality in the
whole theory, independently of graph matching or any solver result. -/
def Unifiable (p : Problem Const Var Hom) : Prop :=
  ∃ σ : Var → Term Const Var Hom, p.IsUnifier σ

def IsSolution (p : Problem Const Var Hom) (σ : Var → Graph Const Empty Hom) : Prop :=
  p.Holds Graph.constant σ

theorem solution_of_unifier (p : Problem Const Var Hom) (σ : Var → Term Const Target Hom)
    (h : p.IsUnifier σ) :
    p.IsSolution (fun v => (σ v).eval Graph.constant (fun _ => (0 : Graph Const Empty Hom))) := by
  intro q hq
  simpa only [Term.eval_substitute, Equation.Holds, Generic.Equation.Holds] using
    (Term.Equal.sound Graph.constant (fun _ => (0 : Graph Const Empty Hom)) (h q hq))

theorem eval_graph {α : Type y} [ACUIhE Hom α] (ic : Const → α)
    (σ : Var → Graph Const Empty Hom) (t : Term Const Var Hom) :
    Graph.eval ic Empty.elim (t.eval Graph.constant σ) =
      t.eval ic (fun v => Graph.eval ic Empty.elim (σ v)) := by
  induction t with
  | zero | var => rfl
  | const c => exact ACUIhE.add_zero _
  | add a b ia ib => simp only [Term.eval, Graph.eval_add, ia, ib]
  | hom h t ih =>
    change Graph.eval ic Empty.elim (Graph.hom h (t.eval Graph.constant σ)) =
      H h (t.eval ic (fun v => Graph.eval ic Empty.elim (σ v)))
    rw [Graph.eval_hom, ih]
  | free t ih =>
    change Graph.eval ic Empty.elim (Graph.free (t.eval Graph.constant σ)) =
      E (Hom := Hom) (t.eval ic (fun v => Graph.eval ic Empty.elim (σ v)))
    rw [Graph.eval_free, ih]

theorem unifiable_of_solution (p : Problem Const Var Hom) (σ : Var → Graph Const Empty Hom)
    (h : p.IsSolution σ) : p.Unifiable := by
  classical
  let τ : Var → Term Const Var Hom := fun v => (Graph.reify (σ v)).substitute Empty.elim
  refine ⟨τ, ?_⟩
  intro q hq α _ ic iv
  have evaluation (v : Var) : (τ v).eval ic iv = Graph.eval ic Empty.elim (σ v) := by
    simp only [τ, Term.eval_substitute]
    have same : (fun v : Empty => (Empty.elim v : Term Const Var Hom).eval ic iv) = Empty.elim :=
      funext (fun v => Empty.elim v)
    rw [same, Graph.eval_reify]
  simp only [Term.eval_substitute, evaluation]
  rw [← eval_graph ic σ q.left, ← eval_graph ic σ q.right]
  exact congrArg (Graph.eval ic Empty.elim) (h q hq)

theorem unifiable_iff_graph (p : Problem Const Var Hom) :
    p.Unifiable ↔ ∃ σ : Var → Graph Const Empty Hom, p.IsSolution σ := by
  constructor
  · rintro ⟨σ, h⟩
    exact ⟨_, p.solution_of_unifier σ h⟩
  · rintro ⟨σ, h⟩
    exact p.unifiable_of_solution σ h

end Problem

def fromInequalities (qs : List (Inequality Const Var Hom)) : Problem Const Var Hom :=
  qs.map Inequality.toEquation

theorem holds_fromInequalities_iff {α : Type y} [ACUIhE Hom α]
    (qs : List (Inequality Const Var Hom)) (ic : Const → α) (iv : Var → α) :
    (fromInequalities qs).Holds ic iv ↔ ∀ q ∈ qs, q.Holds ic iv := by
  simp only [fromInequalities, Problem.Holds, List.forall_mem_map, Inequality.holds_toEquation]

end Solver
end ACUIhE
