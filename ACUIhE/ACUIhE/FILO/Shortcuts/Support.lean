import ACUIhE.FILO.Preprocessing.Signature

/-!
# The finite component interface

Every component mentioned in a goal brings its ancestors into the finite
signature. Local derivative and constant-part equations on this signature
are proved to give exactly `Components.interpret`, not a weaker semantics.
-/

namespace ACUIhE.FILO.Components

open ACUIh.Linear

universe v w

variable {Var : Type v} {Hom : Type w}

def Variable.ancestors : Variable Var Hom → List (Variable Var Hom)
  | .base v => [.base v]
  | .role r x => .role r x :: x.ancestors
  | .constant x => .constant x :: x.ancestors

@[simp] theorem Variable.mem_ancestors_self (x : Variable Var Hom) : x ∈ x.ancestors := by
  cases x <;> simp [ancestors]

theorem Variable.ancestors_trans {x y z : Variable Var Hom}
    (hy : y ∈ x.ancestors) (hz : z ∈ y.ancestors) : z ∈ x.ancestors := by
  induction x with
  | base v =>
    have e : y = .base v := List.mem_singleton.mp hy
    subst y
    exact hz
  | role r x ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hz
    · exact List.mem_cons_of_mem _ (ih hy)
  | constant x ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hz
    · exact List.mem_cons_of_mem _ (ih hy)

def Atom.variables : Atom Var Hom → List (Variable Var Hom)
  | .const _ => []
  | .var x => x.ancestors

def System.names [DecidableEq Var] [DecidableEq Hom] (s : System Var Hom) :
    List (Variable Var Hom) :=
  (s.flat.flatMap fun q => (q.left ++ q.right).flatMap Atom.variables).dedup

variable [DecidableEq Var] [DecidableEq Hom]

theorem System.names_ancestors (s : System Var Hom) {x y : Variable Var Hom}
    (hx : x ∈ s.names) (hy : y ∈ x.ancestors) : y ∈ s.names := by
  simp only [names, List.mem_dedup, List.mem_flatMap] at hx ⊢
  obtain ⟨q, hq, a, ha, hx⟩ := hx
  refine ⟨q, hq, a, ha, ?_⟩
  cases a with
  | const c => exact False.elim (List.not_mem_nil hx)
  | var z => exact Variable.ancestors_trans hx hy

theorem System.parent_role (s : System Var Hom) {r : Hom} {x : Variable Var Hom}
    (hx : .role r x ∈ s.names) : x ∈ s.names :=
  s.names_ancestors hx (List.mem_cons_of_mem _ x.mem_ancestors_self)

theorem System.parent_constant (s : System Var Hom) {x : Variable Var Hom}
    (hx : .constant x ∈ s.names) : x ∈ s.names :=
  s.names_ancestors hx (List.mem_cons_of_mem _ x.mem_ancestors_self)

theorem System.name_of_mem (s : System Var Hom) {q : Generic.Inequality (Expression Var Hom)}
    (hq : q ∈ s.flat) {x : Variable Var Hom} (hx : .var x ∈ q.left ++ q.right) : x ∈ s.names := by
  simp only [names, List.mem_dedup, List.mem_flatMap]
  exact ⟨q, hq, .var x, hx, x.mem_ancestors_self⟩

abbrev Assignment (Var : Type v) (Hom : Type w) := Variable Var Hom → WordPolynomial Hom

/-- The exact component equations, with no relation postulated for base names. -/
def System.Coherent (s : System Var Hom) (a : Assignment Var Hom) : Prop :=
  ∀ x ∈ s.names, match x with
    | .base _ => True
    | .role r p => a x = Language.derivative r (a p)
    | .constant p => a x = Language.constantPart (a p)

/-- Ancestor closure discharges the semantic bridge for every local assignment. -/
theorem System.coherent_interpret (s : System Var Hom) (a : Assignment Var Hom)
    (h : s.Coherent a) {x : Variable Var Hom} (hx : x ∈ s.names) :
    a x = interpret (fun v => a (.base v)) x := by
  induction x with
  | base v => rfl
  | role r x ih =>
    change a (.role r x) = Language.derivative r _
    rw [h _ hx, ih (s.parent_role hx)]
  | constant x ih =>
    change a (.constant x) = Language.constantPart _
    rw [h _ hx, ih (s.parent_constant hx)]

theorem System.interpret_coherent (s : System Var Hom) (iv : Column Var Hom) :
    s.Coherent (interpret iv) := by
  intro x _
  cases x <;> trivial

end ACUIhE.FILO.Components
