import ACUIhE.ACUIESolver.Branching.Layer

/-!
# Exhaustive ACUIE constructor branching

Constructor summands denote zero or one canonical atom; variables may denote
arbitrarily many. Matching therefore branches over constructors and retains
variable-containment equations. It does not distribute E, cancel sums, or
apply an ordinary occurs-check rejection.
-/

namespace ACUIhE.ACUIESolver.Branching

universe u v w

variable {Const : Type u} {Var : Type v} {Target : Type w}

def nodes : ACUIE.Term Const Var → Nat
  | .zero | .const _ | .var _ => 1
  | .add a b => nodes a + nodes b + 1
  | .free a => nodes a + 1

theorem nodes_pos (t : ACUIE.Term Const Var) : 0 < nodes t := by cases t <;> simp [nodes]

def vanish : ACUIE.Term Const Var → Plan Const Var
  | .zero => .accept
  | .const _ => .reject
  | .var v => .equation ⟨.var v, .zero⟩
  | .add a b => .both (vanish a) (vanish b)
  | .free a => vanish a

variable [DecidableEq Const]

def locateConstant (c : Const) : ACUIE.Term Const Var → Plan Const Var
  | .zero | .free _ => .reject
  | .const d => if c = d then .accept else .reject
  | .var v => .equation ⟨.add (.const c) (.var v), .var v⟩
  | .add a b => .either (locateConstant c a) (locateConstant c b)

mutual
  /-- Compile equality by mutual coverage, descending when E heads match. -/
  def compare : ACUIE.Term Const Var → ACUIE.Term Const Var → Plan Const Var
    | .zero, b => vanish b
    | a, .zero => vanish a
    | .var v, b => .equation ⟨.var v, b⟩
    | a, .var v => .equation ⟨a, .var v⟩
    | .const c, .const d => if c = d then .accept else .reject
    | .const _, .free _ | .free _, .const _ => .reject
    | .free a, .free b => compare a b
    | a, b => .both (cover a b) (cover b a)
  termination_by a b => (nodes a + nodes b, 2)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega

  /-- Compile one direction of the additive order. -/
  def cover : ACUIE.Term Const Var → ACUIE.Term Const Var → Plan Const Var
    | .zero, _ => .accept
    | .var v, b => .equation ⟨.add (.var v) b, b⟩
    | .const c, b => locateConstant c b
    | .add a b, c => .both (cover a c) (cover b c)
    | .free a, b => .either (vanish a) (locateFree a b)
  termination_by a b => (nodes a + nodes b, 1)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega

  /-- Locate a nonzero E atom; the caller separately includes its zero case. -/
  def locateFree (a : ACUIE.Term Const Var) : ACUIE.Term Const Var → Plan Const Var
    | .zero | .const _ => .reject
    | .var v => .equation ⟨.add (.free a) (.var v), .var v⟩
    | .add b c => .either (locateFree a b) (locateFree a c)
    | .free b => compare a b
  termination_by b => (nodes a + 1 + nodes b, 0)
  decreasing_by all_goals (try simp only [nodes]); all_goals omega
end

end ACUIhE.ACUIESolver.Branching
