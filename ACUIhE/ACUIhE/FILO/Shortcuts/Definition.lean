import ACUIhE.FILO.Shortcuts.Support
import ACUIhE.FILO.Shortcuts.Saturation
import Mathlib.Data.Finset.Powerset

/-! # Shortcuts and the exact resolving relation (§4.7, Definitions 2–3) -/

namespace ACUIhE.FILO.Shortcuts

open Components

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

abbrev Node (Var : Type v) (Hom : Type w) := Finset (Atom Var Hom)

def atoms (s : System Var Hom) : List (Atom Var Hom) :=
  .const () :: s.names.map (.var ·)

/-- Additive orientation: every present required atom has a present provider. -/
def Flat (s : System Var Hom) (node : Node Var Hom) : Prop :=
  ∀ q ∈ s.flat, ∀ a ∈ q.left, a ∈ node → ∃ b ∈ q.right, b ∈ node

instance (s : System Var Hom) (node : Node Var Hom) : Decidable (Flat s node) :=
  inferInstanceAs (Decidable (∀ q ∈ s.flat, ∀ a ∈ q.left,
    a ∈ node → ∃ b ∈ q.right, b ∈ node))

def Allowed (s : System Var Hom) (node : Node Var Hom) : Prop :=
  ∀ x ∈ s.names, match x with
    | .role r _ => .var x ∈ node → r ∈ s.roles
    | _ => True

instance (s : System Var Hom) (node : Node Var Hom) : Decidable (Allowed s node) := by
  letI : DecidablePred (fun x : Variable Var Hom => match x with
    | .role r _ => .var x ∈ node → r ∈ s.roles
    | _ => True) := fun x => by cases x <;> infer_instance
  unfold Allowed
  infer_instance

def Constants (s : System Var Hom) (initial : Bool) (node : Node Var Hom) : Prop :=
  (.const () ∈ node ↔ initial = true) ∧
  ∀ x ∈ s.names, match x with
    | .constant p => (.var x ∈ node ↔ initial = true ∧ .var p ∈ node)
    | _ => True

instance (s : System Var Hom) (initial : Bool) (node : Node Var Hom) :
    Decidable (Constants s initial node) := by
  letI : DecidablePred (fun x : Variable Var Hom => match x with
      | .constant p => (.var x ∈ node ↔ initial = true ∧ .var p ∈ node)
      | _ => True) := fun x => by cases x <;> infer_instance
  unfold Constants
  infer_instance

def Local (s : System Var Hom) (initial : Bool) (node : Node Var Hom) : Prop :=
  node ⊆ (atoms s).toFinset ∧ Flat s node ∧ Allowed s node ∧ Constants s initial node

instance (s : System Var Hom) (initial : Bool) (node : Node Var Hom) :
    Decidable (Local s initial node) :=
  inferInstanceAs (Decidable (node ⊆ (atoms s).toFinset ∧ Flat s node ∧
    Allowed s node ∧ Constants s initial node))

def Needs (s : System Var Hom) (node : Node Var Hom) (r : Hom) : Prop :=
  ∃ x ∈ s.names, match x with
    | .role t _ => t = r ∧ .var x ∈ node
    | _ => False

instance (s : System Var Hom) (node : Node Var Hom) (r : Hom) :
    Decidable (Needs s node r) := by
  letI : DecidablePred (fun x : Variable Var Hom => match x with
    | .role t _ => t = r ∧ .var x ∈ node
    | _ => False) := fun x => by cases x <;> infer_instance
  unfold Needs
  infer_instance

/-- Both the increasing and the decreasing direction, for every defined child. -/
def Resolves (s : System Var Hom) (source : Node Var Hom) (r : Hom)
    (target : Node Var Hom) : Prop :=
  ∀ x ∈ s.names, match x with
    | .role t p => t = r → (.var x ∈ source ↔ .var p ∈ target)
    | _ => True

instance (s : System Var Hom) (source : Node Var Hom) (r : Hom) (target : Node Var Hom) :
    Decidable (Resolves s source r target) := by
  letI : DecidablePred (fun x : Variable Var Hom => match x with
    | .role t p => t = r → (.var x ∈ source ↔ .var p ∈ target)
    | _ => True) := fun x => by cases x <;> infer_instance
  unfold Resolves
  infer_instance

def candidates (s : System Var Hom) (initial : Bool) : Finset (Node Var Hom) :=
  (atoms s).toFinset.powerset.filter (Local s initial)

@[simp] theorem mem_candidates (s : System Var Hom) (initial : Bool) (node : Node Var Hom) :
    node ∈ candidates s initial ↔ Local s initial node := by
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

def rules (s : System Var Hom) : Saturation.Rules (Node Var Hom) Hom :=
  ⟨candidates s false, s.roles, Needs s, Resolves s⟩

instance (s : System Var Hom) (node : Node Var Hom) (r : Hom) :
    Decidable ((rules s).needs node r) := inferInstanceAs (Decidable (Needs s node r))

instance (s : System Var Hom) (source : Node Var Hom) (r : Hom) (target : Node Var Hom) :
    Decidable ((rules s).resolves source r target) :=
  inferInstanceAs (Decidable (Resolves s source r target))

omit [DecidableEq Var] [DecidableEq Hom] in
theorem flat_empty (s : System Var Hom) : Flat s ∅ := by
  intro q hq a ha h
  exact False.elim (Finset.notMem_empty _ h)

theorem local_empty (s : System Var Hom) : Local s false ∅ := by
  refine ⟨Finset.empty_subset _, flat_empty s, ?_, ?_⟩
  · intro x _; cases x <;> simp
  · refine ⟨by simp, ?_⟩
    intro x _; cases x <;> simp

theorem needs_of_member (s : System Var Hom) {node : Node Var Hom} {r : Hom}
    {x : Variable Var Hom} (hx : .role r x ∈ s.names) (h : .var (.role r x) ∈ node) :
    Needs s node r := ⟨.role r x, hx, rfl, h⟩

end ACUIhE.FILO.Shortcuts
