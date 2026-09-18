import ACUIhE.FILO.Choices.Basic

/-! # Single-particle requirements of a generic goal -/

namespace ACUIhE.FILO.Goal

open Components ACUIh.Linear

universe v w

structure Requirement (Var : Type v) (Hom : Type w) where
  required : Atom Var Hom
  available : Expression Var Hom
  deriving DecidableEq

variable {Var : Type v} {Hom : Type w}

def requirements (g : Components.Goal Var Hom) : List (Requirement Var Hom) :=
  g.flatMap fun q => q.left.map (fun a => ⟨a, q.right⟩)

def Requirement.Present (q : Requirement Var Hom) (member : Atom Var Hom → Prop) : Prop :=
  member q.required → ∃ a ∈ q.available, member a

def Requirement.Holds [DecidableEq Hom] (q : Requirement Var Hom) (iv : Column Var Hom) : Prop :=
  ∀ word, q.Present (fun a => word ∈ (atomValue iv a).words)

theorem holds_requirements [DecidableEq Hom] (g : Components.Goal Var Hom) (iv : Column Var Hom) :
    Components.Holds g iv ↔ ∀ q ∈ requirements g, q.Holds iv := by
  simp only [Components.Holds, inequality_iff, requirements, List.forall_mem_flatMap,
    List.forall_mem_map, Requirement.Holds, Requirement.Present]
  constructor
  · intro h q hq a ha word hw
    exact (mem_value _ _ _).mp (h q hq ((mem_value _ _ _).mpr ⟨a, ha, hw⟩))
  · intro h q hq word hw
    obtain ⟨a, ha, hw⟩ := (mem_value _ _ _).mp hw
    exact (mem_value _ _ _).mpr (h q hq a ha word hw)

variable [DecidableEq Var] [DecidableEq Hom]

theorem requirement_names (s : System Var Hom) {q : Requirement Var Hom}
    (hq : q ∈ requirements s.flat) {x : Variable Var Hom}
    (hx : .var x = q.required ∨ .var x ∈ q.available) : x ∈ s.names := by
  obtain ⟨e, he, hm⟩ := List.mem_flatMap.mp hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  apply s.name_of_mem he
  rcases hx with hx | hx
  · exact List.mem_append_left _ (hx.symm ▸ ha)
  · exact List.mem_append_right _ hx

end ACUIhE.FILO.Goal
