import ACUIhE.FILO.Shortcuts.Definition

/-! # Executable finite subset enumeration for good-variable shortcut generation -/

namespace ACUIhE.FILO.Shortcuts

open Components

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

/-- Ordered enumeration, without a noncomputable finset-to-list conversion. -/
def subsets : List (Atom Var Hom) → List (Node Var Hom)
  | [] => [∅]
  | a :: rest => let tail := subsets rest; tail ++ tail.map (insert a)

theorem mem_subsets (names : List (Atom Var Hom)) (node : Node Var Hom) :
    node ∈ subsets names ↔ node ⊆ names.toFinset := by
  induction names generalizing node with
  | nil => simp [subsets]
  | cons a rest ih =>
    simp only [subsets, List.mem_append, List.mem_map, ih, List.toFinset_cons]
    constructor
    · rintro (h | ⟨t, ht, rfl⟩)
      · exact Finset.Subset.trans h (Finset.subset_insert _ _)
      · exact Finset.insert_subset_insert a ht
    · intro h
      by_cases present : a ∈ node
      · right
        refine ⟨node.erase a, ?_, Finset.insert_erase present⟩
        intro b hb
        have hb' := Finset.mem_erase.mp hb
        exact (Finset.mem_insert.mp (h hb'.2)).resolve_left hb'.1
      · left
        intro b hb
        rcases Finset.mem_insert.mp (h hb) with rfl | hb'
        · exact False.elim (present hb)
        · exact hb'

end ACUIhE.FILO.Shortcuts
