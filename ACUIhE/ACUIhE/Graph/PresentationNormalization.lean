import ACUIhE.Graph.Layers

/-!
# Executable enumerations of normalized terms

An unordered graph does not select a raw enumeration. This module retains an
input-derived enumeration while removing duplicate canonical summands. Its
graph is proved equal to `Graph.normalize`; no second semantic normal form or
ordering assumption on labels is introduced.
-/

namespace ACUIhE.Graph

universe u v w x

namespace Enumeration

variable {α : Type u} {Key : Type v} [DecidableEq Key]

/-- Retain one representative of each key, in input-derived order. -/
def dedupOn (key : α → Key) : List α → List α
  | [] => []
  | a :: rest => if key a ∈ rest.map key then dedupOn key rest else a :: dedupOn key rest

@[simp] theorem map_dedupOn (key : α → Key) (xs : List α) :
    (dedupOn key xs).map key = (xs.map key).dedup := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [dedupOn, List.map_cons, List.dedup_cons]; split_ifs <;> simp [ih]

theorem dedupOn_subset (key : α → Key) (xs : List α) : dedupOn key xs ⊆ xs := by
  induction xs with
  | nil => exact List.Subset.refl _
  | cons a rest ih =>
    simp only [dedupOn]
    split_ifs
    · intro b hb; exact List.mem_cons_of_mem a (ih hb)
    · exact List.cons_subset_cons _ ih

theorem exists_same_key (key : α → Key) (xs : List α) {a : α} (ha : a ∈ xs) :
    ∃ b ∈ dedupOn key xs, key b = key a := by
  have member : key a ∈ (dedupOn key xs).map key := by
    rw [map_dedupOn, List.mem_dedup]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  exact List.mem_map.mp member

theorem forall_dedupOn (key : α → Key) (xs : List α) (P : α → Prop)
    (invariant : ∀ a b, key a = key b → (P a ↔ P b)) :
    (∀ a ∈ dedupOn key xs, P a) ↔ ∀ a ∈ xs, P a := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, same⟩ := exists_same_key key xs ha
    exact (invariant b a same).mp (h b hb)
  · intro h a ha
    exact h a (dedupOn_subset key xs ha)

end Enumeration

namespace Presentation

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Compare summands using canonical children, not child-list syntax. -/
def trim (xs : Forest Const Var Hom) : Forest Const Var Hom :=
  Enumeration.dedupOn Tree.toSummand xs

@[simp] theorem toLayer_trim (xs : Forest Const Var Hom) : toLayer (trim xs) = toLayer xs := by
  unfold toLayer trim
  rw [Enumeration.map_dedupOn]
  ext s
  simp

@[simp] theorem ofPresentation_trim (xs : Forest Const Var Hom) :
    ofPresentation (trim xs) = ofPresentation xs :=
  layer_injective (toLayer_trim xs)

theorem trim_nodup (xs : Forest Const Var Hom) : ((trim xs).map Tree.toSummand).Nodup := by
  rw [trim, Enumeration.map_dedupOn]
  exact List.nodup_dedup _

/-- Normalize full terms, keeping an executable enumeration at every layer.
`free` removes empty E children; `hom` prefixes words without crossing E. -/
def normalizeTerm : Term Const Var Hom → Forest Const Var Hom
  | .zero => []
  | .const c => [.atom [] (.const c)]
  | .var v => [.atom [] (.var v)]
  | .add a b => trim (normalizeTerm a ++ normalizeTerm b)
  | .hom h a => hom h (normalizeTerm a)
  | .free a => free (normalizeTerm a)

/-- The enumeration represents precisely the existing full graph normal form. -/
@[simp] theorem ofPresentation_normalizeTerm (t : Term Const Var Hom) :
    ofPresentation (normalizeTerm t) = Graph.normalize t := by
  induction t with
  | zero | const | var => rfl
  | add a b ia ib => simp only [normalizeTerm, ofPresentation_trim, ofPresentation_append,
      ia, ib, Graph.normalize_add]
  | hom h a ih => simpa only [normalizeTerm, ← hom_ofPresentation, ih] using
      (Graph.normalize_hom h a).symm
  | free a ih => simpa only [normalizeTerm, ← free_ofPresentation, ih] using
      (Graph.normalize_free a).symm

/-- Reuse graph normalization semantics, including arbitrary variable interpretations. -/
@[simp] theorem eval_normalizeTerm {α : Type x} [ACUIhE Hom α]
    (ic : Const → α) (iv : Var → α) (t : Term Const Var Hom) :
    Graph.eval ic iv (ofPresentation (normalizeTerm t)) = t.eval ic iv := by
  rw [ofPresentation_normalizeTerm, Graph.eval_normalize]

end Presentation
end ACUIhE.Graph
