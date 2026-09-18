import Mathlib.Data.Fin.Tuple.Basic

/-!
# Short-circuiting selection from existing branches

This helper retains the residual-branch compatibility interface. The complete
solver itself uses the streaming ordered-group search, not this list interface.
-/

namespace ACUIhE.ACUIESolver.Matching

universe u v
variable {α : Type u} {β : Type v}

def firstSome (values : List α) (f : α → Option β) : Option β :=
  match values with
  | [] => none
  | a :: rest => match f a with
    | some b => some b
    | none => firstSome rest f

theorem firstSome_sound (values : List α) (f : α → Option β) {b : β}
    (h : firstSome values f = some b) : ∃ a ∈ values, f a = some b := by
  induction values with
  | nil => cases h
  | cons a rest ih =>
    cases ha : f a with
    | none =>
      obtain ⟨a', member, eq⟩ := ih (by simpa only [firstSome, ha] using h)
      exact ⟨a', List.mem_cons_of_mem _ member, eq⟩
    | some b' =>
      have eq : b' = b := Option.some.inj (by simpa only [firstSome, ha] using h)
      exact ⟨a, List.mem_cons_self, eq ▸ ha⟩

theorem firstSome_none_iff (values : List α) (f : α → Option β) :
    firstSome values f = none ↔ ∀ a ∈ values, f a = none := by
  induction values with
  | nil => simp [firstSome]
  | cons a rest ih =>
    cases ha : f a <;> simp [firstSome, ha, ih]

end ACUIhE.ACUIESolver.Matching
