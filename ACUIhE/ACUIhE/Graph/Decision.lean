import ACUIhE.Graph.Normalization

/-! # Executable equality of canonical graphs and full ACUIhE terms -/

namespace ACUIhE.Graph

universe u v w

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

namespace Presentation

/-- Finite recursive comparison; children are compared as sets, not lists. -/
def Tree.matches : Tree Const Var Hom → Tree Const Var Hom → Bool
  | .atom word p, .atom word' p' => decide (word = word' ∧ p = p')
  | .edge word first rest, .edge word' first' rest' =>
      decide (word = word') &&
        ((first :: rest).attach.all (fun t => (first' :: rest').any (Tree.matches t.val)) &&
          (first' :: rest').all (fun s =>
            (first :: rest).attach.any (fun t => Tree.matches t.val s)))
  | _, _ => false
termination_by left => sizeOf left
decreasing_by all_goals exact Tree.child_lt word first rest (Subtype.property _)

theorem Tree.matches_eq_true (a b : Tree Const Var Hom) : a.matches b = true ↔ a.Rel b := by
  induction a using (measure (fun t : Tree Const Var Hom => sizeOf t)).wf.induction
    generalizing b
  rename_i a ih
  cases a with
  | atom word p => cases b <;> simp [Tree.matches, Tree.Rel]
  | edge word first rest =>
      cases b with
      | atom => simp [Tree.matches, Tree.Rel]
      | edge word' first' rest' =>
          rw [Tree.matches, Tree.Rel]
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
            List.mem_attach, true_and, Subtype.forall, Subtype.exists, forall_const]
          constructor
          · rintro ⟨hw, hl, hr⟩
            refine ⟨hw, ?_, ?_⟩
            · intro t ht
              obtain ⟨s, hs, hm⟩ := hl t ht
              exact ⟨s, hs, (ih t (Tree.child_lt word first rest ht) s).mp hm⟩
            · intro s hs
              obtain ⟨t, ht, hm⟩ := hr s hs
              exact ⟨t, ht, (ih t (Tree.child_lt word first rest ht) s).mp hm⟩
          · rintro ⟨hw, hl, hr⟩
            refine ⟨hw, ?_, ?_⟩
            · intro t ht
              obtain ⟨s, hs, hm⟩ := hl t ht
              exact ⟨s, hs, (ih t (Tree.child_lt word first rest ht) s).mpr hm⟩
            · intro s hs
              obtain ⟨t, ht, hm⟩ := hr s hs
              exact ⟨t, ht, (ih t (Tree.child_lt word first rest ht) s).mpr hm⟩

def compareForests (xs ys : Forest Const Var Hom) : Bool :=
  xs.all (fun t => ys.any (Tree.matches t)) &&
    ys.all (fun s => xs.any (fun t => Tree.matches t s))

theorem compareForests_eq_true (xs ys : Forest Const Var Hom) :
    compareForests xs ys = true ↔ Rel xs ys := by
  simp [compareForests, Rel, Setwise, List.all_eq_true, List.any_eq_true, Tree.matches_eq_true]

instance decidableRel : DecidableRel (Rel (Const := Const) (Var := Var) (Hom := Hom)) :=
  fun xs ys => decidable_of_iff (compareForests xs ys = true) (compareForests_eq_true xs ys)

end Presentation

/-- Recursive structural equality is decidable using only equality of labels. -/
instance decidableEq : DecidableEq (Graph Const Var Hom) :=
  @Quotient.decidableEq _ _ Presentation.decidableRel

/-- A Boolean equality checker for full ACUIhE terms. -/
def equivalent (a b : Term Const Var Hom) : Bool := decide (normalize a = normalize b)

@[simp] theorem equivalent_eq_true (a b : Term Const Var Hom) :
    equivalent a b = true ↔ Derives a b := by
  simp only [equivalent, decide_eq_true_eq, normalize_eq_iff_derives]

end ACUIhE.Graph

namespace ACUIhE

universe u v w

/-- Full derivability, including E injectivity, is decidable by canonical graphs. -/
instance decidableDerives {Const : Type u} {Var : Type v} {Hom : Type w}
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (a b : Term Const Var Hom) : Decidable (Derives a b) :=
  decidable_of_iff (Graph.normalize a = Graph.normalize b)
    (Graph.normalize_eq_iff_derives a b)

end ACUIhE
