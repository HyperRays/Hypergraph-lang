import ACUIhE.Graph.Structure

/-! # Reification and interpretation of canonical graphs -/

namespace ACUIhE.Graph

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

namespace Presentation

/-- Outermost-first application of a word, without moving it across E. -/
def applyWord : List Hom → Term Const Var Hom → Term Const Var Hom
  | [], term => term
  | name :: word, term => .hom name (applyWord word term)

mutual
  /-- Reify one presented summand, recursively reifying its E child. -/
  def Tree.reify : Tree Const Var Hom → Term Const Var Hom
    | .atom word (.const c) => applyWord word (.const c)
    | .atom word (.var v) => applyWord word (.var v)
    | .edge word first rest =>
        applyWord word (.free (.add first.reify (reify rest)))

  /-- Executable reification in the supplied order, at every layer. -/
  def reify : Forest Const Var Hom → Term Const Var Hom
    | [] => .zero
    | first :: rest => .add first.reify (reify rest)
end

section Interpretation

variable {α : Type x} [ACUIhE Hom α]

local instance : Std.Commutative (fun a b : α => a + b) :=
  ⟨ACUIhE.add_comm (Hom := Hom)⟩
local instance : Std.Associative (fun a b : α => a + b) :=
  ⟨ACUIhE.add_assoc (Hom := Hom)⟩
local instance : Std.IdempotentOp (fun a b : α => a + b) :=
  ⟨ACUIhE.add_idem (Hom := Hom)⟩

private theorem sum_eq_fold {β : Type*} [DecidableEq α] (f : β → α) (xs : List β) :
    xs.foldr (fun t a => f t + a) 0 =
      (xs.map f).toFinset.fold (fun a b : α => a + b) 0 id := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.toFinset_cons,
        Finset.fold_insert_idem, id_eq, ih]

private theorem sum_eq_of_setwise {β : Type*} {r : β → β → Prop}
    (f : β → α) {xs ys : List β} (h : Setwise r xs ys)
    (he : ∀ t ∈ xs, ∀ s ∈ ys, r t s → f t = f s) :
    xs.foldr (fun t a => f t + a) 0 = ys.foldr (fun t a => f t + a) 0 := by
  classical
  rw [sum_eq_fold (Hom := Hom), sum_eq_fold (Hom := Hom)]
  congr 1
  ext a
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hr⟩ := h.1 t ht
    exact ⟨s, hs, (he t ht s hs hr).symm⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hr⟩ := h.2 s hs
    exact ⟨t, ht, he t ht s hs hr⟩

variable (ic : Const → α) (iv : Var → α)

theorem eval_applyWord_congr (word : List Hom) {a b : Term Const Var Hom}
    (h : a.eval ic iv = b.eval ic iv) :
    (applyWord word a).eval ic iv = (applyWord word b).eval ic iv := by
  induction word with
  | nil => exact h
  | cons name word ih => exact congrArg (H name) ih

theorem eval_reify (xs : Forest Const Var Hom) :
    (reify xs).eval ic iv =
      xs.foldr (fun t a => t.reify.eval ic iv + a) 0 := by
  induction xs with
  | nil => rfl
  | cons t xs ih => simpa only [reify, Term.eval, List.foldr_cons] using congrArg (_ + ·) ih

/-- Structural summand equality preserves interpretation in every full model. -/
theorem Tree.eval_eq_of_rel {a b : Tree Const Var Hom} (h : a.Rel b) :
    a.reify.eval ic iv = b.reify.eval ic iv := by
  induction a using (measure (fun t : Tree Const Var Hom => sizeOf t)).wf.induction
    generalizing b
  rename_i a ih
  cases a with
  | atom word p =>
      cases b with
      | atom word' p' =>
          obtain ⟨rfl, rfl⟩ := (Tree.Rel.eq_1 _ _ _ _).mp h
          rfl
      | edge => simp only [Tree.Rel] at h
  | edge word first rest =>
      cases b with
      | atom => simp only [Tree.Rel] at h
      | edge word' first' rest' =>
          rw [Tree.Rel] at h
          obtain ⟨rfl, h⟩ := h
          apply eval_applyWord_congr
          change E (Hom := Hom) ((Presentation.reify (first :: rest)).eval ic iv) =
            E (Hom := Hom) ((Presentation.reify (first' :: rest')).eval ic iv)
          apply congrArg E
          rw [eval_reify, eval_reify]
          exact sum_eq_of_setwise (Hom := Hom) _ h
            (fun t ht s _ r => ih t (Tree.child_lt word first rest ht) r)

/-- Structural forest equality preserves interpretation, including duplicate summands. -/
theorem eval_eq_of_rel {xs ys : Forest Const Var Hom} (h : Rel xs ys) :
    (reify xs).eval ic iv = (reify ys).eval ic iv := by
  rw [eval_reify, eval_reify]
  exact sum_eq_of_setwise (Hom := Hom) _ h (fun _ _ _ _ r => Tree.eval_eq_of_rel ic iv r)

@[simp] theorem eval_reify_append (xs ys : Forest Const Var Hom) :
    (reify (xs ++ ys)).eval ic iv = (reify xs).eval ic iv + (reify ys).eval ic iv := by
  induction xs with
  | nil => exact ((ACUIhE.add_comm _ _).trans (ACUIhE.add_zero _)).symm
  | cons t xs ih =>
      simp only [List.cons_append, reify, Term.eval, ih]
      exact (ACUIhE.add_assoc _ _ _).symm

theorem Tree.eval_prepend (name : Hom) (t : Tree Const Var Hom) :
    (t.prepend name).reify.eval ic iv = H name (t.reify.eval ic iv) := by
  cases t with
  | atom word p => cases p <;> rfl
  | edge => rfl

@[simp] theorem eval_reify_hom (name : Hom) (xs : Forest Const Var Hom) :
    (reify (hom name xs)).eval ic iv = H name ((reify xs).eval ic iv) := by
  induction xs with
  | nil => exact (ACUIhE.hom_zero name).symm
  | cons t xs ih =>
      simp only [hom, List.map_cons, reify, Term.eval, Tree.eval_prepend]
      rw [show (reify (xs.map (Tree.prepend name))).eval ic iv =
        H name ((reify xs).eval ic iv) from ih]
      exact (ACUIhE.hom_add name _ _).symm

@[simp] theorem eval_reify_free (xs : Forest Const Var Hom) :
    (reify (free xs)).eval ic iv = E (Hom := Hom) ((reify xs).eval ic iv) := by
  cases xs with
  | nil => exact ACUIhE.free_zero.symm
  | cons t xs => exact ACUIhE.add_zero _

end Interpretation
end Presentation

variable {α : Type x} [ACUIhE Hom α]

/-- Interpret a canonical graph; the result does not depend on any enumeration. -/
def eval (ic : Const → α) (iv : Var → α) : Graph Const Var Hom → α :=
  Quotient.lift (fun xs => (Presentation.reify xs).eval ic iv)
    (fun _ _ h => Presentation.eval_eq_of_rel ic iv h)

@[simp] theorem eval_ofPresentation (ic : Const → α) (iv : Var → α)
    (xs : Presentation.Forest Const Var Hom) :
    eval ic iv (ofPresentation xs) = (Presentation.reify xs).eval ic iv := rfl

@[simp] theorem eval_zero (ic : Const → α) (iv : Var → α) :
    eval (Hom := Hom) ic iv 0 = 0 := rfl

@[simp] theorem eval_add (ic : Const → α) (iv : Var → α) (a b : Graph Const Var Hom) :
    eval ic iv (a + b) = eval ic iv a + eval ic iv b := by
  refine Quotient.inductionOn₂ a b ?_
  exact Presentation.eval_reify_append ic iv

@[simp] theorem eval_hom (ic : Const → α) (iv : Var → α) (name : Hom)
    (a : Graph Const Var Hom) : eval ic iv (hom name a) = H name (eval ic iv a) := by
  refine Quotient.inductionOn a ?_
  exact Presentation.eval_reify_hom ic iv name

@[simp] theorem eval_free (ic : Const → α) (iv : Var → α)
    (a : Graph Const Var Hom) : eval ic iv (free a) = E (Hom := Hom) (eval ic iv a) := by
  refine Quotient.inductionOn a ?_
  exact Presentation.eval_reify_free ic iv

end ACUIhE.Graph
