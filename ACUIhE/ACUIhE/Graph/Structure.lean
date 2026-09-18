import ACUIhE.ACUIhNF.Definition

/-!
# Hereditarily finite sets of word-labelled summands

`Tree` and lists of trees are executable presentations. An edge has a nonempty
child layer, so `E(0)` cannot occur in a presentation. `Graph` quotients
presentations by recursive *set* equality: order and multiplicity are ignored
at every layer, while words, particles, and E boundaries are retained.

This structural relation does not mention terms, evaluation, or `Derives`.
The quotient plays the same role as the multiset quotient underlying `Finset`;
it also avoids imposing orders on the label types. It is not a quotient of
terms by the equations we will subsequently prove it decides.
-/

namespace ACUIhE

universe u v w

namespace Graph.Presentation

/-- A summand: either a local particle, or an E edge to a nonempty layer. -/
inductive Tree (Const : Type u) (Var : Type v) (Hom : Type w) where
  | atom (word : List Hom) (particle : ACUIh.Particle Const Var)
  | edge (word : List Hom) (first : Tree Const Var Hom)
      (rest : List (Tree Const Var Hom))

abbrev Forest (Const : Type u) (Var : Type v) (Hom : Type w) :=
  List (Tree Const Var Hom)

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- Mutual coverage, with no dependence on order or multiplicity. -/
def Setwise {α : Type*} (r : α → α → Prop) (xs ys : List α) : Prop :=
  (∀ x ∈ xs, ∃ y, ∃ _hy : y ∈ ys, r x y) ∧
  (∀ y ∈ ys, ∃ x, ∃ _hx : x ∈ xs, r x y)

theorem Tree.child_lt (word : List Hom) (first : Tree Const Var Hom)
    (rest : List (Tree Const Var Hom)) {t : Tree Const Var Hom}
    (ht : t ∈ first :: rest) : sizeOf t < sizeOf (Tree.edge word first rest) := by
  have bound := List.sizeOf_lt_of_mem ht
  simp only [Tree.edge.sizeOf_spec, List.cons.sizeOf_spec] at *
  omega

/-- Structural equality of summands, recursively using set equality of children. -/
def Tree.Rel : Tree Const Var Hom → Tree Const Var Hom → Prop
  | .atom word p, .atom word' p' => word = word' ∧ p = p'
  | .edge word first rest, .edge word' first' rest' =>
      word = word' ∧
        (∀ t ∈ first :: rest, ∃ s, ∃ _hs : s ∈ first' :: rest', Tree.Rel t s) ∧
        (∀ s ∈ first' :: rest', ∃ t, ∃ _ht : t ∈ first :: rest, Tree.Rel t s)
  | _, _ => False
termination_by left => sizeOf left
decreasing_by
  all_goals exact Tree.child_lt word first rest ‹_ ∈ first :: rest›

abbrev Rel (xs ys : Forest Const Var Hom) : Prop := Setwise Tree.Rel xs ys

theorem Tree.rel_refl (t : Tree Const Var Hom) : t.Rel t := by
  induction t using (measure (fun t : Tree Const Var Hom => sizeOf t)).wf.induction
  rename_i t ih
  cases t with
  | atom word p => simp [Tree.Rel]
  | edge word first rest =>
      rw [Tree.Rel]
      refine ⟨rfl, ?_, ?_⟩ <;> intro t ht <;>
        exact ⟨t, ht, ih t (Tree.child_lt word first rest ht)⟩

theorem Tree.rel_symm {a b : Tree Const Var Hom} (h : a.Rel b) : b.Rel a := by
  induction a using (measure (fun t : Tree Const Var Hom => sizeOf t)).wf.induction
    generalizing b
  rename_i a ih
  cases a with
  | atom word p =>
      cases b with
      | atom => simpa only [Tree.Rel, eq_comm] using h
      | edge => simp only [Tree.Rel] at h
  | edge word first rest =>
      cases b with
      | atom => simp only [Tree.Rel] at h
      | edge word' first' rest' =>
          rw [Tree.Rel] at h ⊢
          have flip : ∀ t ∈ first :: rest, ∀ s, t.Rel s → s.Rel t := by
            intro t ht
            exact fun _ => ih t (Tree.child_lt word first rest ht)
          refine ⟨h.1.symm, ?_, ?_⟩
          · intro s hs
            obtain ⟨t, ht, r⟩ := h.2.2 s hs
            exact ⟨t, ht, flip t ht s r⟩
          · intro t ht
            obtain ⟨s, hs, r⟩ := h.2.1 t ht
            exact ⟨s, hs, flip t ht s r⟩

theorem Tree.rel_trans {a b c : Tree Const Var Hom}
    (hab : a.Rel b) (hbc : b.Rel c) : a.Rel c := by
  induction a using (measure (fun t : Tree Const Var Hom => sizeOf t)).wf.induction
    generalizing b c
  rename_i a ih
  cases a with
  | atom word p =>
      cases b <;> cases c <;> simp_all [Tree.Rel]
  | edge word first rest =>
      cases b with
      | atom => simp only [Tree.Rel] at hab
      | edge word' first' rest' =>
          cases c with
          | atom => simp only [Tree.Rel] at hbc
          | edge word'' first'' rest'' =>
              rw [Tree.Rel] at hab hbc ⊢
              have chain : ∀ t ∈ first :: rest, ∀ s z, t.Rel s → s.Rel z → t.Rel z := by
                intro t ht
                exact fun _ _ => ih t (Tree.child_lt word first rest ht)
              refine ⟨hab.1.trans hbc.1, ?_, ?_⟩
              · intro t ht
                obtain ⟨s, hs, r⟩ := hab.2.1 t ht
                obtain ⟨z, hz, r'⟩ := hbc.2.1 s hs
                exact ⟨z, hz, chain t ht s z r r'⟩
              · intro z hz
                obtain ⟨s, hs, r'⟩ := hbc.2.2 z hz
                obtain ⟨t, ht, r⟩ := hab.2.2 s hs
                exact ⟨t, ht, chain t ht s z r r'⟩

theorem rel_refl (xs : Forest Const Var Hom) : Rel xs xs :=
  ⟨fun t ht => ⟨t, ht, t.rel_refl⟩, fun t ht => ⟨t, ht, t.rel_refl⟩⟩

theorem rel_symm {xs ys : Forest Const Var Hom} (h : Rel xs ys) : Rel ys xs :=
  ⟨fun y hy => let ⟨x, hx, hxy⟩ := h.2 y hy; ⟨x, hx, Tree.rel_symm hxy⟩,
   fun x hx => let ⟨y, hy, hxy⟩ := h.1 x hx; ⟨y, hy, Tree.rel_symm hxy⟩⟩

theorem rel_trans {xs ys zs : Forest Const Var Hom}
    (h : Rel xs ys) (h' : Rel ys zs) : Rel xs zs := by
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := h.1 x hx
    obtain ⟨z, hz, hyz⟩ := h'.1 y hy
    exact ⟨z, hz, Tree.rel_trans hxy hyz⟩
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := h'.2 z hz
    obtain ⟨x, hx, hxy⟩ := h.2 y hy
    exact ⟨x, hx, Tree.rel_trans hxy hyz⟩

def setoid (Const : Type u) (Var : Type v) (Hom : Type w) :
    Setoid (Forest Const Var Hom) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

theorem rel_of_mem_iff {xs ys : Forest Const Var Hom}
    (h : ∀ t, t ∈ xs ↔ t ∈ ys) : Rel xs ys :=
  ⟨fun t ht => ⟨t, (h t).mp ht, t.rel_refl⟩,
   fun t ht => ⟨t, (h t).mpr ht, t.rel_refl⟩⟩

@[simp] theorem rel_nil_right (xs : Forest Const Var Hom) : Rel xs [] ↔ xs = [] := by
  cases xs with
  | nil => exact ⟨fun _ => rfl, fun _ => rel_refl []⟩
  | cons x xs =>
      constructor
      · intro h
        obtain ⟨y, hy, _⟩ := h.1 x (by simp)
        exact (List.not_mem_nil hy).elim
      · intro h
        cases h

@[simp] theorem rel_nil_left (xs : Forest Const Var Hom) : Rel [] xs ↔ xs = [] :=
  ⟨fun h => (rel_nil_right xs).mp (rel_symm h),
   fun h => rel_symm ((rel_nil_right xs).mpr h)⟩

@[simp] theorem rel_singleton (a b : Tree Const Var Hom) : Rel [a] [b] ↔ a.Rel b := by
  simp [Rel, Setwise]

theorem rel_append {xs xs' ys ys' : Forest Const Var Hom}
    (hx : Rel xs xs') (hy : Rel ys ys') : Rel (xs ++ ys) (xs' ++ ys') := by
  constructor
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨s, hs, r⟩ := hx.1 t ht
      exact ⟨s, List.mem_append_left _ hs, r⟩
    · obtain ⟨s, hs, r⟩ := hy.1 t ht
      exact ⟨s, List.mem_append_right _ hs, r⟩
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨t, ht, r⟩ := hx.2 s hs
      exact ⟨t, List.mem_append_left _ ht, r⟩
    · obtain ⟨t, ht, r⟩ := hy.2 s hs
      exact ⟨t, List.mem_append_right _ ht, r⟩

def Tree.prepend (name : Hom) : Tree Const Var Hom → Tree Const Var Hom
  | .atom word p => .atom (name :: word) p
  | .edge word first rest => .edge (name :: word) first rest

theorem Tree.rel_prepend (name : Hom) {a b : Tree Const Var Hom}
    (h : a.Rel b) : (a.prepend name).Rel (b.prepend name) := by
  cases a <;> cases b <;> simp_all [Tree.prepend, Tree.Rel]

def hom (name : Hom) (xs : Forest Const Var Hom) : Forest Const Var Hom :=
  xs.map (Tree.prepend name)

theorem rel_hom (name : Hom) {xs ys : Forest Const Var Hom}
    (h : Rel xs ys) : Rel (hom name xs) (hom name ys) := by
  constructor
  · intro t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    obtain ⟨b, hb, r⟩ := h.1 a ha
    exact ⟨b.prepend name, List.mem_map.mpr ⟨b, hb, rfl⟩, Tree.rel_prepend name r⟩
  · intro t ht
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    obtain ⟨a, ha, r⟩ := h.2 b hb
    exact ⟨a.prepend name, List.mem_map.mpr ⟨a, ha, rfl⟩, Tree.rel_prepend name r⟩

/-- The only collapsing E case is its empty child. -/
def free : Forest Const Var Hom → Forest Const Var Hom
  | [] => []
  | first :: rest => [.edge [] first rest]

theorem rel_free_iff (xs ys : Forest Const Var Hom) :
    Rel (free xs) (free ys) ↔ Rel xs ys := by
  cases xs <;> cases ys <;> simp [free, Tree.Rel, Rel, Setwise] <;>
    exact ⟨_, fun h => (h rfl).elim⟩

end Graph.Presentation

/-- Canonical ACUIhE graphs: hereditarily finite sets, with no zero E children. -/
def Graph (Const : Type u) (Var : Type v) (Hom : Type w) :=
  Quotient (Graph.Presentation.setoid Const Var Hom)

namespace Graph

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- Forget only presentation order and duplication, recursively. -/
def ofPresentation (xs : Presentation.Forest Const Var Hom) : Graph Const Var Hom :=
  Quotient.mk _ xs

/-- A local constant, with an empty homomorphism word and no E children. -/
def constant (name : Const) : Graph Const Var Hom :=
  ofPresentation [.atom [] (.const name)]

/-- A local variable, with an empty homomorphism word and no E children. -/
def ofVariable (name : Var) : Graph Const Var Hom :=
  ofPresentation [.atom [] (.var name)]

theorem ofPresentation_eq_iff (xs ys : Presentation.Forest Const Var Hom) :
    ofPresentation xs = ofPresentation ys ↔ Presentation.Rel xs ys :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

instance : Zero (Graph Const Var Hom) := ⟨ofPresentation []⟩

/-- An ordinary particle, or an E edge to a nonzero canonical child. -/
abbrev Atom (Const : Type u) (Var : Type v) (Hom : Type w) :=
  ACUIh.Particle Const Var ⊕ {child : Graph Const Var Hom // child ≠ 0}

abbrev Summand (Const : Type u) (Var : Type v) (Hom : Type w) :=
  List Hom × Atom Const Var Hom

abbrev Layer (Const : Type u) (Var : Type v) (Hom : Type w) :=
  Finset (Summand Const Var Hom)

/-- Include a local ACUIh summand without introducing an E edge. -/
def localSummand : ACUIh.Summand Const Var Hom ↪ Summand Const Var Hom where
  toFun := fun summand => (summand.1, .inl summand.2)
  inj' := by
    intro ⟨word, particle⟩ ⟨word', particle'⟩ equality
    simpa using equality

namespace Layer

/-- The edge-free layer of an ordinary ACUIh normal form. -/
def ofNF (normal : ACUIh.NF Const Var Hom) : Layer Const Var Hom :=
  normal.map localSummand

theorem ofNF_injective : Function.Injective (ofNF (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro a b h
  exact Finset.map_injective localSummand h

/-- The local inclusion cannot contain an E child. -/
@[simp] theorem not_mem_ofNF_edge (normal : ACUIh.NF Const Var Hom)
    (word : List Hom) (child : Graph Const Var Hom) (nonzero : child ≠ 0) :
    (word, .inr ⟨child, nonzero⟩) ∉ ofNF normal := by
  intro member
  obtain ⟨⟨_, _⟩, _, equality⟩ := Finset.mem_map.mp member
  have parts := Prod.mk.inj equality
  cases parts.2

end Layer

instance : Add (Graph Const Var Hom) where
  add := Quotient.lift₂ (fun xs ys => ofPresentation (xs ++ ys))
    (fun _ _ _ _ hx hy => Quotient.sound (Presentation.rel_append hx hy))

def hom (name : Hom) : Graph Const Var Hom → Graph Const Var Hom :=
  Quotient.lift (fun xs => ofPresentation (Presentation.hom name xs))
    (fun _ _ h => Quotient.sound (Presentation.rel_hom name h))

def free : Graph Const Var Hom → Graph Const Var Hom :=
  Quotient.lift (fun xs => ofPresentation (Presentation.free xs))
    (fun xs ys h => Quotient.sound ((Presentation.rel_free_iff xs ys).mpr h))

@[simp] theorem ofPresentation_nil :
    ofPresentation ([] : Presentation.Forest Const Var Hom) = 0 := rfl

@[simp] theorem ofPresentation_append (xs ys : Presentation.Forest Const Var Hom) :
    ofPresentation (xs ++ ys) = ofPresentation xs + ofPresentation ys := rfl

@[simp] theorem hom_ofPresentation (name : Hom) (xs : Presentation.Forest Const Var Hom) :
    hom name (ofPresentation xs) = ofPresentation (Presentation.hom name xs) := rfl

@[simp] theorem free_ofPresentation (xs : Presentation.Forest Const Var Hom) :
    free (ofPresentation xs) = ofPresentation (Presentation.free xs) := rfl

/-- The free operator is genuinely injective, including its zero case. -/
theorem free_injective : Function.Injective (free (Const := Const) (Var := Var)
    (Hom := Hom)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro xs ys eq
  exact Quotient.sound ((Presentation.rel_free_iff xs ys).mp (Quotient.exact eq))

/-- The structural canonical forms form a model of the entire ACUIhE theory. -/
instance algebra : ACUIhE Hom (Graph Const Var Hom) where
  hom := hom
  free := free
  add_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro xs ys zs
    change ofPresentation ((xs ++ ys) ++ zs) = ofPresentation (xs ++ (ys ++ zs))
    rw [List.append_assoc]
  add_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro xs ys
    apply Quotient.sound
    exact Presentation.rel_of_mem_iff (fun _ => by simp [or_comm])
  add_zero := by
    intro a
    refine Quotient.inductionOn a ?_
    intro xs
    change ofPresentation (xs ++ []) = ofPresentation xs
    rw [List.append_nil]
  add_idem := by
    intro a
    refine Quotient.inductionOn a ?_
    intro xs
    apply Quotient.sound
    exact Presentation.rel_of_mem_iff (fun _ => by simp)
  hom_add := by
    intro name a b
    refine Quotient.inductionOn₂ a b ?_
    intro xs ys
    change ofPresentation (Presentation.hom name (xs ++ ys)) =
      ofPresentation (Presentation.hom name xs ++ Presentation.hom name ys)
    simp only [Presentation.hom, List.map_append]
  hom_zero := fun _ => rfl
  free_zero := rfl
  free_injective := free_injective

section FiniteSums

local instance : Std.Commutative (fun a b : Graph Const Var Hom => a + b) :=
  ⟨ACUIhE.add_comm (Hom := Hom)⟩
local instance : Std.Associative (fun a b : Graph Const Var Hom => a + b) :=
  ⟨ACUIhE.add_assoc (Hom := Hom)⟩
local instance : Std.IdempotentOp (fun a b : Graph Const Var Hom => a + b) :=
  ⟨ACUIhE.add_idem (Hom := Hom)⟩

/-- Embed an ACUIh normal form as a canonical graph without E children.
The finite-set fold is executable without choosing an enumeration. -/
def ofNF (normal : ACUIh.NF Const Var Hom) : Graph Const Var Hom :=
  normal.fold (fun a b : Graph Const Var Hom => a + b) 0
    (fun summand => ofPresentation [.atom summand.1 summand.2])

@[simp] theorem ofNF_empty : ofNF (∅ : ACUIh.NF Const Var Hom) = 0 := rfl

@[simp] theorem ofNF_singleton (summand : ACUIh.Summand Const Var Hom) :
    ofNF {summand} = ofPresentation [.atom summand.1 summand.2] := by
  simp only [ofNF, Finset.fold_singleton]
  exact ACUIhE.add_zero (Hom := Hom) (ofPresentation [.atom summand.1 summand.2])

@[simp] theorem ofNF_insert [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (summand : ACUIh.Summand Const Var Hom) (normal : ACUIh.NF Const Var Hom) :
    ofNF (insert summand normal) = ofPresentation [.atom summand.1 summand.2] + ofNF normal :=
  Finset.fold_insert_idem

end FiniteSums

end Graph

end ACUIhE
