import ACUIhE.Solver

set_option autoImplicit false

namespace HMEmbedding
open ACUIhE

inductive Op where
  | fn | pair
  deriving DecidableEq

/-- The source HM monotypes. This syntax is used to state the embedding theorem;
the target uses the existing ACUIhE terms and equality. -/
inductive Mono (V : Type) where
  | var : V → Mono V
  | base : Nat → Mono V
  | op : Op → Mono V → Mono V → Mono V
  deriving DecidableEq

inductive Constant where
  | base : Nat → Constant
  | tag : Op → Constant
  | edge | undirected | set | option | none | some
  deriving DecidableEq

inductive Field where
  | first | second
  | edgeTail | edgeHead | edgePayload
  | undirectedTail | undirectedHead | undirectedPayload
  | element | optionPayload
  deriving DecidableEq

abbrev AlgebraType (V : Type) := Term Constant V Field

/-- The binary members of the existing O_i family. -/
def O₂ {V : Type} (i : Op) (a b : AlgebraType V) : AlgebraType V :=
  .free (.add (.const (.tag i))
    (.add (.hom .first a) (.add (.hom .second b) .zero)))

theorem eval_O₂ {V A : Type} [ACUIhE Field A]
    (i : Op) (a b : AlgebraType V) (ic : Constant → A) (iv : V → A) :
    (O₂ i a b).eval ic iv =
      O ic (fun n => if n = 1 then Field.first else Field.second)
        (.tag i) [a.eval ic iv, b.eval ic iv] := rfl

def Mono.encode {V : Type} : Mono V → AlgebraType V
  | .var v => .var v
  | .base b => .const (.base b)
  | .op i a b => O₂ i a.encode b.encode

def Mono.subst {V W : Type} (s : V → Mono W) : Mono V → Mono W
  | .var v => s v
  | .base b => .base b
  | .op i a b => .op i (a.subst s) (b.subst s)

theorem encode_subst {V W : Type} (t : Mono V) (s : V → Mono W) :
    (t.subst s).encode = t.encode.substitute (fun v => (s v).encode) := by
  induction t <;> simp_all [Mono.subst, Mono.encode, O₂, Term.substitute]

namespace Faithful
open Graph.Presentation

def tree {V : Type} : Mono V → Tree Constant V Field
  | .var v => .atom [] (.var v)
  | .base b => .atom [] (.const (.base b))
  | .op i a b => .edge [] (.atom [] (.const (.tag i)))
      [(tree a).prepend .first, (tree b).prepend .second]

def word {V : Type} : Tree Constant V Field → List Field
  | .atom w _ => w
  | .edge w _ _ => w

@[simp] theorem word_tree {V : Type} (t : Mono V) : word (tree t) = [] := by
  cases t <;> rfl

@[simp] theorem word_prepend {V : Type} (h : Field) (t : Tree Constant V Field) :
    word (t.prepend h) = h :: word t := by cases t <;> rfl

theorem rel_word {V : Type} {a b : Tree Constant V Field} (h : a.Rel b) :
    word a = word b := by
  cases a <;> cases b <;> simp_all [Tree.Rel, word]

@[simp] theorem rel_prepend {V : Type} (h k : Field) (a b : Tree Constant V Field) :
    (a.prepend h).Rel (b.prepend k) ↔ h = k ∧ a.Rel b := by
  cases a <;> cases b <;> simp [Tree.prepend, Tree.Rel, and_assoc]

@[simp] theorem tag_not_prepend {V : Type} (i : Op) (h : Field)
    (t : Tree Constant V Field) :
    ¬ (Tree.atom [] (.const (.tag i))).Rel (t.prepend h) := by
  intro r
  have := rel_word r
  rw [word_prepend] at this
  cases this

@[simp] theorem prepend_not_tag {V : Type} (i : Op) (h : Field)
    (t : Tree Constant V Field) :
    ¬ (t.prepend h).Rel (.atom [] (.const (.tag i))) := by
  intro r
  exact tag_not_prepend i h t (Tree.rel_symm r)

theorem tree_rel_iff {V : Type} (a b : Mono V) : (tree a).Rel (tree b) ↔ a = b := by
  induction a generalizing b with
  | var v => cases b <;> simp [tree, Tree.Rel]
  | base n => cases b <;> simp [tree, Tree.Rel]
  | op i a₁ a₂ ih₁ ih₂ =>
    cases b with
    | var | base => simp [tree, Tree.Rel]
    | op j b₁ b₂ =>
      constructor
      · intro h
        simp only [tree, Tree.Rel] at h
        have forward := h.2.1
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp] at forward
        simp_all [Tree.Rel]
      · intro eq
        rcases Mono.op.inj eq with ⟨rfl, rfl, rfl⟩
        exact Tree.rel_refl _

theorem normalize_encode {V : Type} (t : Mono V) :
    Graph.normalize t.encode = Graph.ofPresentation [tree t] := by
  induction t with
  | var | base => rfl
  | op i a b ia ib =>
    simp only [Mono.encode, O₂, Graph.normalize_free, Graph.normalize_add,
      Graph.normalize_const, Graph.normalize_hom, Graph.normalize_zero, ia, ib]
    rfl

end Faithful

/-- No new equations between HM types arise in the full ACUIhE theory. -/
theorem encode_equal_iff {V : Type} (a b : Mono V) :
    a.encode.Equal b.encode ↔ a = b := by
  change SemanticallyEquivalent a.encode b.encode ↔ a = b
  rw [← Graph.normalize_eq_iff_semanticallyEquivalent,
    Faithful.normalize_encode, Faithful.normalize_encode,
    Graph.ofPresentation_eq_iff, Graph.Presentation.rel_singleton,
    Faithful.tree_rel_iff]

theorem encode_injective {V : Type} : Function.Injective (Mono.encode (V := V)) := by
  intro a b h
  apply (encode_equal_iff a b).mp
  rw [h]
  exact Term.Equal.refl _

def Mono.fv {V : Type} [DecidableEq V] : Mono V → Finset V
  | .var v => {v}
  | .base _ => ∅
  | .op _ a b => a.fv ∪ b.fv

/-- Free variables of an existing algebraic term. -/
def freeVars {V : Type} [DecidableEq V] : AlgebraType V → Finset V
  | .zero | .const _ => ∅
  | .var v => {v}
  | .add a b => freeVars a ∪ freeVars b
  | .hom _ a | .free a => freeVars a

theorem encode_fv {V : Type} [DecidableEq V] (t : Mono V) :
    freeVars t.encode = t.fv := by
  induction t <;> simp_all [Mono.encode, Mono.fv, O₂, freeVars]

/-- The HM constructor fragment, specified directly on ACUIhE syntax. -/
inductive WellFormed {V : Type} : AlgebraType V → Prop
  | var (v : V) : WellFormed (.var v)
  | base (n : Nat) : WellFormed (.const (.base n))
  | op (i : Op) {a b : AlgebraType V} :
      WellFormed a → WellFormed b → WellFormed (O₂ i a b)

theorem encode_wellFormed {V : Type} (t : Mono V) : WellFormed t.encode := by
  induction t with
  | var v => exact .var v
  | base n => exact .base n
  | op i a b ia ib => exact .op i ia ib

theorem wellFormed_iff_image {V : Type} (t : AlgebraType V) :
    WellFormed t ↔ ∃ m : Mono V, m.encode = t := by
  constructor
  · intro h
    induction h with
    | var v => exact ⟨.var v, rfl⟩
    | base n => exact ⟨.base n, rfl⟩
    | op i ha hb ia ib =>
      obtain ⟨a, rfl⟩ := ia
      obtain ⟨b, rfl⟩ := ib
      exact ⟨.op i a b, rfl⟩
  · rintro ⟨m, rfl⟩
    exact encode_wellFormed m

theorem WellFormed.substitute {V W : Type} {t : AlgebraType V}
    (h : WellFormed t) (s : V → AlgebraType W) (hs : ∀ v, WellFormed (s v)) :
    WellFormed (t.substitute s) := by
  induction h with
  | var v => exact hs v
  | base n => exact .base n
  | op i ha hb ia ib => exact .op i ia ib

/-- A carrier of HM-shaped representatives; equality below remains ACUIhE equality. -/
abbrev Fragment := {t : AlgebraType Nat // WellFormed t}

def embed (t : Mono Nat) : Fragment := ⟨t.encode, encode_wellFormed t⟩

theorem embed_injective : Function.Injective embed := by
  intro a b h
  exact encode_injective (congrArg Subtype.val h)

theorem embed_surjective : Function.Surjective embed := by
  rintro ⟨t, ht⟩
  obtain ⟨m, hm⟩ := (wellFormed_iff_image t).mp ht
  exact ⟨m, Subtype.ext hm⟩

/-- Decoding is used only in proofs; target operations use ACUIhE directly. -/
noncomputable def decode (t : Fragment) : Mono Nat :=
  Classical.choose (embed_surjective t)

@[simp] theorem embed_decode (t : Fragment) : embed (decode t) = t :=
  Classical.choose_spec (embed_surjective t)

@[simp] theorem decode_embed (t : Mono Nat) : decode (embed t) = t :=
  embed_injective (embed_decode (embed t))

end HMEmbedding
