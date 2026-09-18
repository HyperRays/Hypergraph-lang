import ACUIhE.FILO.Shortcuts.Definition

/-!
# Finite shortcut reconstruction

A trace records the particles assigned along a finite shortcut derivation.
The role on an outgoing edge is appended on the right of a relative trace:
this is the reverse traversal of the paper's operation of prefixing the
particle at the source. In particular, homomorphism order is not commuted.
-/

namespace ACUIhE.FILO.Shortcuts

open Components ACUIh.Linear

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

abbrev Trace (Var : Type v) (Hom : Type w) := Finset (List Hom × Atom Var Hom)

def slice (t : Trace Var Hom) (word : List Hom) : Node Var Hom :=
  (t.filter (fun p => p.1 = word)).image Prod.snd

@[simp] theorem mem_slice (t : Trace Var Hom) (word : List Hom) (a : Atom Var Hom) :
    a ∈ slice t word ↔ (word, a) ∈ t := by
  simp only [slice, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨w, b, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨word, a, ⟨h, rfl⟩, rfl⟩

def polynomial (t : Trace Var Hom) (a : Atom Var Hom) : WordPolynomial Hom :=
  ⟨(t.filter (fun p => p.2 = a)).image Prod.fst⟩

@[simp] theorem mem_polynomial (t : Trace Var Hom) (a : Atom Var Hom) (word : List Hom) :
    word ∈ (polynomial t a).words ↔ (word, a) ∈ t := by
  simp only [polynomial, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨w, b, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨word, a, ⟨h, rfl⟩, rfl⟩

def graft (roles : List Hom) (root : Node Var Hom) (children : Hom → Trace Var Hom) :
    Trace Var Hom :=
  root.image (fun a => ([], a)) ∪ roles.toFinset.biUnion
    (fun r => (children r).image (fun p => (p.1 ++ [r], p.2)))

theorem mem_graft (roles : List Hom) (root : Node Var Hom) (children : Hom → Trace Var Hom)
    (word : List Hom) (a : Atom Var Hom) :
    (word, a) ∈ graft roles root children ↔
      (word = [] ∧ a ∈ root) ∨
      ∃ r ∈ roles, ∃ stem, word = stem ++ [r] ∧ (stem, a) ∈ children r := by
  simp only [graft, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    List.mem_toFinset, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro (⟨b, hb, h, rfl⟩ | ⟨r, hr, p, b, h, eq, rfl⟩)
    · exact .inl ⟨h.symm, hb⟩
    · exact .inr ⟨r, hr, p, eq.symm, h⟩
  · rintro (⟨rfl, h⟩ | ⟨r, hr, p, rfl, h⟩)
    · exact .inl ⟨a, h, rfl, rfl⟩
    · exact .inr ⟨r, hr, p, a, h, rfl, rfl⟩

@[simp] theorem nil_mem_graft (roles : List Hom) (root : Node Var Hom)
    (children : Hom → Trace Var Hom) (a : Atom Var Hom) :
    ([], a) ∈ graft roles root children ↔ a ∈ root := by
  simp [mem_graft]

@[simp] theorem snoc_mem_graft (roles : List Hom) (root : Node Var Hom)
    (children : Hom → Trace Var Hom) (word : List Hom) (r : Hom) (a : Atom Var Hom) :
    (word ++ [r], a) ∈ graft roles root children ↔ r ∈ roles ∧ (word, a) ∈ children r := by
  rw [mem_graft]
  simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, false_and, false_or]
  constructor
  · rintro ⟨s, hs, stem, eq, member⟩
    have e : word = stem ∧ r = s := by
      have lens : word.length = stem.length := by
        have h := congrArg List.length eq
        simp only [List.length_append, List.length_singleton] at h
        omega
      have h := List.append_inj eq lens
      exact ⟨h.1, List.singleton_inj.mp h.2⟩
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨hs, member⟩
  · rintro ⟨hr, member⟩
    exact ⟨r, hr, word, rfl, member⟩

/-- The reconstruction invariant. This is a theorem predicate, not an output type. -/
structure Realizes (s : System Var Hom) (root : Node Var Hom) (t : Trace Var Hom) : Prop where
  at_nil : ∀ a, ([], a) ∈ t ↔ a ∈ root
  in_atoms : ∀ word a, (word, a) ∈ t → a ∈ (atoms s).toFinset
  supported : ∀ word a, (word, a) ∈ t → ∀ r ∈ word, r ∈ s.roles
  flat : ∀ word, Flat s (slice t word)
  literal : ∀ word, (word, .const ()) ∈ t ↔ word = [] ∧ .const () ∈ root
  constant : ∀ x, .constant x ∈ s.names → ∀ word,
    (word, .var (.constant x)) ∈ t ↔ word = [] ∧ .var (.constant x) ∈ root
  role : ∀ r x, .role r x ∈ s.names → ∀ word,
    (word, .var (.role r x)) ∈ t ↔ (r :: word, .var x) ∈ t

theorem realizes_empty (s : System Var Hom) : Realizes s ∅ ∅ := by
  constructor
  · simp
  · simp
  · simp
  · intro word; simpa [slice] using flat_empty s
  · simp
  · simp
  · simp

/-- Joining already realized resolvers is sound. Unneeded roles have no trace. -/
theorem realizes_graft (s : System Var Hom) (initial : Bool) (root : Node Var Hom)
    (localRoot : Local s initial root) (targets : Hom → Node Var Hom)
    (children : Hom → Trace Var Hom)
    (childLocal : ∀ r ∈ s.roles, Local s false (targets r))
    (childRealizes : ∀ r ∈ s.roles, Realizes s (targets r) (children r))
    (links : ∀ r ∈ s.roles, Resolves s root r (targets r)) :
    Realizes s root (graft s.roles root children) := by
  constructor
  · exact nil_mem_graft s.roles root children
  · intro word a h
    rcases (mem_graft _ _ _ _ _).mp h with ⟨rfl, hp⟩ | ⟨r, hr, p, rfl, hp⟩
    · exact localRoot.1 hp
    · exact (childRealizes r hr).in_atoms p a hp
  · intro word a h r hr
    rcases (mem_graft _ _ _ _ _).mp h with ⟨rfl, _⟩ | ⟨s', hs, p, rfl, hp⟩
    · exact False.elim (List.not_mem_nil hr)
    · rcases List.mem_append.mp hr with hr | hr
      · exact (childRealizes s' hs).supported p a hp r hr
      · exact List.mem_singleton.mp hr ▸ hs
  · intro word q hq a ha h
    induction word using List.reverseRecOn with
    | nil =>
      have member := (nil_mem_graft _ _ _ a).mp ((mem_slice _ _ _).mp h)
      obtain ⟨b, hb, present⟩ := localRoot.2.1 q hq a ha member
      exact ⟨b, hb, (mem_slice _ _ _).mpr ((nil_mem_graft _ _ _ b).mpr present)⟩
    | append_singleton word r _ =>
      obtain ⟨hr, member⟩ := (snoc_mem_graft _ _ _ word r a).mp ((mem_slice _ _ _).mp h)
      obtain ⟨b, hb, present⟩ := (childRealizes r hr).flat word q hq a ha
        ((mem_slice _ _ _).mpr member)
      exact ⟨b, hb, (mem_slice _ _ _).mpr ((snoc_mem_graft _ _ _ word r b).mpr
        ⟨hr, (mem_slice _ _ _).mp present⟩)⟩
  · intro word
    induction word using List.reverseRecOn with
    | nil => simp
    | append_singleton word r _ =>
      rw [snoc_mem_graft]
      constructor
      · rintro ⟨hr, h⟩
        have hc := ((childRealizes r hr).literal word).mp h |>.2
        have no := (childLocal r hr).2.2.2.1.mp hc
        cases no
      · simp
  · intro x hx word
    induction word using List.reverseRecOn with
    | nil => simp
    | append_singleton word r _ =>
      rw [snoc_mem_graft]
      constructor
      · rintro ⟨hr, h⟩
        have hc := ((childRealizes r hr).constant x hx word).mp h |>.2
        have no := (childLocal r hr).2.2.2.2 (.constant x) hx |>.mp hc |>.1
        cases no
      · simp
  · intro r x hx word
    induction word using List.reverseRecOn with
    | nil =>
      change ([], .var (.role r x)) ∈ graft s.roles root children ↔
        ([] ++ [r], .var x) ∈ graft s.roles root children
      rw [nil_mem_graft, snoc_mem_graft]
      constructor
      · intro h
        have hr := localRoot.2.2.1 (.role r x) hx h
        exact ⟨hr, ((childRealizes r hr).at_nil _).mpr
          ((links r hr (.role r x) hx rfl).mp h)⟩
      · rintro ⟨hr, h⟩
        exact (links r hr (.role r x) hx rfl).mpr (((childRealizes r hr).at_nil _).mp h)
    | append_singleton word t _ =>
      change (word ++ [t], .var (.role r x)) ∈ graft s.roles root children ↔
        ((r :: word) ++ [t], .var x) ∈ graft s.roles root children
      rw [snoc_mem_graft, snoc_mem_graft]
      exact and_congr_right (fun ht => (childRealizes t ht).role r x hx word)

end ACUIhE.FILO.Shortcuts
