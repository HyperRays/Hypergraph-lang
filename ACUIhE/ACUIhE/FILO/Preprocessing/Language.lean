import ACUIhE.FILO.Preprocessing.Columns

/-!
# Finite-language operations used by flattening II

Derivatives and constant components have their literal set-theoretic meanings.
Restriction to a finite role signature commutes with every input constructor.
This justifies using only input roles; it is not an assumption on solutions.
-/

namespace ACUIhE.FILO.Language

open ACUIh.Linear

universe u v w

variable {Hom : Type w} [DecidableEq Hom]

def derivative (r : Hom) (p : WordPolynomial Hom) : WordPolynomial Hom :=
  ⟨(p.words.filter (fun word => word.head? = some r)).image List.tail⟩

@[simp] theorem mem_derivative (r : Hom) (p : WordPolynomial Hom) (word : List Hom) :
    word ∈ (derivative r p).words ↔ r :: word ∈ p.words := by
  simp only [derivative, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨source, ⟨member, head⟩, tail⟩
    cases source with
    | nil => cases head
    | cons s rest =>
      have eq : s = r := Option.some.inj head
      cases eq
      cases tail
      exact member
  · intro member
    exact ⟨r :: word, ⟨member, rfl⟩, rfl⟩

def constantPart (p : WordPolynomial Hom) : WordPolynomial Hom :=
  if [] ∈ p.words then 1 else 0

@[simp] theorem mem_constantPart (p : WordPolynomial Hom) (word : List Hom) :
    word ∈ (constantPart p).words ↔ word = [] ∧ [] ∈ p.words := by
  by_cases present : [] ∈ p.words <;> simp [constantPart, present]

@[simp] theorem mem_prefix (r : Hom) (p : WordPolynomial Hom) (word : List Hom) :
    word ∈ (WordPolynomial.generator r * p).words ↔ ∃ tail ∈ p.words, word = r :: tail := by
  simp only [WordPolynomial.mul_words, WordPolynomial.generator, WordPolynomial.monomial_words,
    Finset.mem_image₂, Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨tail, member, eq⟩; exact ⟨tail, member, eq.symm⟩
  · rintro ⟨tail, member, eq⟩; exact ⟨tail, member, eq.symm⟩

@[simp] theorem cons_mem_prefix (r s : Hom) (p : WordPolynomial Hom) (word : List Hom) :
    r :: word ∈ (WordPolynomial.generator s * p).words ↔ r = s ∧ word ∈ p.words := by
  simp only [mem_prefix, List.cons.injEq]
  constructor
  · rintro ⟨tail, member, eq, rfl⟩; exact ⟨eq, member⟩
  · rintro ⟨rfl, member⟩; exact ⟨word, member, rfl, rfl⟩

@[simp] theorem derivative_prefix (r s : Hom) (p : WordPolynomial Hom) :
    derivative r (WordPolynomial.generator s * p) = if r = s then p else 0 := by
  apply WordPolynomial.ext
  ext word
  rw [mem_derivative, cons_mem_prefix]
  by_cases eq : r = s <;> simp [eq]

@[simp] theorem derivative_add (r : Hom) (p q : WordPolynomial Hom) :
    derivative r (p + q) = derivative r p + derivative r q := by
  apply WordPolynomial.ext
  ext word
  simp

@[simp] theorem derivative_zero (r : Hom) : derivative r 0 = 0 := by
  apply WordPolynomial.ext
  ext word
  simp

@[simp] theorem derivative_one (r : Hom) : derivative r 1 = 0 := by
  apply WordPolynomial.ext
  ext word
  simp

def Supported (roles : Finset Hom) (p : WordPolynomial Hom) : Prop :=
  ∀ word ∈ p.words, ∀ r ∈ word, r ∈ roles

def restrict (roles : Finset Hom) (p : WordPolynomial Hom) : WordPolynomial Hom :=
  ⟨p.words.filter (fun word => ∀ r ∈ word, r ∈ roles)⟩

theorem derivative_supported {roles : Finset Hom} {p : WordPolynomial Hom}
    (supported : Supported roles p) (r : Hom) : Supported roles (derivative r p) := by
  intro word member s hs
  exact supported (r :: word) ((mem_derivative r p word).mp member) s (List.mem_cons_of_mem r hs)

theorem constantPart_supported (roles : Finset Hom) (p : WordPolynomial Hom) :
    Supported roles (constantPart p) := by
  intro word member
  have nilWord := ((mem_constantPart p word).mp member).1
  simp [nilWord]

theorem constantPart_subset_iff (p q : WordPolynomial Hom) :
    (constantPart p).words ⊆ q.words ↔ (constantPart p).words ⊆ (constantPart q).words := by
  constructor
  · intro sub word member
    have nilWord := ((mem_constantPart p word).mp member).1
    exact (mem_constantPart q word).mpr ⟨nilWord, nilWord ▸ sub member⟩
  · intro sub word member
    obtain ⟨nilWord, present⟩ := (mem_constantPart q word).mp (sub member)
    exact nilWord ▸ present

@[simp] theorem mem_restrict (roles : Finset Hom) (p : WordPolynomial Hom) (word : List Hom) :
    word ∈ (restrict roles p).words ↔ word ∈ p.words ∧ ∀ r ∈ word, r ∈ roles := by
  simp only [restrict, Finset.mem_filter]

theorem restrict_supported (roles : Finset Hom) (p : WordPolynomial Hom) :
    Supported roles (restrict roles p) := fun word member => (mem_restrict roles p word).mp member |>.2

@[simp] theorem restrict_zero (roles : Finset Hom) : restrict roles 0 = 0 := by
  apply WordPolynomial.ext
  ext word
  simp

@[simp] theorem restrict_one (roles : Finset Hom) : restrict roles 1 = 1 := by
  apply WordPolynomial.ext
  ext word
  simp only [mem_restrict, WordPolynomial.one_words, Finset.mem_singleton]
  exact ⟨And.left, fun h => ⟨h, by simp [h]⟩⟩

@[simp] theorem restrict_add (roles : Finset Hom) (p q : WordPolynomial Hom) :
    restrict roles (p + q) = restrict roles p + restrict roles q := by
  apply WordPolynomial.ext
  exact Finset.filter_union _ _ _

theorem restrict_prefix (roles : Finset Hom) {r : Hom} (present : r ∈ roles) (p : WordPolynomial Hom) :
    restrict roles (WordPolynomial.generator r * p) = WordPolynomial.generator r * restrict roles p := by
  apply WordPolynomial.ext
  ext word
  simp only [mem_restrict, mem_prefix]
  constructor
  · rintro ⟨⟨tail, member, rfl⟩, supported⟩
    exact ⟨tail, ⟨member, fun s hs => supported s (by simp [hs])⟩, rfl⟩
  · rintro ⟨tail, ⟨member, supported⟩, rfl⟩
    refine ⟨⟨tail, member, rfl⟩, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact present
    · exact supported s hs

/-- Equality and inclusion are preserved by deleting words outside the signature. -/
theorem restrict_mono (roles : Finset Hom) {p q : WordPolynomial Hom}
    (sub : p.words ⊆ q.words) : (restrict roles p).words ⊆ (restrict roles q).words := by
  intro word member
  obtain ⟨present, supported⟩ := (mem_restrict roles p word).mp member
  exact (mem_restrict roles q word).mpr ⟨sub present, supported⟩

/-- A finite role alphabet suffices to reconstruct a supported language from
its constant part and all role derivatives. -/
theorem subset_iff_components (roles : Finset Hom) (p q : WordPolynomial Hom)
    (supported : Supported roles p) :
    p.words ⊆ q.words ↔ (constantPart p).words ⊆ (constantPart q).words ∧
      ∀ r ∈ roles, (derivative r p).words ⊆ (derivative r q).words := by
  constructor
  · intro sub
    constructor
    · intro word member
      obtain ⟨rfl, present⟩ := (mem_constantPart p word).mp member
      exact (mem_constantPart q []).mpr ⟨rfl, sub present⟩
    · intro r _ word member
      exact (mem_derivative r q word).mpr (sub ((mem_derivative r p word).mp member))
  · rintro ⟨constant, derivatives⟩ word member
    cases word with
    | nil =>
      exact ((mem_constantPart q []).mp (constant ((mem_constantPart p []).mpr ⟨rfl, member⟩))).2
    | cons r tail =>
      exact (mem_derivative r q tail).mp (derivatives r (supported _ member r (by simp))
        ((mem_derivative r p tail).mpr member))

end ACUIhE.FILO.Language
