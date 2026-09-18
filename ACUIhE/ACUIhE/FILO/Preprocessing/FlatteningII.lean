import ACUIhE.FILO.Preprocessing.Components
import ACUIhE.FILO.Preprocessing.Projection

/-! # Verified flattening-II rules (Figure 2) -/

namespace ACUIhE.FILO.FlatteningII

open ACUIh.Linear Components

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Hom]

local instance : ACUIh Hom (WordPolynomial Hom) := Column.algebra

abbrev Shallow (Var : Type v) (Hom : Type w) := Flat.Particle Unit (Components.Variable Var Hom) Hom

abbrev Concept (Var : Type v) (Hom : Type w) := List (Shallow Var Hom)

def embedAtom : Flat.Atom Unit Var → Components.Atom Var Hom
  | .const c => .const c
  | .var v => .var (.base v)

def embed : Flat.Particle Unit Var Hom → Shallow Var Hom
  | .atom a => .atom (embedAtom a)
  | .hom r a => .hom r (embedAtom a)

def eval (iv : Column Var Hom) (ps : Concept Var Hom) : WordPolynomial Hom :=
  Flat.Concept.eval (fun _ => 1) (interpret iv) ps

def particleValue (iv : Column Var Hom) (p : Shallow Var Hom) : WordPolynomial Hom :=
  p.eval (fun _ => 1) (interpret iv)

@[simp] theorem eval_nil (iv : Column Var Hom) : eval iv [] = 0 := rfl

@[simp] theorem eval_cons (iv : Column Var Hom) (p : Shallow Var Hom) (ps : Concept Var Hom) :
    eval iv (p :: ps) = particleValue iv p + eval iv ps := rfl

@[simp] theorem particleValue_atom (iv : Column Var Hom) (a : Components.Atom Var Hom) :
    particleValue iv (.atom a) = atomValue iv a := by cases a <;> rfl

@[simp] theorem particleValue_hom (iv : Column Var Hom) (r : Hom) (a : Components.Atom Var Hom) :
    particleValue iv (.hom r a) = WordPolynomial.generator r * atomValue iv a := by cases a <;> rfl

@[simp] theorem mem_eval (iv : Column Var Hom) (ps : Concept Var Hom) (word : List Hom) :
    word ∈ (eval iv ps).words ↔ ∃ p ∈ ps, word ∈ (particleValue iv p).words := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [eval_cons, WordPolynomial.add_words, Finset.mem_union, ih,
      List.mem_cons, exists_eq_or_imp]

def bare (roles : List Hom) (available : Expression Var Hom) : Components.Atom Var Hom → Goal Var Hom
  | .const c => [⟨[.const c], available⟩]
  | .var x =>
    if available.any (fun a => match a with | .const _ => true | .var _ => false) then
      splitVariable roles available x
    else [⟨[.var x], available⟩]

theorem bare_correct (roles : List Hom) (iv : Column Var Hom)
    (supported : ∀ v, Language.Supported roles.toFinset (iv v))
    (available : Expression Var Hom) (required : Components.Atom Var Hom) :
    Holds (bare roles available required) iv ↔
      (atomValue iv required).words ⊆ (value iv available).words := by
  cases required with
  | const c => simp [bare, Holds, inequality_iff]
  | var x =>
    simp only [bare]
    split
    · exact splitVariable_correct roles iv available x (interpret_supported _ iv supported x)
    · simp [Holds, inequality_iff]

def peel (r : Hom) : Shallow Var Hom → Option (Components.Atom Var Hom)
  | .atom a => Components.derivative r a
  | .hom s a => if r = s then some a else none

def atConstant : Shallow Var Hom → Option (Components.Atom Var Hom)
  | .atom a => some a
  | .hom _ _ => none

theorem peel_particle (iv : Column Var Hom) (r : Hom) (p : Shallow Var Hom) :
    value iv (peel r p).toList = Language.derivative r (particleValue iv p) := by
  cases p with
  | atom a =>
    cases a with
    | const c => simp [peel, Components.derivative, atomValue]
    | var x => simp [peel, Components.derivative, atomValue, interpret]
  | hom s a =>
    by_cases eq : r = s <;> simp [peel, eq]

theorem value_filterMap {α : Type*} (iv : Column Var Hom)
    (f : α → Option (Components.Atom Var Hom)) (ps : List α) :
    value iv (ps.filterMap f) = (ps.map (fun p => value iv (f p).toList)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases h : f p <;> simp [h, ih]

theorem peel_eval (iv : Column Var Hom) (r : Hom) (ps : Concept Var Hom) :
    value iv (ps.filterMap (peel r)) = Language.derivative r (eval iv ps) := by
  rw [value_filterMap]
  induction ps with
  | nil => simp
  | cons p ps ih => rw [List.map_cons, List.sum_cons, ih, peel_particle, eval_cons,
      Language.derivative_add]

theorem atConstant_particle (iv : Column Var Hom) (p : Shallow Var Hom) :
    [] ∈ (value iv (atConstant p).toList).words ↔ [] ∈ (particleValue iv p).words := by
  cases p with
  | atom a => simp [atConstant]
  | hom r a => simp only [atConstant, Option.toList_none, value_nil, WordPolynomial.zero_words,
      Finset.notMem_empty, particleValue_hom, Language.mem_prefix, List.nil_eq, reduceCtorEq,
      and_false, exists_false]

theorem atConstant_eval (iv : Column Var Hom) (ps : Concept Var Hom) :
    [] ∈ (value iv (ps.filterMap atConstant)).words ↔ [] ∈ (eval iv ps).words := by
  rw [value_filterMap]
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, WordPolynomial.add_words,
      Finset.mem_union, atConstant_particle, ih, eval_cons]

theorem prefix_subset_iff (r : Hom) (p q : WordPolynomial Hom) :
    (WordPolynomial.generator r * p).words ⊆ q.words ↔ p.words ⊆ (Language.derivative r q).words := by
  constructor
  · intro sub word member
    exact (Language.mem_derivative r q word).mpr (sub ((Language.mem_prefix r p _).mpr ⟨word, member, rfl⟩))
  · intro sub word member
    obtain ⟨tail, ht, rfl⟩ := (Language.mem_prefix r p word).mp member
    exact (Language.mem_derivative r q tail).mp (sub ht)

theorem constantPart_subset_atConstant (iv : Column Var Hom) (ps : Concept Var Hom)
    (p : WordPolynomial Hom) :
    (Language.constantPart p).words ⊆ (value iv (ps.filterMap atConstant)).words ↔
      (Language.constantPart p).words ⊆ (Language.constantPart (eval iv ps)).words := by
  rw [← Language.constantPart_subset_iff]
  constructor <;> intro sub word member
  · have nilWord := ((Language.mem_constantPart p word).mp member).1
    subst word
    exact (atConstant_eval iv ps).mp (sub member)
  · have nilWord := ((Language.mem_constantPart p word).mp member).1
    subst word
    exact (atConstant_eval iv ps).mpr (sub member)

def offending : Shallow Var Hom → Bool
  | .hom _ _ | .atom (.const _) => true
  | .atom (.var _) => false

theorem atConstant_eval_of_flat (iv : Column Var Hom) (ps : Concept Var Hom)
    (flat : ps.any offending = false) : value iv (ps.filterMap atConstant) = eval iv ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have rest : ps.any offending = false := (Bool.or_eq_false_iff.mp flat).2
    cases p with
    | atom a =>
      change atomValue iv a + value iv (ps.filterMap atConstant) = particleValue iv (.atom a) + _
      rw [ih rest, particleValue_atom]
      rfl
    | hom r a => simp [offending] at flat

/-- The three cases of Figure 2. `bare` handles the possible further constant
case after a role is peeled. No recursive worklist or external fuel is needed. -/
def flatten (roles : List Hom) (available : Concept Var Hom) : Shallow Var Hom → Goal Var Hom
  | .hom r a => bare roles (available.filterMap (peel r)) a
  | .atom (.const c) => [⟨[.const c], available.filterMap atConstant⟩]
  | .atom (.var x) =>
    if available.any offending then
      ⟨[.var (.constant x)], available.filterMap atConstant⟩ ::
        roles.flatMap (fun r => bare roles (available.filterMap (peel r)) (.var (.role r x)))
    else [⟨[.var x], available.filterMap atConstant⟩]

/-- Each executable flattening-II rule is an equivalence, with the role
signature condition stated explicitly rather than silently assumed. -/
theorem flatten_correct (roles : List Hom) (iv : Column Var Hom)
    (supported : ∀ v, Language.Supported roles.toFinset (iv v))
    (available : Concept Var Hom) (required : Shallow Var Hom) :
    Holds (flatten roles available required) iv ↔
      (particleValue iv required).words ⊆ (eval iv available).words := by
  cases required with
  | hom r a =>
    rw [flatten, bare_correct roles iv supported, peel_eval, particleValue_hom, prefix_subset_iff]
  | atom a =>
    cases a with
    | const c =>
      simp only [flatten, Holds, List.forall_mem_singleton, inequality_iff, value_singleton,
        atomValue, particleValue_atom, WordPolynomial.one_words, Finset.singleton_subset_iff]
      exact atConstant_eval iv available
    | var x =>
      simp only [flatten]
      split
      next hasOffending =>
        change Holds (_ :: roles.flatMap _) iv ↔ _
        simp only [Holds, List.forall_mem_cons, List.forall_mem_flatMap]
        change _ ∧ (∀ r ∈ roles, Holds (bare roles (available.filterMap (peel r)) (.var (.role r x))) iv) ↔ _
        simp only [bare_correct roles iv supported, inequality_iff, value_singleton, atomValue,
          interpret, peel_eval, particleValue_atom]
        rw [constantPart_subset_atConstant,
          Language.subset_iff_components roles.toFinset _ _ (interpret_supported _ iv supported x)]
        simp only [List.mem_toFinset]
      next noOffending =>
        simp only [Holds, List.forall_mem_singleton, inequality_iff, value_singleton, atomValue,
          particleValue_atom]
        rw [atConstant_eval_of_flat iv available (Bool.eq_false_iff.mpr noOffending)]

@[simp] theorem particleValue_embed (iv : Column Var Hom) (p : Flat.Particle Unit Var Hom) :
    particleValue iv (embed p) = p.eval (fun _ => 1) iv := by
  cases p with
  | atom a => cases a <;> rfl
  | hom r a => cases a <;> rfl

@[simp] theorem eval_embed (iv : Column Var Hom) (ps : Flat.Concept Unit Var Hom) :
    eval iv (ps.map embed) = ps.eval (fun _ => 1) iv := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change particleValue iv (embed p) + eval iv (ps.map embed) = _ + _
    rw [particleValue_embed, ih]

def compile (roles : List Hom) (m : Flat.Model Unit Var Hom) : Goal Var Hom :=
  (Projection.constraints m).flatMap fun q =>
    q.left.flatMap (fun required => flatten roles (q.right.map embed) (embed required))

theorem compile_correct (roles : List Hom) (iv : Column Var Hom)
    (supported : ∀ v, Language.Supported roles.toFinset (iv v)) (m : Flat.Model Unit Var Hom) :
    Holds (compile roles m) iv ↔ m.Holds (fun _ => 1) iv := by
  rw [← Projection.constraints_iff m (fun _ => 1) iv]
  simp only [Holds, compile, List.forall_mem_flatMap]
  change (∀ q ∈ Projection.constraints m, ∀ p ∈ q.left,
    Holds (flatten roles (q.right.map embed) (embed p)) iv) ↔ _
  simp only [flatten_correct roles iv supported, particleValue_embed, eval_embed]
  constructor
  · intro h q hq
    apply WordPolynomial.ext
    apply Finset.union_eq_right.mpr
    intro word member
    have embedded : word ∈ (eval iv (q.left.map embed)).words := by simpa only [eval_embed] using member
    obtain ⟨p, hp, hw⟩ := (mem_eval iv _ word).mp embedded
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hp
    exact h q hq source hs (by simpa only [particleValue_embed] using hw)
  · intro h q hq p hp
    have sub := Finset.union_eq_right.mp (congrArg WordPolynomial.words (h q hq))
    intro word member
    apply sub
    rw [← eval_embed, mem_eval]
    exact ⟨embed p, List.mem_map.mpr ⟨p, hp, rfl⟩, by simpa only [particleValue_embed] using member⟩

end ACUIhE.FILO.FlatteningII
