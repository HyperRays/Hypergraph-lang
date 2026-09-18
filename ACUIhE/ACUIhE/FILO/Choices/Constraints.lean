import ACUIhE.FILO.Goal.Requirement

/-!
# Necessary finite status constraints

These clauses express consequences of the actual word requirements and of
component consistency. They are used for propagation, never as a replacement
for the word solver. Every genuine solution satisfies every compiled clause.
-/

namespace ACUIhE.FILO.Choices

open Components ACUIh.Linear Goal

universe v w
variable {Var : Type v} {Hom : Type w}

structure Literal (Var : Type v) (Hom : Type w) where
  atom : Atom Var Hom
  allowed : List Status

abbrev Clause (Var : Type v) (Hom : Type w) := List (Literal Var Hom)

def Literal.Holds (c : Choice Var Hom) (l : Literal Var Hom) : Prop :=
  atomStatus c l.atom ∈ l.allowed

def Clause.Holds (c : Choice Var Hom) (q : Clause Var Hom) : Prop :=
  ∃ l ∈ q, l.Holds c

/-- Contradictions made solely of literal constants need no variable setup. -/
def Literal.Feasible (l : Literal Var Hom) : Prop :=
  match l.atom with
  | .const _ => .constant ∈ l.allowed
  | .var _ => l.allowed ≠ []

instance (l : Literal Var Hom) : Decidable l.Feasible := by
  unfold Literal.Feasible
  split <;> infer_instance

def Clause.Feasible (q : Clause Var Hom) : Prop := ∃ l ∈ q, l.Feasible

instance (q : Clause Var Hom) : Decidable q.Feasible :=
  inferInstanceAs (Decidable (∃ l ∈ q, l.Feasible))

theorem Clause.feasible_of_holds (c : Choice Var Hom) (q : Clause Var Hom) (h : q.Holds c) :
    q.Feasible := by
  obtain ⟨l, hl, holds⟩ := h
  refine ⟨l, hl, ?_⟩
  cases he : l.atom with
  | const a => simpa only [Literal.Feasible, Literal.Holds, he, atomStatus] using holds
  | var x =>
    simp only [Literal.Feasible, he]
    intro empty
    simp [Literal.Holds, empty] at holds

def Literal.is (x : Variable Var Hom) (k : Status) : Literal Var Hom := ⟨.var x, [k]⟩
def Literal.isNot (x : Variable Var Hom) (k : Status) : Literal Var Hom :=
  ⟨.var x, statuses.filter (· != k)⟩

@[simp] theorem Literal.holds_is (c : Choice Var Hom) (x : Variable Var Hom) (k : Status) :
    (Literal.is x k).Holds c ↔ c x = k := by simp [Literal.is, Literal.Holds, atomStatus]

@[simp] theorem Literal.holds_isNot (c : Choice Var Hom) (x : Variable Var Hom) (k : Status) :
    (Literal.isNot x k).Holds c ↔ c x ≠ k := by
  simp [Literal.isNot, Literal.Holds, atomStatus]

@[simp] theorem Clause.holds_cons (c : Choice Var Hom) (l : Literal Var Hom) (q : Clause Var Hom) :
    Clause.Holds c (l :: q) ↔ l.Holds c ∨ q.Holds c := by simp [Clause.Holds]

@[simp] theorem Clause.holds_nil (c : Choice Var Hom) :
    Clause.Holds c ([] : Clause Var Hom) ↔ False := by simp [Clause.Holds]

variable [DecidableEq Var] [DecidableEq Hom]

/-- A nonempty word cannot be supplied by a literal constant. -/
def nonliteralProviders (q : Requirement Var Hom) : Clause Var Hom :=
  q.available.filterMap (fun a => match a with
    | .const _ => none
    | .var x => some ⟨.var x, [.constant, .nothing]⟩)

/-- Empty-word membership, nonemptiness, and a nonempty word each need a provider. -/
def requirementClauses (q : Requirement Var Hom) : List (Clause Var Hom) :=
  [⟨q.required, [.top, .nothing]⟩ :: q.available.map (fun a => ⟨a, [.constant]⟩),
   ⟨q.required, [.top]⟩ :: q.available.map (fun a => ⟨a, [.constant, .nothing]⟩),
   ⟨q.required, [.top, .constant]⟩ :: nonliteralProviders q]

omit [DecidableEq Var] in
@[simp] theorem atomStatus_ofAssignment (iv : Column Var Hom) (a : Atom Var Hom) :
    atomStatus (ofAssignment iv) a = classify (atomValue iv a) := by
  cases a with
  | var x => rfl
  | const a => simp [atomStatus, atomValue, classify]

omit [DecidableEq Var] in
theorem requirementClauses_sound (q : Requirement Var Hom) (iv : Column Var Hom)
    (h : q.Holds iv) : ∀ r ∈ requirementClauses q, r.Holds (ofAssignment iv) := by
  have constant :
      Clause.Holds (ofAssignment iv) (⟨q.required, [.top, .nothing]⟩ ::
        q.available.map (fun a => (⟨a, [.constant]⟩ : Literal Var Hom))) := by
    by_cases hc : classify (atomValue iv q.required) = .constant
    · obtain ⟨a, ha, hw⟩ := h [] ((classify_constant _).mp hc)
      apply (Clause.holds_cons _ _ _).mpr
      right
      refine ⟨⟨a, [.constant]⟩, List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      simpa [Literal.Holds] using (classify_constant _).mpr hw
    · apply (Clause.holds_cons _ _ _).mpr
      left
      simp only [Literal.Holds, atomStatus_ofAssignment, List.mem_cons]
      cases hs : classify (atomValue iv q.required) <;> simp_all
  have nonempty :
      Clause.Holds (ofAssignment iv) (⟨q.required, [.top]⟩ ::
        q.available.map (fun a => (⟨a, [.constant, .nothing]⟩ : Literal Var Hom))) := by
    by_cases ht : classify (atomValue iv q.required) = .top
    · exact (Clause.holds_cons _ _ _).mpr (.inl (by simpa [Literal.Holds] using ht))
    · have ne : (atomValue iv q.required).words ≠ ∅ := fun hz => ht ((classify_top _).mpr hz)
      obtain ⟨word, hw⟩ := Finset.nonempty_iff_ne_empty.mpr ne
      obtain ⟨a, ha, hw⟩ := h word hw
      have live : classify (atomValue iv a) ≠ .top := by
        intro top
        simp [(classify_top _).mp top] at hw
      apply (Clause.holds_cons _ _ _).mpr
      right
      refine ⟨⟨a, [.constant, .nothing]⟩, List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      simp only [Literal.Holds, atomStatus_ofAssignment, List.mem_cons]
      cases hs : classify (atomValue iv a) <;> simp_all
  have nonliteral : Clause.Holds (ofAssignment iv)
      (⟨q.required, [.top, .constant]⟩ :: nonliteralProviders q) := by
    by_cases hn : classify (atomValue iv q.required) = .nothing
    · obtain ⟨ne, noEmpty⟩ := (classify_nothing _).mp hn
      obtain ⟨word, hw⟩ := Finset.nonempty_iff_ne_empty.mpr ne
      obtain ⟨a, ha, member⟩ := h word hw
      cases a with
      | const a =>
        have eq : word = [] := by simpa [atomValue] using member
        exact False.elim (noEmpty (eq ▸ hw))
      | var x =>
        apply (Clause.holds_cons _ _ _).mpr
        right
        refine ⟨⟨.var x, [.constant, .nothing]⟩,
          List.mem_filterMap.mpr ⟨.var x, ha, rfl⟩, ?_⟩
        have live : classify (interpret iv x) ≠ .top := by
          intro top
          simp [atomValue, (classify_top _).mp top] at member
        simp only [Literal.Holds, atomStatus_ofAssignment, atomValue]
        cases hs : classify (interpret iv x) <;> simp_all
    · apply (Clause.holds_cons _ _ _).mpr
      left
      simp only [Literal.Holds, atomStatus_ofAssignment]
      cases hs : classify (atomValue iv q.required) <;> simp_all
  intro r hr
  simp only [requirementClauses, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact constant
  · exact nonempty
  · exact nonliteral

def parentClauses (s : System Var Hom) : Variable Var Hom → List (Clause Var Hom)
  | .base _ => []
  | .role r p =>
      [[Literal.isNot p .top, Literal.is (.role r p) .top]] ++
      (if r ∉ s.roles then [[Literal.is (.role r p) .top]] else []) ++
      (match p with | .constant _ => [[Literal.is (.role r p) .top]] | _ => [])
  | .constant p =>
      [[Literal.isNot (.constant p) .nothing],
       [Literal.isNot (.constant p) .constant, Literal.is p .constant],
       [Literal.isNot p .constant, Literal.is (.constant p) .constant]]

omit [DecidableEq Var] in
theorem parentClauses_sound (s : System Var Hom) (c : Choice Var Hom) (x : Variable Var Hom)
    (h : ConsistentAt s c x) : ∀ q ∈ parentClauses s x, q.Holds c := by
  cases x with
  | base v => simp [parentClauses]
  | constant p =>
    simp only [ConsistentAt] at h
    simp only [parentClauses, List.forall_mem_cons,
      Clause.holds_cons, Clause.holds_nil, or_false, Literal.holds_is, Literal.holds_isNot]
    tauto
  | role r p =>
    cases p <;> simp only [ConsistentAt] at h <;>
      simp only [parentClauses, List.forall_mem_append, List.forall_mem_singleton,
        Clause.holds_cons, Clause.holds_nil, or_false, Literal.holds_is, Literal.holds_isNot]
    all_goals split_ifs <;> simp_all <;> tauto

def clauses (s : System Var Hom) : List (Clause Var Hom) :=
  s.names.flatMap (parentClauses s) ++ (requirements s.flat).flatMap requirementClauses

theorem clauses_sound (s : System Var Hom) (iv : Column Var Hom) (h : s.Solution iv) :
    ∀ q ∈ clauses s, q.Holds (ofAssignment iv) := by
  intro q hq
  rcases List.mem_append.mp hq with hp | hr
  · obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hp
    exact parentClauses_sound s _ x (ofAssignment_consistent s iv h.1 x hx) q hq
  · obtain ⟨r, hr, hq⟩ := List.mem_flatMap.mp hr
    exact requirementClauses_sound r iv ((holds_requirements _ _).mp h.2 r hr) q hq

end ACUIhE.FILO.Choices
