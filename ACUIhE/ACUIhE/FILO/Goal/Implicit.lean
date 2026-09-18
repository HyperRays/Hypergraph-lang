import ACUIhE.FILO.Goal.Requirement

/-! # Figure 3: the implicit solver

Critical rules 5, 7, and 8 run before rules 1–4 and 6 simplify the goal.
An empty returned list is rule 9's success case, not a search placeholder.
-/

namespace ACUIhE.FILO.Goal.Implicit

open Components ACUIh.Linear Choices

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def HasConstant (c : Choice Var Hom) (available : Expression Var Hom) : Prop :=
  ∃ a ∈ available, atomStatus c a = .constant

instance (c : Choice Var Hom) (available : Expression Var Hom) : Decidable (HasConstant c available) :=
  inferInstanceAs (Decidable (∃ a ∈ available, atomStatus c a = .constant))

def live (c : Choice Var Hom) (available : Expression Var Hom) : Expression Var Hom :=
  available.filter (fun a => atomStatus c a != .top)

def ActiveChild (s : System Var Hom) (c : Choice Var Hom) (required : Atom Var Hom) : Prop :=
  ∃ y ∈ s.names, match y with
    | .role _ p => required = .var p ∧ c y ≠ .top
    | _ => False

instance (s : System Var Hom) (c : Choice Var Hom) (required : Atom Var Hom) :
    Decidable (ActiveChild s c required) := by
  letI : DecidablePred (fun y : Variable Var Hom => match y with
    | .role _ p => required = .var p ∧ c y ≠ .top
    | _ => False) := fun y => by cases y <;> infer_instance
  unfold ActiveChild
  infer_instance

def Fails (s : System Var Hom) (c : Choice Var Hom) (q : Requirement Var Hom) : Prop :=
  (atomStatus c q.required = .constant ∧ ¬ HasConstant c q.available) ∨
  (atomStatus c q.required ≠ .top ∧ live c q.available = []) ∨
  ((∀ a ∈ live c q.available, a = .const ()) ∧ atomStatus c q.required ≠ .top ∧
    (atomStatus c q.required = .nothing ∨ ActiveChild s c q.required))

instance (s : System Var Hom) (c : Choice Var Hom) (q : Requirement Var Hom) :
    Decidable (Fails s c q) :=
  inferInstanceAs (Decidable ((atomStatus c q.required = .constant ∧ ¬ HasConstant c q.available) ∨
    (atomStatus c q.required ≠ .top ∧ live c q.available = []) ∨
    ((∀ a ∈ live c q.available, a = .const ()) ∧ atomStatus c q.required ≠ .top ∧
      (atomStatus c q.required = .nothing ∨ ActiveChild s c q.required))))

def Solved (c : Choice Var Hom) (q : Requirement Var Hom) : Prop :=
  atomStatus c q.required = .top ∨ q.required ∈ q.available ∨
    (q.required = .const () ∧ HasConstant c q.available)

instance (c : Choice Var Hom) (q : Requirement Var Hom) : Decidable (Solved c q) :=
  inferInstanceAs (Decidable (atomStatus c q.required = .top ∨ q.required ∈ q.available ∨
    (q.required = .const () ∧ HasConstant c q.available)))

def providers (c : Choice Var Hom) (q : Requirement Var Hom) : Expression Var Hom :=
  q.available.filter (fun a => decide
    (atomStatus c a ≠ .top ∧ (a ≠ .const () ∨ atomStatus c q.required = .constant)))

def simplify (c : Choice Var Hom) (q : Requirement Var Hom) : List (Requirement Var Hom) :=
  if Solved c q then [] else [⟨q.required, providers c q⟩]

def reduce (s : System Var Hom) (c : Choice Var Hom) : Option (List (Requirement Var Hom)) :=
  let qs := requirements s.flat
  if ∃ q ∈ qs, Fails s c q then none else some (qs.flatMap (simplify c))

/-- Pointwise facts needed by the simplification rules. -/
def FitsAtom (c : Choice Var Hom) (initial : Bool) (member : Atom Var Hom → Prop)
    (a : Atom Var Hom) : Prop :=
  (atomStatus c a = .top → ¬ member a) ∧
  (initial = true → (member a ↔ atomStatus c a = .constant)) ∧
  (a = .const () → (member a ↔ initial = true))

def Fits (c : Choice Var Hom) (initial : Bool) (member : Atom Var Hom → Prop)
    (q : Requirement Var Hom) : Prop :=
  ∀ a ∈ q.required :: q.available, FitsAtom c initial member a

omit [DecidableEq Var] [DecidableEq Hom] in
theorem solved_present (c : Choice Var Hom) (initial : Bool) (member : Atom Var Hom → Prop)
    (q : Requirement Var Hom) (fits : Fits c initial member q) (solved : Solved c q) :
    q.Present member := by
  intro required
  rcases solved with top | same | ⟨literal, a, ha, constant⟩
  · exact False.elim (fits q.required (by simp) |>.1 top required)
  · exact ⟨q.required, same, required⟩
  · have atRoot := (fits q.required (by simp) |>.2.2 literal).mp required
    exact ⟨a, ha, (fits a (by simp [ha]) |>.2.1 atRoot).mpr constant⟩

theorem providers_correct (c : Choice Var Hom) (initial : Bool) (member : Atom Var Hom → Prop)
    (q : Requirement Var Hom) (fits : Fits c initial member q) (hr : member q.required) :
    (∃ a ∈ q.available, member a) ↔ ∃ a ∈ providers c q, member a := by
  constructor
  · rintro ⟨a, ha, hm⟩
    refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hm⟩
    apply decide_eq_true
    refine ⟨fun ht => fits a (by simp [ha]) |>.1 ht hm, ?_⟩
    by_cases literal : a = .const ()
    · right
      have atRoot := (fits a (by simp [ha]) |>.2.2 literal).mp hm
      exact (fits q.required (by simp) |>.2.1 atRoot).mp hr
    · exact .inl literal
  · rintro ⟨a, ha, hm⟩
    exact ⟨a, (List.mem_filter.mp ha).1, hm⟩

theorem simplify_correct (c : Choice Var Hom) (initial : Bool) (member : Atom Var Hom → Prop)
    (q : Requirement Var Hom) (fits : Fits c initial member q) :
    q.Present member ↔ ∀ r ∈ simplify c q, r.Present member := by
  unfold simplify
  split
  · rename_i solved
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    exact solved_present c initial member q fits solved
  · simp only [List.forall_mem_singleton, Requirement.Present]
    exact forall_congr' (fun hr => providers_correct c initial member q fits hr)

theorem reduce_some_correct (s : System Var Hom) (c : Choice Var Hom)
    {result : List (Requirement Var Hom)} (h : reduce s c = some result)
    (initial : Bool) (member : Atom Var Hom → Prop)
    (fits : ∀ q ∈ requirements s.flat, Fits c initial member q) :
    (∀ q ∈ requirements s.flat, q.Present member) ↔ ∀ q ∈ result, q.Present member := by
  unfold reduce at h
  dsimp only at h
  split at h
  · cases h
  · have eq := Option.some.inj h
    subst result
    simp only [List.forall_mem_flatMap]
    exact forall_congr' (fun q => forall_congr' (fun hq => simplify_correct c initial member q (fits q hq)))

theorem status_of_classifies (s : System Var Hom) (c : Choice Var Hom) (iv : Column Var Hom)
    (hc : Classifies s c iv) {q : Requirement Var Hom} (hq : q ∈ requirements s.flat)
    {a : Atom Var Hom} (ha : a ∈ q.required :: q.available) :
    atomStatus c a = classify (atomValue iv a) := by
  cases a with
  | const label => simp [atomStatus, atomValue, classify]
  | var x =>
    exact hc x (requirement_names s hq (List.mem_cons.mp ha))

theorem fails_impossible (s : System Var Hom) (c : Choice Var Hom) (iv : Column Var Hom)
    (solution : s.Solution iv) (hc : Classifies s c iv)
    {q : Requirement Var Hom} (hq : q ∈ requirements s.flat) : ¬ Fails s c q := by
  have holds := (holds_requirements _ _).mp solution.2 q hq
  have status : ∀ {a : Atom Var Hom}, a ∈ q.required :: q.available →
      atomStatus c a = classify (atomValue iv a) :=
    fun {_} ha => status_of_classifies s c iv hc hq ha
  have live_provider : ∀ word, word ∈ (atomValue iv q.required).words →
      ∃ a ∈ live c q.available, word ∈ (atomValue iv a).words := by
    intro word hw
    obtain ⟨a, ha, hm⟩ := holds word hw
    refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hm⟩
    have notTop : atomStatus c a ≠ .top := by
      rw [status (by simp [ha])]
      intro top
      have empty := (classify_top _).mp top
      rw [empty] at hm
      exact Finset.notMem_empty _ hm
    simpa using notTop
  have requiredStatus := status (a := q.required) (by simp)
  rintro (⟨constant, noProvider⟩ | ⟨notTop, empty⟩ | ⟨onlyConstant, notTop, tail⟩)
  · apply noProvider
    have hw : [] ∈ (atomValue iv q.required).words :=
      (classify_constant _).mp (requiredStatus ▸ constant)
    obtain ⟨a, ha, hm⟩ := holds [] hw
    exact ⟨a, ha, (status (by simp [ha])).trans ((classify_constant _).mpr hm)⟩
  · have nonempty : (atomValue iv q.required).words.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      exact fun hz => notTop (requiredStatus.trans ((classify_top _).mpr hz))
    obtain ⟨word, hw⟩ := nonempty
    obtain ⟨a, ha, _⟩ := live_provider word hw
    simp [empty] at ha
  · have onlyNil : ∀ word ∈ (atomValue iv q.required).words, word = [] := by
      intro word hw
      obtain ⟨a, ha, hm⟩ := live_provider word hw
      simpa [onlyConstant a ha, atomValue] using hm
    rcases tail with nothing | ⟨y, hy, active⟩
    · obtain ⟨nonempty, noConstant⟩ := (classify_nothing _).mp (requiredStatus ▸ nothing)
      obtain ⟨word, hw⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
      exact noConstant (onlyNil word hw ▸ hw)
    · cases y with
      | base v | constant p => exact active
      | role r p =>
        obtain ⟨required, notTop⟩ := active
        have ne : (interpret iv (.role r p)).words ≠ ∅ := by
          intro hz
          exact notTop ((hc _ hy).trans ((classify_top _).mpr hz))
        obtain ⟨word, hw⟩ := Finset.nonempty_iff_ne_empty.mpr ne
        have member := (Language.mem_derivative r (interpret iv p) word).mp hw
        have impossible := onlyNil (r :: word) (by simpa [required, atomValue] using member)
        cases impossible

theorem reduce_complete (s : System Var Hom) (c : Choice Var Hom) (iv : Column Var Hom)
    (solution : s.Solution iv) (hc : Classifies s c iv) :
    ∃ result, reduce s c = some result := by
  have noFail : ¬ ∃ q ∈ requirements s.flat, Fails s c q := by
    rintro ⟨q, hq, fail⟩
    exact fails_impossible s c iv solution hc hq fail
  exact ⟨(requirements s.flat).flatMap (simplify c), by simp only [reduce, if_neg noFail]⟩

end ACUIhE.FILO.Goal.Implicit
