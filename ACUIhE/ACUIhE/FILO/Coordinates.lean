import ACUIhE.FILO.Solver

/-!
# FILO with prescribed coordinate support

Support restrictions share one finite coordinate alphabet. Each stores its
term once and the allowed coordinates, rather than expanding a pair for every
forbidden coordinate. Outside that alphabet the term remains unrestricted.
-/

namespace ACUIhE.FILO.Coordinates

open ACUIh.Linear

universe u v w

structure System (Const : Type u) (Var : Type v) (Hom : Type w) where
  inequalities : Problem Const Var Hom
  coordinates : List Const
  support : List (ACUIh.Term Const Var Hom × Finset Const)

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

local instance : ACUIh Hom (WordPolynomial Hom) := Column.algebra

def System.IsSolution (s : System Const Var Hom) (m : GroundMatrix Const Var Hom) : Prop :=
  s.inequalities.IsSolution m ∧ ∀ z ∈ s.support, ∀ c ∈ s.coordinates,
    c ∉ z.2 → matrixCoordinates m z.1 c = 0

def System.Unifiable (s : System Const Var Hom) : Prop := ∃ m, s.IsSolution m

def System.at (s : System Const Var Hom) (c : Const) : Problem Const Var Hom :=
  s.inequalities ++ (s.support.filter (fun z => c ∈ s.coordinates ∧ c ∉ z.2)).map
    (fun z => ⟨z.1, .zero⟩)

omit [DecidableEq Var] in
theorem System.at_iff (s : System Const Var Hom) (c : Const) (iv : Column Var Hom) :
    Column.Satisfies (s.at c) c iv ↔ Column.Satisfies s.inequalities c iv ∧
      ∀ z ∈ s.support, c ∈ s.coordinates → c ∉ z.2 → z.1.eval (Column.constant c) iv = 0 := by
  simp only [Column.Satisfies, Problem.Holds, System.at, List.forall_mem_append,
    List.forall_mem_map, List.mem_filter, decide_eq_true_eq, and_imp]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  change z.1.eval (Column.constant c) iv + 0 = 0 ↔ _
  rw [add_zero]

theorem System.isSolution_iff (s : System Const Var Hom) (m : GroundMatrix Const Var Hom) :
    s.IsSolution m ↔ ∀ c, Column.Satisfies (s.at c) c (fun v => m v c) := by
  simp only [System.IsSolution, Column.isSolution_iff, System.at_iff, Column.eval_eq_coordinate]
  constructor
  · rintro ⟨ordinary, support⟩ c
    exact ⟨ordinary c, fun z hz hc missing => support z hz c hc missing⟩
  · intro h
    exact ⟨fun c => (h c).1, fun z hz c hc missing => (h c).2 z hz hc missing⟩

/-- Column completeness holds for every constant, including constants added
solely to express an absent-coordinate condition. -/
theorem column_complete (p : Problem Const Var Hom) (c : Const)
    (iv : Column Var Hom) (h : Column.Satisfies p c iv) :
    ∃ result, solveColumn p c = some result := by
  have compiled : (Preprocessing.compile p c).Solvable := by
    rw [Preprocessing.compile, FlatteningII.normalize_solvable_iff,
      Projection.solvable_compile_iff, FlatteningI.solvable_compile_iff]
    exact ⟨iv, h⟩
  cases hs : solveColumn p c with
  | none => exact ((solveColumn_none_iff p c).mp hs compiled).elim
  | some result => exact ⟨result, rfl⟩

def System.names (s : System Const Var Hom) : List Const :=
  (s.inequalities.constantList ++ s.coordinates).dedup

omit [DecidableEq Var] [DecidableEq Hom] in
@[simp] theorem System.mem_names (s : System Const Var Hom) (c : Const) :
    c ∈ s.names ↔ c ∈ s.inequalities.constantNames ∨ c ∈ s.coordinates := by
  simp [System.names]

theorem System.assemble_solution (s : System Const Var Hom) (columns : Const → Column Var Hom)
    (h : ∀ c ∈ s.names, Column.Satisfies (s.at c) c (columns c)) :
    s.IsSolution (Column.assemble s.names.toFinset columns) := by
  apply (s.isSolution_iff _).mpr
  intro c
  by_cases present : c ∈ s.names
  · have same : (fun v => Column.assemble s.names.toFinset columns v c) = columns c := by
      funext v
      simp [Column.assemble_apply, present]
    rw [same]
    exact h c present
  · have same : (fun v => Column.assemble s.names.toFinset columns v c) = fun _ => 0 := by
      funext v
      simp [Column.assemble_apply, present]
    rw [same, s.at_iff]
    constructor
    · rw [Column.satisfies_iff]
      intro q hq
      have missing : c ∉ Problem.termConstants q.left := by
        intro hc
        exact present ((s.mem_names c).mpr (.inl
          ((Problem.mem_constantNames s.inequalities c).mpr ⟨q, hq, .inl hc⟩)))
      rw [Column.eval_zero_of_absent c q.left missing]
      exact Finset.empty_subset _
    · intro z _ hc _
      exact (present ((s.mem_names c).mpr (.inr hc))).elim

/-- Common flattening and support-term flattenings are independent of the column. -/
structure Prepared (Const : Type u) (Var : Type v) (Hom : Type w) where
  ordinary : Flat.Model Const (Flat.Variable Const Var Hom) Hom
  coordinates : List Const
  support : List (FlatteningI.Result Const Var Hom × Finset Const)

def prepare (s : System Const Var Hom) : Prepared Const Var Hom :=
  ⟨FlatteningI.compile s.inequalities, s.coordinates,
    s.support.map (fun z => (FlatteningI.term z.1, z.2))⟩

@[noinline] def Prepared.at (p : Prepared Const Var Hom) (c : Const) :
    Flat.Model Const (Flat.Variable Const Var Hom) Hom :=
  let selected := p.support.filter (fun z => c ∈ p.coordinates ∧ c ∉ z.2)
  ⟨p.ordinary.inequalities ++ selected.map (fun z => ⟨z.1.body, []⟩),
    p.ordinary.definitions ++ selected.flatMap (fun z => z.1.definitions)⟩

omit [DecidableEq Var] [DecidableEq Hom] in
/-- Exact equality with flattening the unshared column specification. -/
theorem prepare_at_eq (s : System Const Var Hom) (c : Const) :
    (prepare s).at c = FlatteningI.compile (s.at c) := by
  simp only [Prepared.at, prepare, System.at, FlatteningI.compile, List.filter_map,
    List.map_append, List.map_map, List.flatMap_append, List.flatMap_map,
    Function.comp_def, FlatteningI.term, List.append_nil]
  rfl

@[noinline] def Prepared.solveColumn (p : Prepared Const Var Hom) (c : Const) :
    Option (Column Var Hom) := solveFlatColumn (p.at c) c

theorem prepared_solveColumn_eq (s : System Const Var Hom) (c : Const) :
    (prepare s).solveColumn c = solveColumn (s.at c) c := by
  rw [Prepared.solveColumn, prepare_at_eq]
  rfl

@[noinline] def Prepared.collect (p : Prepared Const Var Hom) (names : List Const) :
    Option (List (Const × Column Var Hom)) := ColumnCache.collect p.solveColumn names

def solve (s : System Const Var Hom) : Option (GroundMatrix Const Var Hom) :=
  ((prepare s).collect s.names).map
    (fun cached => Column.assemble s.names.toFinset
      (fun c => (cached.lookup c).getD (fun _ => 0)))

theorem solve_eq (s : System Const Var Hom) : solve s =
    (ColumnCache.collect (fun c => solveColumn (s.at c) c) s.names).map
      (fun cached => Column.assemble s.names.toFinset
        (fun c => (cached.lookup c).getD (fun _ => 0))) := by
  have same : (prepare s).solveColumn = fun c => solveColumn (s.at c) c :=
    funext (prepared_solveColumn_eq s)
  simp only [solve, Prepared.collect, same]

theorem solve_sound (s : System Const Var Hom) {m : GroundMatrix Const Var Hom}
    (h : solve s = some m) : s.IsSolution m := by
  rw [solve_eq] at h
  obtain ⟨cached, found, rfl⟩ := Option.map_eq_some_iff.mp h
  apply s.assemble_solution
  intro c hc
  have lookup := ColumnCache.lookup_collect _ _ (fun _ => (0 : WordPolynomial Hom)) found hc
  rw [lookup]
  have success := (ColumnCache.collect_some _ _ (fun _ => (0 : WordPolynomial Hom)) found).2 c hc
  cases hs : solveColumn (s.at c) c with
  | none => simp [hs] at success
  | some iv => exact solveColumn_sound (s.at c) c hs

theorem solve_complete (s : System Const Var Hom) (h : s.Unifiable) :
    ∃ m, solve s = some m := by
  obtain ⟨m, hm⟩ := h
  have success : ∀ c ∈ s.names, (solveColumn (s.at c) c).isSome = true := by
    intro c _
    obtain ⟨iv, hiv⟩ := column_complete (s.at c) c _ ((s.isSolution_iff m).mp hm c)
    simp [hiv]
  rw [solve_eq]
  rw [ColumnCache.collect_eq _ _ (fun _ => (0 : WordPolynomial Hom)), if_pos success]
  exact ⟨_, rfl⟩

theorem solve_none_iff (s : System Const Var Hom) : solve s = none ↔ ¬ s.Unifiable := by
  constructor
  · intro failed solution
    obtain ⟨m, found⟩ := solve_complete s solution
    rw [failed] at found
    cases found
  · intro absent
    cases found : solve s with
    | none => rfl
    | some m => exact (absent ⟨m, solve_sound s found⟩).elim

end ACUIhE.FILO.Coordinates
