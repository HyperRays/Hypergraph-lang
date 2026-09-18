import ACUIhE.FILO.Preprocessing
import ACUIhE.FILO.GenericSolver

/-!
# The proved ACUIh solver

Success returns an ordinary ground substitution matrix. Failure is equivalent
to non-unifiability of the original input, not just failure at a chosen depth.
The solver contains no output-validation pass or correctness parameter.
-/

namespace ACUIhE.FILO

open ACUIh.Linear

universe u v w

namespace ColumnCache

universe k l

variable {Key : Type k} {Value : Type l}

/-- Evaluate each requested column once, retaining its result. Failure stops
the traversal immediately. The public caller supplies duplicate-free keys. -/
def collect (compute : Key → Option Value) : List Key → Option (List (Key × Value))
  | [] => some []
  | key :: rest =>
      match compute key with
      | none => none
      | some value => (collect compute rest).map (fun cached => (key, value) :: cached)

/-- Exact value semantics of the cache, not just preservation of solvability.
The expression on the right is a specification, not an executable fallback. -/
theorem collect_eq (compute : Key → Option Value) (keys : List Key) (fallback : Value) :
    collect compute keys =
      if ∀ key ∈ keys, (compute key).isSome = true then
        some (keys.map (fun key => (key, (compute key).getD fallback)))
      else none := by
  induction keys with
  | nil => simp [collect]
  | cons key rest ih =>
    cases h : compute key with
    | none => simp [collect, h]
    | some value => simp [collect, h, ih]

variable [DecidableEq Key]

theorem lookup_map (keys : List Key) (values : Key → Value) (key : Key) :
    (keys.map (fun k => (k, values k))).lookup key =
      if key ∈ keys then some (values key) else none := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    by_cases eq : key = k
    · subst k; simp
    · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr eq, eq, ih]

omit [DecidableEq Key] in
/-- Stored entries are precisely the requested columns, in traversal order. -/
theorem collect_some (compute : Key → Option Value) (keys : List Key) (fallback : Value)
    {cached : List (Key × Value)} (h : collect compute keys = some cached) :
    cached = keys.map (fun key => (key, (compute key).getD fallback)) ∧
      ∀ key ∈ keys, (compute key).isSome = true := by
  rw [collect_eq compute keys fallback] at h
  split at h
  · exact ⟨(Option.some.inj h).symm, by assumption⟩
  · cases h

/-- Cache reads on requested keys recover the exact original result. -/
theorem lookup_collect (compute : Key → Option Value) (keys : List Key) (fallback : Value)
    {cached : List (Key × Value)} (h : collect compute keys = some cached)
    {key : Key} (member : key ∈ keys) : cached.lookup key = compute key := by
  obtain ⟨rfl, success⟩ := collect_some compute keys fallback h
  rw [lookup_map, if_pos member]
  have found := success key member
  cases hk : compute key with
  | none => simp [hk] at found
  | some value => rfl

omit [DecidableEq Key] in
theorem keys_collect (compute : Key → Option Value) (keys : List Key) (fallback : Value)
    {cached : List (Key × Value)} (h : collect compute keys = some cached) :
    cached.map Prod.fst = keys := by
  rw [(collect_some compute keys fallback h).1]
  simp [Function.comp_def]

end ColumnCache

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

local instance : ACUIh Hom (WordPolynomial Hom) := Column.algebra

omit [DecidableEq Var] in
theorem Preprocessing.column_sound (p : Problem Const Var Hom) (c : Const)
    (iv : Column (Flat.Variable Const Var Hom) Hom) (h : (compile p c).Solution iv) :
    Column.Satisfies p c (fun v => iv (.user v)) := by
  have flat := (FlatteningII.compile_correct _ iv h.1
    (Projection.compile (FlatteningI.compile p) c)).mp h.2
  have model := (Projection.holds_compile_iff (FlatteningI.compile p) c 1 iv).mp flat
  exact FlatteningI.compile_sound p (Column.constant c) iv model

/-- The common flattening is supplied as data, outside the column callback. -/
@[noinline] def solveFlatColumn (flat : Flat.Model Const (Flat.Variable Const Var Hom) Hom)
    (c : Const) : Option (Column Var Hom) :=
  (GenericSolver.solve (FlatteningII.normalize (Projection.compile flat c))).map
    (fun iv v => iv (.user v))

def solveColumn (p : Problem Const Var Hom) (c : Const) : Option (Column Var Hom) :=
  solveFlatColumn (FlatteningI.compile p) c

theorem solveColumn_sound (p : Problem Const Var Hom) (c : Const) {iv : Column Var Hom}
    (h : solveColumn p c = some iv) : Column.Satisfies p c iv := by
  unfold solveColumn solveFlatColumn at h
  change (GenericSolver.solve (Preprocessing.compile p c)).map (fun iv v => iv (.user v)) = some iv at h
  cases hs : GenericSolver.solve (Preprocessing.compile p c) with
  | none => simp [hs] at h
  | some source =>
    have eq := Option.some.inj (by simpa [hs] using h)
    subst iv
    exact Preprocessing.column_sound p c source (GenericSolver.solve_sound _ hs)

theorem solveColumn_none_iff (p : Problem Const Var Hom) (c : Const) :
    solveColumn p c = none ↔ ¬ (Preprocessing.compile p c).Solvable := by
  simp only [solveColumn, solveFlatColumn, Preprocessing.compile,
    Option.map_eq_none_iff, GenericSolver.solve_none_iff]

@[noinline] def solveFlatColumns (flat : Flat.Model Const (Flat.Variable Const Var Hom) Hom)
    (names : List Const) : Option (List (Const × Column Var Hom)) :=
  ColumnCache.collect (solveFlatColumn flat) names

/-- Solve the duplicate-free constant list once and retain every successful
column. No cache is returned if any required column fails. -/
def solveColumns (p : Problem Const Var Hom) : Option (List (Const × Column Var Hom)) :=
  solveFlatColumns (FlatteningI.compile p) p.constantList

theorem solveColumns_lookup (p : Problem Const Var Hom)
    {cached : List (Const × Column Var Hom)} (h : solveColumns p = some cached)
    {c : Const} (member : c ∈ p.constantNames) : cached.lookup c = solveColumn p c :=
  ColumnCache.lookup_collect _ _ (fun _ => 0) h ((Problem.mem_constantList p c).mpr member)

theorem solveColumns_keys (p : Problem Const Var Hom)
    {cached : List (Const × Column Var Hom)} (h : solveColumns p = some cached) :
    cached.map Prod.fst = p.constantList :=
  ColumnCache.keys_collect _ _ (fun _ => 0) h

theorem solveColumns_nodup (p : Problem Const Var Hom)
    {cached : List (Const × Column Var Hom)} (h : solveColumns p = some cached) :
    (cached.map Prod.fst).Nodup := by
  rw [solveColumns_keys p h]
  exact p.constantList_nodup

/-- All constant columns must succeed. Matrix reads use only cached results,
never the problem or a search callback. Absent input constants have zero columns. -/
def solve (p : Problem Const Var Hom) : Option (GroundMatrix Const Var Hom) :=
  let names := p.constantNames
  (solveColumns p).map (fun cached =>
    Column.assemble names (fun c => (cached.lookup c).getD (fun _ => 0)))

/-- Caching preserves exactly the previous wrapper's result, including every
matrix coordinate. This uncached expression occurs only in the theorem. -/
theorem solve_eq_uncached (p : Problem Const Var Hom) :
    solve p =
      if ∀ c ∈ p.constantNames, (solveColumn p c).isSome = true then
        some (Column.assemble p.constantNames (fun c => (solveColumn p c).getD (fun _ => 0)))
      else none := by
  unfold solve solveColumns solveFlatColumns
  change (ColumnCache.collect (solveColumn p) p.constantList).map
    (fun cached => Column.assemble p.constantNames
      (fun c => (cached.lookup c).getD (fun _ => 0))) = _
  rw [ColumnCache.collect_eq _ _ (fun _ => 0)]
  simp only [Problem.mem_constantList]
  split
  · simp only [Option.map_some]
    apply congrArg some
    funext v
    apply Finsupp.ext
    intro c
    simp only [Column.assemble_apply, ColumnCache.lookup_map, Problem.mem_constantList]
    split <;> simp_all
  · rfl

theorem solve_sound (p : Problem Const Var Hom) {m : GroundMatrix Const Var Hom}
    (h : solve p = some m) : p.IsSolution m := by
  rw [solve_eq_uncached] at h
  split at h
  · rename_i successful
    have eq := Option.some.inj h
    subst m
    apply Column.assemble_solution
    intro c hc
    have success := successful c hc
    cases hs : solveColumn p c with
    | none => simp [hs] at success
    | some iv => simpa [hs] using solveColumn_sound p c hs
  · simp at h

/-- Both positive and negative answers are complete for the original problem. -/
theorem solve_none_iff (p : Problem Const Var Hom) : solve p = none ↔ ¬ p.Unifiable := by
  constructor
  · intro h unifiable
    have columns := (Preprocessing.unifiable_iff p).mp unifiable
    have success : ∀ c ∈ p.constantNames, (solveColumn p c).isSome = true := by
      intro c hc
      cases hs : solveColumn p c with
      | none => exact False.elim ((solveColumn_none_iff p c).mp hs (columns c hc))
      | some iv => rfl
    rw [solve_eq_uncached] at h
    rw [if_pos success] at h
    cases h
  · intro no
    cases hs : solve p with
    | none => rfl
    | some m => exact False.elim (no ⟨m, solve_sound p hs⟩)

theorem solve_complete (p : Problem Const Var Hom) (h : p.Unifiable) :
    ∃ m, solve p = some m := by
  cases hs : solve p with
  | none => exact False.elim ((solve_none_iff p).mp hs h)
  | some m => exact ⟨m, rfl⟩

/-- Decision-only entry point: skip reconstruction when no matrix is requested. -/
@[noinline] def checkFlatColumns (flat : Flat.Model Const (Flat.Variable Const Var Hom) Hom)
    (names : List Const) : Bool :=
  decide (∀ c ∈ names,
    (GenericSolver.search (FlatteningII.normalize (Projection.compile flat c))).isSome = true)

def isUnifiable (p : Problem Const Var Hom) : Bool :=
  checkFlatColumns (FlatteningI.compile p) p.constantList

theorem isUnifiable_iff (p : Problem Const Var Hom) : isUnifiable p = true ↔ p.Unifiable := by
  simp only [isUnifiable, checkFlatColumns, decide_eq_true_eq, GenericSolver.search_isSome_iff,
    Problem.mem_constantList]
  exact (Preprocessing.unifiable_iff p).symm

instance (p : Problem Const Var Hom) : Decidable p.Unifiable :=
  decidable_of_iff (isUnifiable p = true) (isUnifiable_iff p)

end ACUIhE.FILO
