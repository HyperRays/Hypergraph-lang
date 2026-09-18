import ACUIhE.FILO.Problem

/-!
# Verified constant decomposition (§4.3, Lemma 2)

Each column is interpreted directly in the existing finite-word semiring.
Assembly is executable and its correctness is proved, not checked afterward.
Only the finitely many constants occurring in the input need columns.
-/

namespace ACUIhE.FILO

open ACUIh.Linear

universe u v w

abbrev Column (Var : Type v) (Hom : Type w) := Var → WordPolynomial Hom

namespace Column

variable {Const : Type u} {Var : Type v} {Hom : Type w} [DecidableEq Hom]

/-- The semiring's additive structure and multiplication by a role generator. -/
@[instance_reducible] def algebra : ACUIh Hom (WordPolynomial Hom) where
  add := (· + ·)
  zero := 0
  hom r p := WordPolynomial.generator r * p
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  add_idem := WordPolynomial.add_self
  hom_add := fun r p q => mul_add (WordPolynomial.generator r) p q
  hom_zero := fun r => mul_zero (WordPolynomial.generator r)

local instance : ACUIh Hom (WordPolynomial Hom) := algebra

variable [DecidableEq Const]

def constant (c : Const) (d : Const) : WordPolynomial Hom := if d = c then 1 else 0

/-- Truth of one constant column, independent of any search procedure. -/
def Satisfies (p : Problem Const Var Hom) (c : Const) (column : Column Var Hom) : Prop :=
  p.Holds (constant c) column

variable [DecidableEq Var]

/-- Column evaluation is precisely the existing matrix coordinate. -/
theorem eval_eq_coordinate (m : GroundMatrix Const Var Hom) (c : Const)
    (t : ACUIh.Term Const Var Hom) :
    t.eval (constant c) (fun v => m v c) = matrixCoordinates m t c := by
  induction t with
  | zero => simp [ACUIh.Term.eval, matrixCoordinates, variableRow, constantRow]
  | const d =>
    simp only [ACUIh.Term.eval, matrixCoordinates, variableRow, constantRow, rowVecMul_zero,
      Row.add_eq, zero_add, Row.basis_eq, Finsupp.single_apply]
    simp [constant, eq_comm]
  | var v =>
    simp only [ACUIh.Term.eval, matrixCoordinates, variableRow, constantRow, rowVecMul_basis,
      Row.add_eq, add_zero]
  | add a b ia ib =>
    change a.eval (constant c) (fun v => m v c) + b.eval (constant c) (fun v => m v c) = _
    rw [ia, ib]
    simp only [matrixCoordinates, variableRow, constantRow, Row.add_eq, rowVecMul_add,
      Finsupp.add_apply]
    ac_rfl
  | hom r t ih =>
    change WordPolynomial.generator r * t.eval (constant c) (fun v => m v c) = _
    rw [ih]
    simp only [matrixCoordinates, variableRow, constantRow, Row.add_eq, Row.scale_eq,
      rowVecMul_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, mul_add]

omit [DecidableEq Var] in
theorem satisfies_iff (p : Problem Const Var Hom) (c : Const) (column : Column Var Hom) :
    Satisfies p c column ↔ ∀ q ∈ p,
      (q.left.eval (constant c) column).words ⊆ (q.right.eval (constant c) column).words := by
  unfold Satisfies Problem.Holds ACUIh.Inequality.Holds Generic.Inequality.Holds
  constructor
  · intro h q hq
    have sets := congrArg WordPolynomial.words (h q hq)
    exact Finset.union_eq_right.mp sets
  · intro h q hq
    exact WordPolynomial.ext (Finset.union_eq_right.mpr (h q hq))

/-- No constant information is lost by passing from a matrix to its columns. -/
theorem isSolution_iff (p : Problem Const Var Hom) (m : GroundMatrix Const Var Hom) :
    p.IsSolution m ↔ ∀ c, Satisfies p c (fun v => m v c) := by
  simp only [Problem.IsSolution, instantiateNF_subset_iff, satisfies_iff, eval_eq_coordinate]
  exact ⟨fun h c q hq => h q hq c, fun h q hq c => h c q hq⟩

end Column

namespace Problem

variable {Const : Type u} {Var : Type v} {Hom : Type w} [DecidableEq Const]

def termConstants : ACUIh.Term Const Var Hom → Finset Const
  | .zero | .var _ => ∅
  | .const c => {c}
  | .add a b => termConstants a ∪ termConstants b
  | .hom _ t => termConstants t

/-- The finite constant signature, computed from syntax alone. -/
def constantNames (p : Problem Const Var Hom) : Finset Const :=
  p.foldr (fun q names => termConstants q.left ∪ termConstants q.right ∪ names) ∅

/-- A syntax-directed enumeration, avoiding a noncomputable conversion from a finset. -/
def termConstantList : ACUIh.Term Const Var Hom → List Const
  | .zero | .var _ => []
  | .const c => [c]
  | .add a b => termConstantList a ++ termConstantList b
  | .hom _ t => termConstantList t

@[simp] theorem mem_termConstantList (t : ACUIh.Term Const Var Hom) (c : Const) :
    c ∈ termConstantList t ↔ c ∈ termConstants t := by
  induction t <;> simp_all [termConstantList, termConstants]

/-- Each input constant occurs exactly once in the executable column traversal. -/
def constantList (p : Problem Const Var Hom) : List Const :=
  (p.flatMap (fun q => termConstantList q.left ++ termConstantList q.right)).dedup

theorem constantList_nodup (p : Problem Const Var Hom) : p.constantList.Nodup :=
  List.nodup_dedup _

theorem mem_constantNames (p : Problem Const Var Hom) (c : Const) :
    c ∈ p.constantNames ↔ ∃ q ∈ p, c ∈ termConstants q.left ∨ c ∈ termConstants q.right := by
  induction p with
  | nil => simp [constantNames]
  | cons q rest ih =>
    simp only [constantNames, List.foldr_cons, Finset.mem_union]
    change (_ ∨ _) ∨ c ∈ constantNames rest ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

@[simp] theorem mem_constantList (p : Problem Const Var Hom) (c : Const) :
    c ∈ p.constantList ↔ c ∈ p.constantNames := by
  simp only [constantList, List.mem_dedup, List.mem_flatMap, List.mem_append,
    mem_termConstantList, mem_constantNames]

end Problem

namespace Column

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Hom]

local instance : ACUIh Hom (WordPolynomial Hom) := algebra

/-- Assemble a finite family of columns into a sparse matrix; other columns are zero. -/
def assemble (names : Finset Const) (columns : Const → Column Var Hom) : GroundMatrix Const Var Hom :=
  fun v => Row.onSupport names (fun c => if c ∈ names then columns c v else 0) (by
    intro c nonzero
    by_contra absent
    exact nonzero (if_neg absent))

@[simp] theorem assemble_apply (names : Finset Const) (columns : Const → Column Var Hom)
    (v : Var) (c : Const) :
    assemble names columns v c = if c ∈ names then columns c v else 0 := rfl

theorem eval_congr (c : Const) {a b : Column Var Hom} (same : ∀ v, a v = b v)
    (t : ACUIh.Term Const Var Hom) : t.eval (constant c) a = t.eval (constant c) b := by
  exact congrArg (fun iv => t.eval (constant c) iv) (funext same)

theorem eval_zero_of_absent (c : Const) (t : ACUIh.Term Const Var Hom)
    (absent : c ∉ Problem.termConstants t) :
    t.eval (constant c) (fun _ => (0 : WordPolynomial Hom)) = 0 := by
  induction t with
  | zero | var => rfl
  | const d =>
    have ne : d ≠ c := by simpa [Problem.termConstants, eq_comm] using absent
    exact if_neg ne
  | add a b ia ib =>
    have missing := not_or.mp (fun h => absent (Finset.mem_union.mpr h))
    change a.eval (constant c) _ + b.eval (constant c) _ = 0
    rw [ia missing.1, ib missing.2, add_zero]
  | hom r t ih =>
    change WordPolynomial.generator r * t.eval (constant c) _ = 0
    rw [ih absent, mul_zero]

variable [DecidableEq Var]

/-- The constructive direction of constant decomposition. -/
theorem assemble_solution (p : Problem Const Var Hom) (columns : Const → Column Var Hom)
    (solutions : ∀ c ∈ p.constantNames, Satisfies p c (columns c)) :
    p.IsSolution (assemble p.constantNames columns) := by
  apply (isSolution_iff p _).mpr
  intro c
  by_cases present : c ∈ p.constantNames
  · have eq : (fun v => assemble p.constantNames columns v c) = columns c := by
      funext v
      exact if_pos present
    rw [eq]
    exact solutions c present
  · rw [satisfies_iff]
    intro q hq
    have missing : c ∉ Problem.termConstants q.left :=
      fun h => present ((Problem.mem_constantNames p c).mpr ⟨q, hq, .inl h⟩)
    have eq : (fun v => assemble p.constantNames columns v c) = fun _ => 0 := by
      funext v
      exact if_neg present
    rw [eq, eval_zero_of_absent c q.left missing]
    exact Finset.empty_subset _

/-- A unifier exists exactly when each input-constant column has a solution.
Classical choice appears only in the existential proof, not in assembly. -/
theorem unifiable_iff (p : Problem Const Var Hom) :
    p.Unifiable ↔ ∀ c ∈ p.constantNames, ∃ column, Satisfies p c column := by
  constructor
  · rintro ⟨matrix, solution⟩ c _
    exact ⟨fun v => matrix v c, (isSolution_iff p matrix).mp solution c⟩
  · intro solutions
    classical
    let columns : Const → Column Var Hom := fun c =>
      if present : c ∈ p.constantNames then Classical.choose (solutions c present) else fun _ => 0
    refine ⟨assemble p.constantNames columns, assemble_solution p columns ?_⟩
    intro c present
    simpa only [columns, dif_pos present] using Classical.choose_spec (solutions c present)

/-- The no-constant branch is solved by the zero substitution, not by a check. -/
theorem zero_solution (p : Problem Const Var Hom) (empty : p.constantNames = ∅) :
    p.IsSolution (assemble p.constantNames (fun _ _ => 0)) :=
  assemble_solution p _ (by intro c member; simp [empty] at member)

end Column

end ACUIhE.FILO
