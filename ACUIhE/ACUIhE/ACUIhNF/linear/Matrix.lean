import ACUIhE.ACUIhNF.linear.Semimodule
import ACUIhE.ACUIhNF.Completeness
import ACUIhE.Solution
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Matrix.Mul

/-!
# Constant coordinates and substitution matrices for ACUIh

`Row Const Hom` is a finitely supported, constant-indexed row over the
noncommutative semiring `WordPolynomial Hom`. `GroundMatrix Const Var Hom`
has one such row for each variable. Its entries describe ground substitutions;
variables label rows, not additional columns.

The computational definitions explicitly carry finite supports. They do not
use the classical implementations of addition and scalar multiplication on
mathlib's general `Finsupp`; theorems identify them with those operations.
-/

namespace ACUIhE.ACUIh.Linear

universe u v w

/-- A sparse row whose coordinates are indexed by constants. -/
abbrev Row (Const : Type u) (Hom : Type w) := Const →₀ WordPolynomial Hom

/-- A row-finite substitution matrix: variables index rows, constants index columns. -/
abbrev GroundMatrix (Const : Type u) (Var : Type v) (Hom : Type w) := Var → Row Const Hom

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- All homomorphism words attached to a specified particle. -/
def coefficient (normal : NF Const Var Hom) (particle : Particle Const Var) :
    WordPolynomial Hom :=
  ⟨(normal.filter (fun summand => summand.2 = particle)).image Prod.fst⟩

@[simp] theorem mem_coefficient (normal : NF Const Var Hom)
    (particle : Particle Const Var) (word : List Hom) :
    word ∈ (coefficient normal particle).words ↔ (word, particle) ∈ normal := by
  simp only [coefficient, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨w, p⟩, ⟨h, hp⟩, hw⟩
    cases hp
    cases hw
    exact h
  · intro h
    exact ⟨(word, particle), ⟨h, rfl⟩, rfl⟩

@[simp] theorem coefficient_empty (particle : Particle Const Var) :
    coefficient (∅ : NF Const Var Hom) particle = 0 := by
  apply WordPolynomial.ext
  ext word
  simp

theorem coefficient_union (left right : NF Const Var Hom) (particle : Particle Const Var) :
    coefficient (left ∪ right) particle = coefficient left particle + coefficient right particle := by
  apply WordPolynomial.ext
  ext word
  simp

theorem coefficient_act (p : WordPolynomial Hom) (normal : NF Const Var Hom)
    (particle : Particle Const Var) :
    coefficient (act p normal) particle = p * coefficient normal particle := by
  apply WordPolynomial.ext
  ext word
  rw [mem_coefficient, mem_act, WordPolynomial.mul_words, Finset.mem_image₂]
  constructor
  · rintro ⟨u, hu, ⟨v, q⟩, hv, eq⟩
    obtain ⟨hw, hq⟩ := Prod.mk.inj eq
    change q = particle at hq
    subst q
    exact ⟨u, hu, v, (mem_coefficient normal particle v).mpr hv, hw⟩
  · rintro ⟨u, hu, v, hv, hw⟩
    exact ⟨u, hu, (v, particle), (mem_coefficient normal particle v).mp hv,
      congrArg (fun w => (w, particle)) hw⟩

namespace Row

omit [DecidableEq Var] in
/-- Bundle a coordinate function using a known finite bound on its support. -/
def onSupport (support : Finset Const) (f : Const → WordPolynomial Hom)
    (bound : ∀ c, f c ≠ 0 → c ∈ support) : Row Const Hom where
  support := support.filter (fun c => f c ≠ 0)
  toFun := f
  mem_support_toFun c := by simp only [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨bound c h, h⟩⟩

omit [DecidableEq Const] [DecidableEq Var] in
@[simp] theorem onSupport_apply (support : Finset Const) (f : Const → WordPolynomial Hom)
    (bound : ∀ c, f c ≠ 0 → c ∈ support) (c : Const) :
    onSupport support f bound c = f c := rfl

omit [DecidableEq Var] in
/-- Computable row addition. -/
def add (left right : Row Const Hom) : Row Const Hom :=
  onSupport (left.support ∪ right.support) (fun c => left c + right c) (by
    intro c h
    by_contra absent
    have parts := not_or.mp (show ¬ (c ∈ left.support ∨ c ∈ right.support) by simpa using absent)
    exact h (by simp [Finsupp.notMem_support_iff.mp parts.1,
      Finsupp.notMem_support_iff.mp parts.2]))

omit [DecidableEq Var] in
@[simp] theorem add_eq (left right : Row Const Hom) : add left right = left + right := by
  ext c
  rfl

omit [DecidableEq Var] in
/-- Computable left scalar action; the scalar's words are outermost. -/
def scale (p : WordPolynomial Hom) (row : Row Const Hom) : Row Const Hom :=
  onSupport row.support (fun c => p * row c) (by
    intro c h
    by_contra absent
    exact h (by simp [Finsupp.notMem_support_iff.mp absent]))

omit [DecidableEq Var] in
@[simp] theorem scale_eq (p : WordPolynomial Hom) (row : Row Const Hom) :
    scale p row = p • row := by
  ext c
  rfl

omit [DecidableEq Var] in
/-- The basis row for a constant: `1` at that constant and `0` elsewhere. -/
def basis (constant : Const) : Row Const Hom :=
  onSupport {constant} (fun c => if constant = c then 1 else 0) (by
    intro c h
    by_cases eq : constant = c
    · simp [eq]
    · exact False.elim (h (by simp [eq])))

omit [DecidableEq Var] in
@[simp] theorem basis_eq (constant : Const) :
    basis (Hom := Hom) constant = Finsupp.single constant 1 := by
  ext c
  simp [basis, Finsupp.single_apply]

private def constantOfParticle : Particle Const Empty → Const
  | .const c => c
  | .var v => nomatch v

omit [DecidableEq Var] in
/-- Group a ground normal form by its constant particles. -/
def ofNF (normal : NF Const Empty Hom) : Row Const Hom :=
  onSupport (normal.image (fun s => constantOfParticle s.2))
    (fun c => coefficient normal (.const c)) (by
      intro c nonzero
      by_contra absent
      apply nonzero
      apply WordPolynomial.ext
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro word member
      exact absent (Finset.mem_image.mpr
        ⟨(word, .const c), (mem_coefficient normal (.const c) word).mp member, rfl⟩))

omit [DecidableEq Var] in
@[simp] theorem ofNF_apply (normal : NF Const Empty Hom) (c : Const) :
    ofNF normal c = coefficient normal (.const c) := rfl

omit [DecidableEq Var] in
/-- Reconstruct the ground normal form, retaining every coordinate and word. -/
def toNF (row : Row Const Hom) : NF Const Empty Hom :=
  row.support.biUnion (fun c => (row c).words.image (fun word => (word, .const c)))

omit [DecidableEq Var] in
@[simp] theorem mem_toNF (row : Row Const Hom) (word : List Hom) (c : Const) :
    (word, Particle.const c) ∈ row.toNF ↔ word ∈ (row c).words := by
  simp only [toNF, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨c', _, w, hw, eq⟩
    obtain ⟨hwEq, hcEq⟩ := Prod.mk.inj eq
    have hc := Particle.const.inj hcEq
    subst c'
    subst w
    exact hw
  · intro hw
    refine ⟨c, Finsupp.mem_support_iff.mpr ?_, word, hw, rfl⟩
    intro zero
    simp [zero] at hw

omit [DecidableEq Var] in
@[simp] theorem toNF_ofNF (normal : NF Const Empty Hom) : (ofNF normal).toNF = normal := by
  ext ⟨word, particle⟩
  cases particle with
  | const c => simp
  | var v => exact Empty.elim v

omit [DecidableEq Var] in
@[simp] theorem ofNF_toNF (row : Row Const Hom) : ofNF row.toNF = row := by
  ext c word
  simp

omit [DecidableEq Var] in
/-- Constant-coordinate rows and ground ACUIh normal forms are losslessly equivalent. -/
def groundEquiv : NF Const Empty Hom ≃ Row Const Hom where
  toFun := ofNF
  invFun := toNF
  left_inv := toNF_ofNF
  right_inv := ofNF_toNF

omit [DecidableEq Var] in
theorem ofNF_injective : Function.Injective (ofNF (Const := Const) (Hom := Hom)) :=
  groundEquiv.injective

omit [DecidableEq Var] in
@[simp] theorem ofNF_empty : ofNF (∅ : NF Const Empty Hom) = 0 := by
  ext c word
  simp

omit [DecidableEq Var] in
theorem ofNF_union (left right : NF Const Empty Hom) :
    ofNF (left ∪ right) = ofNF left + ofNF right := by
  apply Finsupp.ext
  intro c
  exact coefficient_union left right (.const c)

omit [DecidableEq Var] in
theorem ofNF_act (p : WordPolynomial Hom) (normal : NF Const Empty Hom) :
    ofNF (act p normal) = p • ofNF normal := by
  apply Finsupp.ext
  intro c
  exact coefficient_act p normal (.const c)

omit [DecidableEq Var] in
@[simp] theorem ofNF_prepend (h : Hom) (normal : NF Const Empty Hom) :
    ofNF (NF.prepend h normal) = WordPolynomial.generator h • ofNF normal := by
  rw [← act_generator, ofNF_act]

omit [DecidableEq Var] in
@[simp] theorem ofNF_constant (c : Const) :
    ofNF ({([], .const c)} : NF Const Empty Hom) = basis c := by
  ext d word
  by_cases eq : c = d
  · subst d
    simp
  · simp [Ne.symm eq]

omit [DecidableEq Var] in
/-- Additive comparison of ground normal forms is coordinatewise word-set inclusion. -/
theorem subset_iff (left right : NF Const Empty Hom) :
    left ⊆ right ↔ ∀ c, (ofNF left c).words ⊆ (ofNF right c).words := by
  constructor
  · intro inclusion c word member
    exact (mem_coefficient right (.const c) word).mpr
      (inclusion ((mem_coefficient left (.const c) word).mp member))
  · intro inclusion ⟨word, particle⟩ member
    cases particle with
    | const c =>
        exact (mem_coefficient right (.const c) word).mp
          (inclusion c ((mem_coefficient left (.const c) word).mpr member))
    | var v => exact Empty.elim v

end Row

/-- The ordinary matrix view of a row-finite ground substitution. -/
def GroundMatrix.asMatrix (matrix : GroundMatrix Const Var Hom) :
    Matrix Var Const (WordPolynomial Hom) := fun v c => matrix v c

/-- Sparse row-by-matrix multiplication, with the expression coefficient on the left. -/
def rowVecMul (coefficients : Row Var Hom) (matrix : GroundMatrix Const Var Hom) :
    Row Const Hom :=
  Row.onSupport (coefficients.support.biUnion (fun v => (matrix v).support))
    (fun c => ∑ v ∈ coefficients.support, coefficients v * matrix v c) (by
      intro c nonzero
      by_contra absent
      apply nonzero
      apply Finset.sum_eq_zero
      intro v member
      have missing : c ∉ (matrix v).support := fun hc =>
        absent (Finset.mem_biUnion.mpr ⟨v, member, hc⟩)
      simp [Finsupp.notMem_support_iff.mp missing])

omit [DecidableEq Var] in
@[simp] theorem rowVecMul_apply (coefficients : Row Var Hom)
    (matrix : GroundMatrix Const Var Hom) (c : Const) :
    rowVecMul coefficients matrix c =
      ∑ v ∈ coefficients.support, coefficients v * matrix v c := rfl

omit [DecidableEq Var] in
/-- The computable product agrees with the usual finitely supported linear combination. -/
theorem rowVecMul_eq_sum (coefficients : Row Var Hom) (matrix : GroundMatrix Const Var Hom) :
    rowVecMul coefficients matrix = coefficients.sum (fun v p => p • matrix v) := by
  apply Finsupp.ext
  intro c
  simp [Finsupp.sum]

omit [DecidableEq Var] in
@[simp] theorem rowVecMul_zero (matrix : GroundMatrix Const Var Hom) :
    rowVecMul 0 matrix = 0 := by simp [rowVecMul_eq_sum]

@[simp] theorem rowVecMul_basis (matrix : GroundMatrix Const Var Hom) (v : Var) :
    rowVecMul (Row.basis v) matrix = matrix v := by
  simp [rowVecMul_eq_sum, Finsupp.sum_single_index]

omit [DecidableEq Var] in
theorem rowVecMul_add (left right : Row Var Hom) (matrix : GroundMatrix Const Var Hom) :
    rowVecMul (left + right) matrix = rowVecMul left matrix + rowVecMul right matrix := by
  simp only [rowVecMul_eq_sum]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

omit [DecidableEq Var] in
theorem rowVecMul_smul (p : WordPolynomial Hom) (coefficients : Row Var Hom)
    (matrix : GroundMatrix Const Var Hom) :
    rowVecMul (p • coefficients) matrix = p • rowVecMul coefficients matrix := by
  have transform := Finsupp.sum_smul_index (g := coefficients) (b := p)
    (h := fun v q => q • matrix v) (fun _ => zero_smul _ _)
  simpa only [rowVecMul_eq_sum, Finsupp.sum, mul_smul, Finset.smul_sum] using transform

omit [DecidableEq Var] in
/-- Ordinary matrix multiplication when the variable index type is finite.
No finiteness assumption on the constants is needed. -/
theorem rowVecMul_eq_vecMul [Fintype Var] (coefficients : Row Var Hom)
    (matrix : GroundMatrix Const Var Hom) (c : Const) :
    rowVecMul coefficients matrix c =
      Matrix.vecMul coefficients matrix.asMatrix c := by
  rw [rowVecMul_eq_sum, Finsupp.sum_apply,
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  rfl

omit [DecidableEq Var] in
/-- Even with infinitely many possible variable names, the support gives a finite matrix. -/
theorem rowVecMul_eq_support_vecMul (coefficients : Row Var Hom)
    (matrix : GroundMatrix Const Var Hom) (c : Const) :
    rowVecMul coefficients matrix c =
      Matrix.vecMul (fun v : coefficients.support => coefficients v)
        (fun v : coefficients.support => fun d => matrix v d) c := by
  change (∑ v ∈ coefficients.support, coefficients v * matrix v c) =
    ∑ v : coefficients.support, coefficients v * matrix v c
  exact (Finset.sum_coe_sort _ _).symm

/-- The coefficient row of the variables; constants contribute only to the offset. -/
def variableRow : Term Const Var Hom → Row Var Hom
  | .zero | .const _ => 0
  | .var v => Row.basis v
  | .add left right => Row.add (variableRow left) (variableRow right)
  | .hom h body => Row.scale (WordPolynomial.generator h) (variableRow body)

/-- The constant offset row, including any homomorphism words on constants. -/
def constantRow : Term Const Var Hom → Row Const Hom
  | .zero | .var _ => 0
  | .const c => Row.basis c
  | .add left right => Row.add (constantRow left) (constantRow right)
  | .hom h body => Row.scale (WordPolynomial.generator h) (constantRow body)

/-- Substitute the ground values encoded by the matrix, directly in normal forms. -/
def instantiateNF (matrix : GroundMatrix Const Var Hom) :
    Term Const Var Hom → NF Const Empty Hom
  | .zero => ∅
  | .const c => {([], .const c)}
  | .var v => (matrix v).toNF
  | .add left right => instantiateNF matrix left ∪ instantiateNF matrix right
  | .hom h body => NF.prepend h (instantiateNF matrix body)

/-- The affine matrix expression: variable coefficient row times matrix, plus constant offset. -/
def matrixCoordinates (matrix : GroundMatrix Const Var Hom) (term : Term Const Var Hom) :
    Row Const Hom :=
  Row.add (rowVecMul (variableRow term) matrix) (constantRow term)

/-- The matrix expression is exactly the constant-coordinate vector of the substituted term. -/
theorem ofNF_instantiateNF (matrix : GroundMatrix Const Var Hom) (term : Term Const Var Hom) :
    Row.ofNF (instantiateNF matrix term) = matrixCoordinates matrix term := by
  induction term with
  | zero => simp [instantiateNF, matrixCoordinates, variableRow, constantRow]
  | const c => simp [instantiateNF, matrixCoordinates, variableRow, constantRow]
  | var v =>
      simpa only [instantiateNF, Row.ofNF_toNF, matrixCoordinates, variableRow, constantRow,
        Row.add_eq, _root_.add_zero] using (rowVecMul_basis matrix v).symm
  | add left right ih₁ ih₂ =>
      simp only [instantiateNF, Row.ofNF_union, ih₁, ih₂, matrixCoordinates,
        variableRow, constantRow, Row.add_eq, rowVecMul_add]
      ac_rfl
  | hom h body ih =>
      simp only [instantiateNF, Row.ofNF_prepend, ih, matrixCoordinates,
        variableRow, constantRow, Row.scale_eq, Row.add_eq, rowVecMul_smul, smul_add]

/-- Decoding the matrix result recovers the entire instantiated normal form. -/
@[simp] theorem toNF_matrixCoordinates (matrix : GroundMatrix Const Var Hom)
    (term : Term Const Var Hom) :
    (matrixCoordinates matrix term).toNF = instantiateNF matrix term := by
  rw [← ofNF_instantiateNF, Row.toNF_ofNF]

/-- The precise `p X + b` matrix formula, using ordinary finite matrix multiplication. -/
theorem matrixCoordinates_eq_vecMul [Fintype Var] (matrix : GroundMatrix Const Var Hom)
    (term : Term Const Var Hom) (c : Const) :
    matrixCoordinates matrix term c =
      Matrix.vecMul (variableRow term) matrix.asMatrix c + constantRow term c := by
  change rowVecMul (variableRow term) matrix c + constantRow term c = _
  rw [rowVecMul_eq_vecMul]

/-- The same matrix formula over just the finitely many variable coefficients in the term. -/
theorem matrixCoordinates_eq_support_vecMul (matrix : GroundMatrix Const Var Hom)
    (term : Term Const Var Hom) (c : Const) :
    matrixCoordinates matrix term c =
      Matrix.vecMul (fun v : (variableRow term).support => variableRow term v)
        (fun v : (variableRow term).support => fun d => matrix v d) c + constantRow term c :=
  congrArg (fun p => p + constantRow term c)
    (rowVecMul_eq_support_vecMul (variableRow term) matrix c)

/-- No information is lost by using matrix coordinates to compare ground instances. -/
theorem instantiateNF_eq_iff (matrix : GroundMatrix Const Var Hom)
    (left right : Term Const Var Hom) :
    instantiateNF matrix left = instantiateNF matrix right ↔
      matrixCoordinates matrix left = matrixCoordinates matrix right := by
  rw [← ofNF_instantiateNF, ← ofNF_instantiateNF]
  exact Row.ofNF_injective.eq_iff.symm

/-- Additive inequalities of ground instances are precisely coordinatewise word-set inclusion. -/
theorem instantiateNF_subset_iff (matrix : GroundMatrix Const Var Hom)
    (left right : Term Const Var Hom) :
    instantiateNF matrix left ⊆ instantiateNF matrix right ↔
      ∀ c, (matrixCoordinates matrix left c).words ⊆
        (matrixCoordinates matrix right c).words := by
  rw [Row.subset_iff, ofNF_instantiateNF, ofNF_instantiateNF]

/-- Ground substitution in the raw ACUIh syntax. -/
def substituteGround (substitution : Var → Term Const Empty Hom) :
    Term Const Var Hom → Term Const Empty Hom
  | .zero => .zero
  | .const c => .const c
  | .var v => substitution v
  | .add left right => .add (substituteGround substitution left) (substituteGround substitution right)
  | .hom h body => .hom h (substituteGround substitution body)

/-- The matrix of a raw ground substitution, obtained by normalizing each variable's value. -/
def GroundMatrix.ofSubstitution (substitution : Var → Term Const Empty Hom) :
    GroundMatrix Const Var Hom := fun v => Row.ofNF (substitution v).normalize

omit [DecidableEq Var] in
/-- Matrix instantiation computes the normal form of ordinary raw-term substitution. -/
theorem normalize_substituteGround (substitution : Var → Term Const Empty Hom)
    (term : Term Const Var Hom) :
    (substituteGround substitution term).normalize =
      instantiateNF (GroundMatrix.ofSubstitution substitution) term := by
  induction term with
  | zero | const => rfl
  | var v => simp [substituteGround, instantiateNF, GroundMatrix.ofSubstitution]
  | add left right ih₁ ih₂ => simp only [substituteGround, Term.normalize, instantiateNF, ih₁, ih₂]
  | hom h body ih => simp only [substituteGround, Term.normalize, instantiateNF, ih]

/-- The matrix equality characterizes equality in the ACUIh equational theory after substitution. -/
theorem derives_substituteGround_iff (substitution : Var → Term Const Empty Hom)
    (left right : Term Const Var Hom) :
    Derives (substituteGround substitution left) (substituteGround substitution right) ↔
      matrixCoordinates (GroundMatrix.ofSubstitution substitution) left =
        matrixCoordinates (GroundMatrix.ofSubstitution substitution) right := by
  rw [← NF.normalize_eq_iff_derives, normalize_substituteGround, normalize_substituteGround,
    instantiateNF_eq_iff]

/-- The corresponding characterization for additive inequalities, expressed by their equations. -/
theorem derives_add_substituteGround_iff (substitution : Var → Term Const Empty Hom)
    (left right : Term Const Var Hom) :
    Derives (.add (substituteGround substitution left) (substituteGround substitution right))
        (substituteGround substitution right) ↔
      ∀ c, (matrixCoordinates (GroundMatrix.ofSubstitution substitution) left c).words ⊆
        (matrixCoordinates (GroundMatrix.ofSubstitution substitution) right c).words := by
  rw [← NF.normalize_eq_iff_derives]
  change (substituteGround substitution left).normalize ∪
      (substituteGround substitution right).normalize =
      (substituteGround substitution right).normalize ↔ _
  rw [Finset.union_eq_right, normalize_substituteGround, normalize_substituteGround,
    instantiateNF_subset_iff]

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
/-- The empty variable type certifies that a substitution value really is ground. -/
theorem groundTerm_isGround (term : Term Const Empty Hom) : term.IsGround := by
  induction term with
  | zero | const => trivial
  | var v => exact Empty.elim v
  | add _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | hom _ _ ih => exact ih

/-- The matrix criterion is exactly the existing ACUIh notion of a solved ground equation. -/
theorem solved_substituteGround_iff (substitution : Var → Term Const Empty Hom)
    (left right : Term Const Var Hom) :
    Solved (substituteGround substitution left) (substituteGround substitution right) ↔
      matrixCoordinates (GroundMatrix.ofSubstitution substitution) left =
        matrixCoordinates (GroundMatrix.ofSubstitution substitution) right := by
  rw [solved_iff_derives]
  simp only [groundTerm_isGround, true_and, derives_substituteGround_iff]

/-- The matrix criterion is exactly the existing ACUIh notion of a solved ground inequality. -/
theorem solvedBelow_substituteGround_iff (substitution : Var → Term Const Empty Hom)
    (left right : Term Const Var Hom) :
    SolvedBelow (substituteGround substitution left) (substituteGround substitution right) ↔
      ∀ c, (matrixCoordinates (GroundMatrix.ofSubstitution substitution) left c).words ⊆
        (matrixCoordinates (GroundMatrix.ofSubstitution substitution) right c).words := by
  rw [solvedBelow_iff_derives]
  simp only [groundTerm_isGround, true_and, derives_add_substituteGround_iff]

end ACUIhE.ACUIh.Linear
