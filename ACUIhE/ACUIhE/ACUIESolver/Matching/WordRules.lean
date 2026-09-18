import ACUIhE.ACUIESolver.Matching.Rules
import ACUIhE.FILO.Coordinates

/-!
# Word-valued interpretation of the shared E conditions

Named E atoms have empty homomorphism words at the root. Child support only
restricts E-name coordinates; ordinary constants and arbitrary words remain
available. The translation to FILO is proved exact for every input matrix.
-/

namespace ACUIhE.ACUIESolver.Matching.WordRules

open ACUIh.Linear

universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w} {n : Nat}

abbrev Atom (Const : Type u) (n : Nat) := Const ⊕ Fin n
abbrev Layer (Const : Type u) (Var : Type v) (Hom : Type w) (n : Nat) :=
  ACUIh.Term (Atom Const n) Var Hom

def names (s : Finset (Fin n)) : Layer Const Var Hom n :=
  ((List.finRange n).filter (fun i => i ∈ s)).foldr
    (fun i rest => .add (.const (.inr i)) rest) .zero

def expression : Rules.Expr (Layer Const Var Hom n) n → Layer Const Var Hom n
  | .layer e => e
  | .atoms s => names s

def inequalities : Rules.Condition (Layer Const Var Hom n) n → FILO.Problem (Atom Const n) Var Hom
  | .equal a b => [⟨expression a, expression b⟩, ⟨expression b, expression a⟩]
  | .below a b => [⟨expression a, expression b⟩]
  | .supported _ _ => []

def support : Rules.Condition (Layer Const Var Hom n) n →
    List (Layer Const Var Hom n × Finset (Atom Const n))
  | .equal _ _ | .below _ _ => []
  | .supported e allowed => [(e, allowed.map ⟨Sum.inr, Sum.inr_injective⟩)]

def compile (cs : Rules.System (Layer Const Var Hom n) n) :
    FILO.Coordinates.System (Atom Const n) Var Hom where
  inequalities := cs.flatMap inequalities
  coordinates := (List.finRange n).map Sum.inr
  support := cs.flatMap support

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

def atoms (s : Finset (Fin n)) : ACUIh.NF (Atom Const n) Empty Hom :=
  s.image (fun i => ([], .const (.inr i)))

def interpretation (m : GroundMatrix (Atom Const n) Var Hom) :
    Rules.Interpretation (Layer Const Var Hom n) (ACUIh.NF (Atom Const n) Empty Hom) n where
  layer := instantiateNF m
  atoms := atoms
  below := (· ⊆ ·)
  support := fun nf => Finset.univ.filter (fun i => Row.ofNF nf (.inr i) ≠ 0)

omit [DecidableEq Var] in
theorem instantiate_names (m : GroundMatrix (Atom Const n) Var Hom) (s : Finset (Fin n)) :
    instantiateNF m (names s) = atoms (Const := Const) (Hom := Hom) s := by
  have aux (xs : List (Fin n)) :
      instantiateNF m (xs.foldr (fun i rest => .add (.const (.inr i)) rest) .zero) =
        atoms (Const := Const) (Hom := Hom) xs.toFinset := by
    induction xs with
    | nil => simp [instantiateNF, atoms]
    | cons i xs ih => simp [instantiateNF, atoms, ih]
  rw [names, aux]
  congr 1
  ext i
  simp

omit [DecidableEq Var] in
@[simp] theorem instantiate_expression (m : GroundMatrix (Atom Const n) Var Hom)
    (e : Rules.Expr (Layer Const Var Hom n) n) :
    instantiateNF m (expression e) = e.eval (interpretation m) := by
  cases e with
  | layer e => rfl
  | atoms s => exact instantiate_names m s

theorem supported_iff (m : GroundMatrix (Atom Const n) Var Hom)
    (e : Layer Const Var Hom n) (allowed : Finset (Fin n)) :
    (interpretation m).support ((interpretation m).layer e) ⊆ allowed ↔
      ∀ i, i ∉ allowed → matrixCoordinates m e (.inr i) = 0 := by
  change (Finset.univ.filter (fun i => Row.ofNF (instantiateNF m e) (.inr i) ≠ 0)) ⊆ allowed ↔ _
  rw [ofNF_instantiateNF]
  constructor
  · intro h i missing
    by_contra nonzero
    exact missing (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, nonzero⟩))
  · intro h i member
    by_contra missing
    exact (Finset.mem_filter.mp member).2 (h i missing)

theorem condition_exact (m : GroundMatrix (Atom Const n) Var Hom)
    (c : Rules.Condition (Layer Const Var Hom n) n) :
    (inequalities c).IsSolution m ∧
      (∀ z ∈ support c, ∀ i : Fin n,
        .inr i ∉ z.2 → matrixCoordinates m z.1 (.inr i) = 0) ↔ c.Holds (interpretation m) := by
  cases c with
  | equal a b =>
    simp [inequalities, support, FILO.Problem.IsSolution, ACUIh.Inequality.left,
      ACUIh.Inequality.right, Rules.Condition.Holds]
    exact ⟨fun h => Finset.Subset.antisymm h.1 h.2,
      fun h => ⟨h ▸ Finset.Subset.refl _, h ▸ Finset.Subset.refl _⟩⟩
  | below a b =>
    change (inequalities (.below a b)).IsSolution m ∧ _ ↔
      a.eval (interpretation m) ⊆ b.eval (interpretation m)
    simp [inequalities, support, FILO.Problem.IsSolution, ACUIh.Inequality.left,
      ACUIh.Inequality.right]
  | supported e allowed =>
    change _ ↔ (interpretation m).support ((interpretation m).layer e) ⊆ allowed
    rw [supported_iff]
    simp [inequalities, FILO.Problem.IsSolution, support]

theorem compile_exact (m : GroundMatrix (Atom Const n) Var Hom)
    (cs : Rules.System (Layer Const Var Hom n) n) :
    (compile cs).IsSolution m ↔ Rules.Holds (interpretation m) cs := by
  simp only [FILO.Coordinates.System.IsSolution, compile, FILO.Problem.IsSolution,
    List.forall_mem_flatMap, List.forall_mem_map, List.mem_finRange, forall_true_left, Rules.Holds]
  constructor
  · rintro ⟨hi, hz⟩ c hc
    exact (condition_exact m c).mp ⟨hi c hc, hz c hc⟩
  · intro h
    exact ⟨fun c hc => ((condition_exact m c).mpr (h c hc)).1,
      fun c hc => ((condition_exact m c).mpr (h c hc)).2⟩

omit [DecidableEq Var] in
theorem atoms_mono (m : GroundMatrix (Atom Const n) Var Hom) (a b : Finset (Fin n))
    (h : a ⊆ b) : (interpretation m).below ((interpretation m).atoms a)
      ((interpretation m).atoms b) := Finset.image_subset_image h

end ACUIhE.ACUIESolver.Matching.WordRules
