import ACUIhE.Solver.Problem
import ACUIhE.Solver.ForcedMatching

/-! Deterministic decomposition in the canonical algebra. Field separation is
checked algebraically; no type-constructor names or additional equations are
assumed. Variables at an exposed additive layer prevent separation. -/

namespace ACUIhE.Solver.Decomposition
universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Hom]

local notation "Ty" => Term Const Var Hom
local notation "Assignment" => Var → Graph Const Empty Hom

def headKey (s : Graph.Summand Const Empty Hom) : Hom ⊕ Option Const :=
  match s with
  | (h :: _, _) => .inl h
  | ([], .inl (.const c)) => .inr (some c)
  | ([], _) => .inr none

def heads : Ty → Option (Finset (Hom ⊕ Option Const))
  | .zero => some ∅
  | .var _ => none
  | .const c => some {.inr (some c)}
  | .free _ => some {.inr none}
  | .hom h _ => some {.inl h}
  | .add a b => do return (← heads a) ∪ (← heads b)

theorem heads_sound (t : Ty) (hs : heads t = some names) (iv : Assignment)
    {s} (member : s ∈ (t.eval Graph.constant iv).layer) : headKey s ∈ names := by
  induction t generalizing names with
  | zero => simp [Term.eval] at member
  | var => simp [heads] at hs
  | const c =>
    simp only [heads, Option.some.injEq] at hs
    subst names
    have eq : s = ([], .inl (.const c)) := by simpa [Term.eval] using member
    subst s
    simp [headKey]
  | free t ih =>
    simp only [heads, Option.some.injEq] at hs
    subst names
    by_cases hz : t.eval Graph.constant iv = 0
    · change s ∈ (Graph.free (t.eval Graph.constant iv)).layer at member
      rw [hz] at member
      change s ∈ (0 : Graph Const Empty Hom).layer at member
      simp at member
    · have layer := Graph.layer_free_of_ne_zero (t.eval Graph.constant iv) hz
      change s ∈ (Graph.free (t.eval Graph.constant iv)).layer at member
      rw [layer, Finset.mem_singleton] at member
      subst s
      simp [headKey]
  | hom h t ih =>
    simp only [heads, Option.some.injEq] at hs
    subst names
    change s ∈ (Graph.hom h (t.eval Graph.constant iv)).layer at member
    rw [Graph.layer_hom, Finset.mem_image] at member
    obtain ⟨⟨word, atom⟩, _, rfl⟩ := member
    simp [headKey]
  | add a b ia ib =>
    cases ha : heads a <;> cases hb : heads b <;> simp [heads, ha, hb] at hs
    rename_i na nb
    subst names
    change s ∈ (a.eval Graph.constant iv + b.eval Graph.constant iv).layer at member
    rw [Graph.layer_add, Finset.mem_union] at member
    exact member.elim (fun h => Finset.mem_union_left _ (ia ha h))
      (fun h => Finset.mem_union_right _ (ib hb h))

def separated (a b c d : Ty) : Bool :=
  match heads a, heads b, heads c, heads d with
  | some ha, some hb, some hc, some hd => decide (Disjoint (ha ∪ hc) (hb ∪ hd))
  | _, _, _, _ => false

theorem separated_eq (a b c d : Ty) (hs : separated a b c d = true) (iv : Assignment) :
    (.add a b : Ty).eval Graph.constant iv = (.add c d : Ty).eval Graph.constant iv ↔
      a.eval Graph.constant iv = c.eval Graph.constant iv ∧
      b.eval Graph.constant iv = d.eval Graph.constant iv := by
  cases ha : heads a <;> cases hb : heads b <;>
    cases hc : heads c <;> cases hd : heads d <;> simp [separated, ha, hb, hc, hd] at hs
  rename_i na nb nc nd
  have hdj : Disjoint (na ∪ nc) (nb ∪ nd) := by simpa using hs
  constructor
  · intro eq
    have layers := congrArg Graph.layer eq
    change (a.eval Graph.constant iv + b.eval Graph.constant iv).layer =
      (c.eval Graph.constant iv + d.eval Graph.constant iv).layer at layers
    rw [Graph.layer_add, Graph.layer_add] at layers
    have disj : Disjoint ((a.eval Graph.constant iv).layer ∪ (c.eval Graph.constant iv).layer)
        ((b.eval Graph.constant iv).layer ∪ (d.eval Graph.constant iv).layer) := by
      apply Finset.disjoint_left.mpr
      intro s hl hr
      have left := (Finset.mem_union.mp hl).elim
        (fun h => Finset.mem_union_left _ (heads_sound a ha iv h))
        (fun h => Finset.mem_union_right _ (heads_sound c hc iv h))
      have right := (Finset.mem_union.mp hr).elim
        (fun h => Finset.mem_union_left _ (heads_sound b hb iv h))
        (fun h => Finset.mem_union_right _ (heads_sound d hd iv h))
      exact Finset.disjoint_left.mp hdj left right
    have split : (a.eval Graph.constant iv).layer = (c.eval Graph.constant iv).layer ∧
        (b.eval Graph.constant iv).layer = (d.eval Graph.constant iv).layer := by
      constructor <;> ext s
      all_goals
        have same := Finset.ext_iff.mp layers s
        have apart : s ∈ ((a.eval Graph.constant iv).layer ∪ (c.eval Graph.constant iv).layer) →
            s ∈ ((b.eval Graph.constant iv).layer ∪ (d.eval Graph.constant iv).layer) → False :=
          fun hl hr => Finset.disjoint_left.mp disj hl hr
        simp only [Finset.mem_union] at same apart
        tauto
    exact ⟨Graph.layer_injective split.1, Graph.layer_injective split.2⟩
  · rintro ⟨a, b⟩
    simp only [Term.eval, a, b]

theorem hom_injective (h : Hom) : Function.Injective (Graph.hom h : Graph Const Empty Hom → _) := by
  intro a b eq
  apply Graph.layer_injective
  have layers := congrArg Graph.layer eq
  simp only [Graph.layer_hom] at layers
  exact Finset.image_injective (by intro ⟨u, x⟩ ⟨v, y⟩ h; simpa using h) layers

def equation : Ty → Ty → Problem Const Var Hom
  | .free a, .free b => equation a b
  | .hom h a, .hom k b => if h = k then equation a b else [⟨.hom h a, .hom k b⟩]
  | .add a b, .add c d =>
      if separated a b c d then equation a c ++ equation b d else [⟨.add a b, .add c d⟩]
  | a, b => [⟨a, b⟩]
termination_by a b => sizeOf a + sizeOf b

theorem equation_correct (a b : Ty) (iv : Assignment) :
    (equation a b).IsSolution iv ↔ a.eval Graph.constant iv = b.eval Graph.constant iv := by
  fun_induction equation a b
  · rename_i a b ih
    simpa only [Term.eval] using ih.trans (E_injective.eq_iff.symm)
  · rename_i a h b ih
    exact ih.trans (hom_injective (Const := Const) h).eq_iff.symm
  · simp [Problem.IsSolution, Problem.Holds, Equation.Holds, Generic.Equation.Holds]
  · rename_i a b c d separated ia ib
    simp only [Problem.IsSolution, Problem.Holds, List.forall_mem_append]
    exact (and_congr ia ib).trans (separated_eq a b c d separated iv).symm
  · simp [Problem.IsSolution, Problem.Holds, Equation.Holds, Generic.Equation.Holds]
  · simp [Problem.IsSolution, Problem.Holds, Equation.Holds, Generic.Equation.Holds]

variable [DecidableEq Var]

/-- Expose constructor shapes hidden by additive units or repeated terms.
This is an interpretation-preserving use of the existing ACUI equations. -/
def tidy : Ty → Ty
  | .add a b =>
      let a := tidy a
      let b := tidy b
      if a = .zero then b else if b = .zero ∨ a = b then a else .add a b
  | .hom h a => .hom h (tidy a)
  | .free a => .free (tidy a)
  | t => t

theorem tidy_correct {A : Type*} [ACUIhE Hom A] (t : Ty) (ic : Const → A) (iv : Var → A) :
    (tidy t).eval ic iv = t.eval ic iv := by
  induction t with
  | zero | const | var => rfl
  | hom h a ih => exact congrArg (H h) ih
  | free a ih => exact congrArg (E (Hom := Hom)) ih
  | add a b ia ib =>
    simp only [tidy]
    split_ifs with az bz
    · have zero : a.eval ic iv = 0 := by rw [← ia, az]; rfl
      simp only [Term.eval, zero, ib]
      rw [ACUIhE.add_comm (0 : A), ACUIhE.add_zero]
    · rcases bz with bz | same
      · have zero : b.eval ic iv = 0 := by rw [← ib, bz]; rfl
        simp only [Term.eval, zero, ia, ACUIhE.add_zero]
      · have eq : a.eval ic iv = b.eval ic iv := by rw [← ia, same, ib]
        simp only [Term.eval, ia, eq, ACUIhE.add_idem]
    · simp only [Term.eval, ia, ib]

def basic (p : Problem Const Var Hom) : Problem Const Var Hom :=
  p.flatMap (fun q => equation (tidy q.left) (tidy q.right))

theorem basic_correct (p : Problem Const Var Hom) (iv : Assignment) :
    (basic p).IsSolution iv ↔ p.IsSolution iv := by
  simp only [basic, Problem.IsSolution, Problem.Holds, List.forall_mem_flatMap]
  exact forall_congr' fun q => forall_congr' fun _ => by
    simpa only [Problem.IsSolution, Problem.Holds, Equation.Holds, Generic.Equation.Holds,
      tidy_correct] using equation_correct (tidy q.left) (tidy q.right) iv

/-- Expose deterministic fields, derive necessary E-child equalities, and
decompose those fields too. Keep the residual equations to preserve all
sharing and all ambiguous matches for the complete solver. -/
def run (p : Problem Const Var Hom) : Problem Const Var Hom :=
  let q := basic p
  q ++ basic (ForcedMatching.extra q)

/-- Equality of solution sets for every canonical graph assignment. -/
theorem run_correct (p : Problem Const Var Hom) (iv : Assignment) :
    (run p).IsSolution iv ↔ p.IsSolution iv := by
  have append : (run p).IsSolution iv ↔
      (basic p).IsSolution iv ∧ (basic (ForcedMatching.extra (basic p))).IsSolution iv := by
    simp only [run, Problem.IsSolution, Problem.Holds, List.forall_mem_append]
  rw [append, basic_correct]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, (basic_correct _ iv).mpr
      (ForcedMatching.extra_sound _ iv ((basic_correct p iv).mpr h))⟩

end ACUIhE.Solver.Decomposition
