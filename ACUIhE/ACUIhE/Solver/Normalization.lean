import ACUIhE.Solver.Problem
import ACUIhE.Graph.PresentationNormalization
import ACUIhE.Solver.Cancellation

/-!
# Canonical equation preprocessing

Enumerations are retained for the list-based FILO interface, but identities
and duplicate equations are detected by full canonical graph equality.
Preservation is pointwise in every interpretation and every substitution.
-/

namespace ACUIhE.Solver.Normalization

universe u v w x y
variable {Const : Type u} {Var : Type v} {Hom : Type w} {Target : Type x}

abbrev Forest := Graph.Presentation.Forest
abbrev Equations (Const : Type u) (Var : Type v) (Hom : Type w) :=
  List (Generic.Equation (Forest Const Var Hom))

def key (q : Generic.Equation (Forest Const Var Hom)) : Graph Const Var Hom × Graph Const Var Hom :=
  (Graph.ofPresentation q.left, Graph.ofPresentation q.right)

def Holds {α : Type y} [ACUIhE Hom α] (qs : Equations Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Prop :=
  ∀ q ∈ qs, Graph.eval ic iv (key q).1 = Graph.eval ic iv (key q).2

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

def equation (q : Equation Const Var Hom) : Generic.Equation (Forest Const Var Hom) :=
  Cancellation.cancel (Graph.Presentation.normalizeTerm q.left)
    (Graph.Presentation.normalizeTerm q.right)

theorem equation_correct {α : Type y} [ACUIhE Hom α] (q : Equation Const Var Hom)
    (ic : Const → α) (iv : Var → α) :
    Graph.eval ic iv (key (equation q)).1 = Graph.eval ic iv (key (equation q)).2 ↔
      q.Holds ic iv := by
  simp only [key, equation, Graph.eval_ofPresentation]
  rw [Cancellation.cancel_correct]
  simp only [← Graph.eval_ofPresentation, Graph.Presentation.eval_normalizeTerm,
    Equation.Holds, Generic.Equation.Holds]

def normalize (p : Problem Const Var Hom) : Equations Const Var Hom :=
  Graph.Enumeration.dedupOn key
    ((p.map equation).filter (fun q => (key q).1 ≠ (key q).2))

theorem normalize_nodup (p : Problem Const Var Hom) : ((normalize p).map key).Nodup := by
  rw [normalize, Graph.Enumeration.map_dedupOn]
  exact List.nodup_dedup _

theorem normalize_no_identities (p : Problem Const Var Hom) {q : Generic.Equation (Forest Const Var Hom)}
    (hq : q ∈ normalize p) : (key q).1 ≠ (key q).2 := by
  have member := Graph.Enumeration.dedupOn_subset key _ hq
  simpa using (List.mem_filter.mp member).2

/-- No interpretation is gained or lost, including interpretations by nonground terms. -/
theorem holds_normalize_iff {α : Type y} [ACUIhE Hom α] (p : Problem Const Var Hom)
    (ic : Const → α) (iv : Var → α) : Holds (normalize p) ic iv ↔ p.Holds ic iv := by
  unfold normalize Holds
  rw [Graph.Enumeration.forall_dedupOn key _ _ (by intro a b h; rw [h])]
  constructor
  · intro h q hq
    let r := equation q
    have same : Graph.eval ic iv (key r).1 = Graph.eval ic iv (key r).2 := by
      by_cases eq : (key r).1 = (key r).2
      · rw [eq]
      · exact h r (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨q, hq, rfl⟩, by simpa using eq⟩)
    exact (equation_correct q ic iv).mp same
  · intro h r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hr).1
    exact (equation_correct q ic iv).mpr (h q hq)

/-- A raw-term view for preservation theorems; preparation uses the enumerations directly. -/
def reify (qs : Equations Const Var Hom) : Problem Const Var Hom :=
  qs.map (fun q => ⟨Graph.Presentation.reify q.left, Graph.Presentation.reify q.right⟩)

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
theorem holds_reify_iff {α : Type y} [ACUIhE Hom α] (qs : Equations Const Var Hom)
    (ic : Const → α) (iv : Var → α) : (reify qs).Holds ic iv ↔ Holds qs ic iv := by
  simp only [reify, Problem.Holds, List.forall_mem_map, Equation.Holds,
    Generic.Equation.Holds, Holds, key, Graph.eval_ofPresentation]

/-- Exact preservation of each ordinary substitution, not just existence of one. -/
theorem isUnifier_normalize_iff (p : Problem Const Var Hom)
    (σ : Var → Term Const Target Hom) : (reify (normalize p)).IsUnifier σ ↔ p.IsUnifier σ := by
  constructor <;> intro h q hq α inst ic iv
  · have original := (holds_normalize_iff p ic (fun v => (σ v).eval ic iv)).mp
      ((holds_reify_iff _ ic _).mp (show (reify (normalize p)).Holds ic
        (fun v => (σ v).eval ic iv) from fun r hr => by
          simpa only [Equation.Holds, Generic.Equation.Holds, Term.eval_substitute] using
            Term.Equal.sound ic iv (h r hr)))
    simpa only [Term.eval_substitute, Equation.Holds, Generic.Equation.Holds] using original q hq
  · have normalized := (holds_reify_iff _ ic (fun v => (σ v).eval ic iv)).mpr
      ((holds_normalize_iff p ic _).mpr (show p.Holds ic
        (fun v => (σ v).eval ic iv) from fun r hr => by
          simpa only [Equation.Holds, Generic.Equation.Holds, Term.eval_substitute] using
            Term.Equal.sound ic iv (h r hr)))
    simpa only [Term.eval_substitute, Equation.Holds, Generic.Equation.Holds] using normalized q hq

theorem unifiable_normalize_iff (p : Problem Const Var Hom) :
    (reify (normalize p)).Unifiable ↔ p.Unifiable := by
  exact exists_congr (fun σ => isUnifier_normalize_iff p σ)

/-- The inequality interface uses the existing exact conversion to equations. -/
theorem holds_inequalities_iff {α : Type y} [ACUIhE Hom α]
    (qs : List (Inequality Const Var Hom)) (ic : Const → α) (iv : Var → α) :
    Holds (normalize (fromInequalities qs)) ic iv ↔ ∀ q ∈ qs, q.Holds ic iv :=
  (holds_normalize_iff _ ic iv).trans (holds_fromInequalities_iff qs ic iv)

end ACUIhE.Solver.Normalization
