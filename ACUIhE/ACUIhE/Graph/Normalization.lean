import ACUIhE.Graph.Semantics
import ACUIhE.Completeness

/-!
# Canonicality for the full ACUIhE algebra

Normalization and presentation-based reification are executable without orders
on labels. Choosing a raw representative of an unordered canonical graph uses
choice, as does `Finset.toList`; `reifyWith` is the certified executable API.
-/

namespace ACUIhE.Graph

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-- Normalize arbitrary full terms, with arbitrarily nested E and homomorphisms. -/
def normalize (term : Term Const Var Hom) : Graph Const Var Hom :=
  term.eval constant ofVariable

@[simp] theorem normalize_zero : normalize (.zero : Term Const Var Hom) = 0 := rfl
@[simp] theorem normalize_const (name : Const) :
    normalize (.const name : Term Const Var Hom) = constant name := rfl
@[simp] theorem normalize_var (name : Var) :
    normalize (.var name : Term Const Var Hom) = ofVariable name := rfl
@[simp] theorem normalize_add (a b : Term Const Var Hom) :
    normalize (.add a b) = normalize a + normalize b := rfl
@[simp] theorem normalize_hom (name : Hom) (a : Term Const Var Hom) :
    normalize (.hom name a) = hom name (normalize a) := rfl
@[simp] theorem normalize_free (a : Term Const Var Hom) :
    normalize (.free a) = free (normalize a) := rfl

/-- Interpretation of a normal form agrees with interpretation of the original term. -/
@[simp] theorem eval_normalize {α : Type x} [ACUIhE Hom α]
    (ic : Const → α) (iv : Var → α) (term : Term Const Var Hom) :
    eval ic iv (normalize term) = term.eval ic iv := by
  induction term with
  | zero => rfl
  | const => exact ACUIhE.add_zero _
  | var => exact ACUIhE.add_zero _
  | add a b ih₁ ih₂ => simp only [normalize_add, eval_add, Term.eval, ih₁, ih₂]
  | hom name body ih => simp only [normalize_hom, eval_hom, Term.eval, ih]
  | free body ih => simp only [normalize_free, eval_free, Term.eval, ih]

/-- All rules, including E cancellation, preserve the canonical graph. -/
theorem completeness {a b : Term Const Var Hom} (h : Derives a b) :
    normalize a = normalize b := h.sound constant ofVariable

/-- Equal canonical graphs imply a derivation using the full ACUIhE axioms. -/
theorem soundness {a b : Term Const Var Hom} (h : normalize a = normalize b) :
    Derives a b := by
  apply ACUIhE.completeness
  intro α _ ic iv
  rw [← eval_normalize ic iv a, ← eval_normalize ic iv b, h]

/-- Equality of canonical graphs is exactly full ACUIhE derivability. -/
theorem normalize_eq_iff_derives (a b : Term Const Var Hom) :
    normalize a = normalize b ↔ Derives a b := ⟨soundness, completeness⟩

theorem normalize_eq_iff_semanticallyEquivalent (a b : Term Const Var Hom) :
    normalize a = normalize b ↔ SemanticallyEquivalent a b :=
  (normalize_eq_iff_derives a b).trans ACUIhE.soundness_and_completeness

private theorem normalize_reify_of_trees (xs : Presentation.Forest Const Var Hom)
    (h : ∀ t ∈ xs, normalize t.reify = ofPresentation [t]) :
    normalize (Presentation.reify xs) = ofPresentation xs := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
      change normalize t.reify + normalize (Presentation.reify xs) = _
      rw [h t (by simp), ih (fun s hs => h s (by simp [hs]))]
      rfl

private theorem normalize_reify_tree (t : Presentation.Tree Const Var Hom) :
    normalize t.reify = ofPresentation [t] := by
  induction t using
    (measure (fun t : Presentation.Tree Const Var Hom => sizeOf t)).wf.induction
  rename_i t ih
  cases t with
  | atom word p =>
      clear ih
      cases p <;> induction word with
      | nil => rfl
      | cons name word ih =>
          simp only [Presentation.Tree.reify] at ih
          change hom name (normalize _) = _
          rw [ih]
          rfl
  | edge word first rest =>
      have children : normalize (Presentation.reify (first :: rest)) =
          ofPresentation (first :: rest) :=
        normalize_reify_of_trees _
          (fun t ht => ih t (Presentation.Tree.child_lt word first rest ht))
      clear ih
      change normalize (Presentation.applyWord word (.free (Presentation.reify (first :: rest)))) = _
      induction word with
      | nil =>
          change free (normalize (Presentation.reify (first :: rest))) = _
          rw [children]
          rfl
      | cons name word ih =>
          change hom name (normalize (Presentation.applyWord word _)) = _
          rw [ih]
          rfl

/-- Every presentation is recovered up to precisely recursive set equality. -/
@[simp] theorem normalize_reifyPresentation (xs : Presentation.Forest Const Var Hom) :
    normalize (Presentation.reify xs) = ofPresentation xs :=
  normalize_reify_of_trees xs (fun t _ => normalize_reify_tree t)

/-- Choose an enumeration at every layer and reify it to raw syntax. -/
noncomputable def reify (graph : Graph Const Var Hom) : Term Const Var Hom :=
  Presentation.reify graph.out

/-- Reify a supplied structural presentation, with the round trip in the result type. -/
def reifyWith (graph : Graph Const Var Hom) (xs : Presentation.Forest Const Var Hom)
    (h : ofPresentation xs = graph) : {term : Term Const Var Hom // normalize term = graph} :=
  ⟨Presentation.reify xs, (normalize_reifyPresentation xs).trans h⟩

/-- The canonical graph → term → canonical graph round trip is literal equality. -/
@[simp] theorem normalize_reify (graph : Graph Const Var Hom) :
    normalize (reify graph) = graph := by
  unfold reify
  rw [normalize_reifyPresentation]
  exact Quotient.out_eq graph

/-- The term → graph → term round trip is equality in the full theory. -/
theorem reify_normalize (term : Term Const Var Hom) :
    Derives (reify (normalize term)) term :=
  soundness (normalize_reify (normalize term))

/-- Graph forms are already fixed points of normalization after reification. -/
noncomputable def canonicalize (graph : Graph Const Var Hom) : Graph Const Var Hom :=
  normalize (reify graph)

def IsCanonical (graph : Graph Const Var Hom) : Prop := canonicalize graph = graph

@[simp] theorem canonicalize_eq (graph : Graph Const Var Hom) :
    canonicalize graph = graph := normalize_reify graph

theorem isCanonical (graph : Graph Const Var Hom) : IsCanonical graph := canonicalize_eq graph

@[simp] theorem canonicalize_idempotent (graph : Graph Const Var Hom) :
    canonicalize (canonicalize graph) = canonicalize graph := canonicalize_eq _

theorem reify_derives_iff (a b : Graph Const Var Hom) :
    Derives (reify a) (reify b) ↔ a = b := by
  rw [← normalize_eq_iff_derives, normalize_reify, normalize_reify]

theorem reify_injective : Function.Injective (reify (Const := Const) (Var := Var)
    (Hom := Hom)) := by
  intro a b h
  simpa only [normalize_reify] using congrArg normalize h

/-- The executable API has the same semantics as chosen-representative reification. -/
theorem reifyWith_derives_reify (graph : Graph Const Var Hom)
    (xs : Presentation.Forest Const Var Hom) (h : ofPresentation xs = graph) :
    Derives (reifyWith graph xs h).val (reify graph) :=
  soundness ((reifyWith graph xs h).property.trans (normalize_reify graph).symm)

@[simp] theorem eval_reify {α : Type x} [ACUIhE Hom α]
    (ic : Const → α) (iv : Var → α) (graph : Graph Const Var Hom) :
    (reify graph).eval ic iv = eval ic iv graph := by
  rw [← eval_normalize, normalize_reify]

theorem eval_reifyWith {α : Type x} [ACUIhE Hom α]
    (ic : Const → α) (iv : Var → α) (graph : Graph Const Var Hom)
    (xs : Presentation.Forest Const Var Hom) (h : ofPresentation xs = graph) :
    (reifyWith graph xs h).val.eval ic iv = eval ic iv graph := by
  rw [← eval_normalize, (reifyWith graph xs h).property]

end ACUIhE.Graph
