import ACUIhE.Transfer.Core
import ACUIhE.Equation

/-!
# Transfer between raw terms, quotient terms, and canonical forms

`Transfer.termModelEquivGraph` identifies the full ACUIhE term model (terms
modulo derivability) with canonical graphs. Both directions are computable;
the accompanying laws preserve zero, addition, named homomorphisms, and E.
It is not an equivalence between raw syntax and graphs.

`Transfer.NormalForm` packages a complete normalization and its reification.
Its predicate and relation transfer theorems require invariance under the
algebraic equality relation, so syntax-dependent properties cannot be
silently transported. Its quantifier theorems let a property of canonical
forms be proved by considering normalized terms, and conversely.

`Transfer.graph` and `Transfer.acuih` instantiate this shared interface for
the full algebra and the ACUIh fragment respectively. These two packages use
the existing noncomputable raw reifiers; this does not affect the executable
normalizers, decision procedures, or `termModelEquivGraph`.

The representation-independent machinery lives in `Transfer.Core`, allowing
the fragment equation laws to reuse it without circular imports. The concrete
soundness and round-trip proofs remain the foundations of these transfers.
-/

namespace ACUIhE.Transfer

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

/-! ## Full ACUIhE: a computable equivalence of the two quotient models -/

/-- Normalize a derivability class; the result is independent of its representative. -/
def toGraph : TermModel Const Var Hom → Graph Const Var Hom :=
  Quotient.lift Graph.normalize (fun _ _ h => Graph.completeness h)

/-- Interpret a graph directly in the quotient term model, without choosing raw syntax. -/
def fromGraph : Graph Const Var Hom → TermModel Const Var Hom :=
  Graph.eval (fun c => TermModel.ofTerm (.const c)) (fun v => TermModel.ofTerm (.var v))

@[simp] theorem toGraph_ofTerm (t : Term Const Var Hom) :
    toGraph (TermModel.ofTerm t) = Graph.normalize t := rfl

@[simp] theorem fromGraph_ofPresentation (xs : Graph.Presentation.Forest Const Var Hom) :
    fromGraph (Graph.ofPresentation xs) = TermModel.ofTerm (Graph.Presentation.reify xs) :=
  TermModel.eval_eq_ofTerm _

@[simp] theorem fromGraph_normalize (t : Term Const Var Hom) :
    fromGraph (Graph.normalize t) = TermModel.ofTerm t := by
  simp only [fromGraph, Graph.eval_normalize, TermModel.eval_eq_ofTerm]

@[simp] theorem fromGraph_toGraph (t : TermModel Const Var Hom) :
    fromGraph (toGraph t) = t := by
  refine Quotient.inductionOn t ?_
  exact fromGraph_normalize

@[simp] theorem toGraph_fromGraph (g : Graph Const Var Hom) : toGraph (fromGraph g) = g := by
  refine Quotient.inductionOn g ?_
  intro xs
  change toGraph (fromGraph (Graph.ofPresentation xs)) = Graph.ofPresentation xs
  rw [fromGraph_ofPresentation, toGraph_ofTerm, Graph.normalize_reifyPresentation]

/-- Terms modulo algebraic equality and canonical graphs are equivalent types.
Unlike raw reification, both maps compute without any choice of enumeration. -/
def termModelEquivGraph : TermModel Const Var Hom ≃ Graph Const Var Hom where
  toFun := toGraph
  invFun := fromGraph
  left_inv := fromGraph_toGraph
  right_inv := toGraph_fromGraph

@[simp] theorem termModelEquivGraph_apply (t : TermModel Const Var Hom) :
    termModelEquivGraph t = toGraph t := rfl

@[simp] theorem termModelEquivGraph_symm_apply (g : Graph Const Var Hom) :
    termModelEquivGraph.symm g = fromGraph g := rfl

@[simp] theorem toGraph_zero : toGraph (0 : TermModel Const Var Hom) = 0 := rfl

@[simp] theorem toGraph_add (a b : TermModel Const Var Hom) :
    toGraph (a + b) = toGraph a + toGraph b := by
  refine Quotient.inductionOn₂ a b ?_
  intro a b
  rfl

@[simp] theorem toGraph_hom (name : Hom) (t : TermModel Const Var Hom) :
    toGraph (TermModel.hom name t) = Graph.hom name (toGraph t) := by
  refine Quotient.inductionOn t ?_
  intro t
  rfl

@[simp] theorem toGraph_free (t : TermModel Const Var Hom) :
    toGraph (TermModel.free t) = Graph.free (toGraph t) := by
  refine Quotient.inductionOn t ?_
  intro t
  rfl

@[simp] theorem fromGraph_zero : fromGraph (0 : Graph Const Var Hom) = 0 := rfl

@[simp] theorem fromGraph_add (a b : Graph Const Var Hom) :
    fromGraph (a + b) = fromGraph a + fromGraph b := Graph.eval_add _ _ a b

@[simp] theorem fromGraph_hom (name : Hom) (g : Graph Const Var Hom) :
    fromGraph (Graph.hom name g) = TermModel.hom name (fromGraph g) := Graph.eval_hom _ _ name g

@[simp] theorem fromGraph_free (g : Graph Const Var Hom) :
    fromGraph (Graph.free g) = TermModel.free (fromGraph g) := Graph.eval_free _ _ g

@[simp] theorem toGraph_eq_iff (a b : TermModel Const Var Hom) :
    toGraph a = toGraph b ↔ a = b := termModelEquivGraph.injective.eq_iff

@[simp] theorem fromGraph_eq_iff (a b : Graph Const Var Hom) :
    fromGraph a = fromGraph b ↔ a = b := termModelEquivGraph.symm.injective.eq_iff

/-- The equivalence preserves and reflects the additive order. -/
@[simp] theorem toGraph_below_iff (a b : TermModel Const Var Hom) :
    toGraph a ≤₊ toGraph b ↔ a ≤₊ b := by
  change toGraph a + toGraph b = toGraph b ↔ a + b = b
  rw [← toGraph_add, toGraph_eq_iff]

@[simp] theorem fromGraph_below_iff (a b : Graph Const Var Hom) :
    fromGraph a ≤₊ fromGraph b ↔ a ≤₊ b := by
  change fromGraph a + fromGraph b = fromGraph b ↔ a + b = b
  rw [← fromGraph_add, fromGraph_eq_iff]

/-! ## Raw-term transfer for the full algebra -/

/-- Full terms and graphs instantiate the representation-independent transfer API. -/
noncomputable def graph : NormalForm (Term Const Var Hom) (Graph Const Var Hom) Term.Equal where
  normalize := Graph.normalize
  reify := Graph.reify
  normalize_reify := Graph.normalize_reify
  equal_iff_normalize_eq := Term.equal_iff_normalize_eq

theorem term_equal_iff (a b : Term Const Var Hom) :
    a.Equal b ↔ Graph.normalize a = Graph.normalize b := Term.equal_iff_normalize_eq a b

theorem term_below_iff (a b : Term Const Var Hom) :
    a.Below b ↔ Graph.normalize a ≤₊ Graph.normalize b := Term.below_iff_normalize_eq a b

theorem reify_equal_iff (a b : Graph Const Var Hom) :
    (Graph.reify a).Equal (Graph.reify b) ↔ a = b := graph.reify_equal_iff a b

theorem reify_below_iff (a b : Graph Const Var Hom) :
    (Graph.reify a).Below (Graph.reify b) ↔ a ≤₊ b := by
  rw [term_below_iff, Graph.normalize_reify, Graph.normalize_reify]

/-- Equality itself meets the condition required by binary property transfer. -/
theorem equal_invariant : Invariant₂ (Term.Equal (Const := Const) (Var := Var) (Hom := Hom))
    Term.Equal := by
  intro a a' b b' ha hb
  rw [term_equal_iff] at ha hb ⊢
  rw [term_equal_iff, ha, hb]

/-- Inequality meets the same condition; it does not depend on raw representatives. -/
theorem below_invariant : Invariant₂ (Term.Equal (Const := Const) (Var := Var) (Hom := Hom))
    Term.Below := by
  intro a a' b b' ha hb
  rw [term_equal_iff] at ha hb
  rw [term_below_iff, term_below_iff, ha, hb]

/-! ## The same predicate-transfer API for ACUIh finite-set normal forms -/

section ACUIh

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- ACUIh uses its own equality and its own normal form, without introducing E. -/
noncomputable def acuih :
    NormalForm (ACUIh.Term Const Var Hom) (ACUIh.NF Const Var Hom) ACUIh.Term.Equal where
  normalize := ACUIh.Term.normalize
  reify := ACUIh.NF.reify
  normalize_reify := ACUIh.NF.normalize_reify
  equal_iff_normalize_eq := ACUIh.Term.equal_iff_normalize_eq

theorem acuih_equal_iff (a b : ACUIh.Term Const Var Hom) :
    a.Equal b ↔ a.normalize = b.normalize := ACUIh.Term.equal_iff_normalize_eq a b

/-- On ACUIh normal forms the additive order is precisely finite-set inclusion. -/
theorem acuih_below_iff (a b : ACUIh.Term Const Var Hom) :
    a.Below b ↔ a.normalize ⊆ b.normalize :=
  (ACUIh.Term.below_iff_normalize_eq a b).trans Finset.union_eq_right

theorem acuih_reify_equal_iff (a b : ACUIh.NF Const Var Hom) :
    a.reify.Equal b.reify ↔ a = b := acuih.reify_equal_iff a b

theorem acuih_reify_below_iff (a b : ACUIh.NF Const Var Hom) :
    a.reify.Below b.reify ↔ a ⊆ b := by
  rw [acuih_below_iff, ACUIh.NF.normalize_reify, ACUIh.NF.normalize_reify]

end ACUIh

end ACUIhE.Transfer
