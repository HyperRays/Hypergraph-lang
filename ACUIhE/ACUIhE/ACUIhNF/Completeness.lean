import ACUIhE.ACUIhNF.Soundness

/-!
# Correctness and completeness of ACUIh normal forms

Normal-form equality characterizes both equational derivability and validity
in all ACUIh algebras. The two round trips use literal equality on normal
forms and derivable equality on raw terms.
-/

namespace ACUIhE.ACUIh

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- Every derivation preserves normalization, as witnessed by the normal-form model. -/
theorem Derives.normalize_eq {left right : Term Const Var Hom}
    (derivation : Derives left right) : left.normalize = right.normalize := by
  let _ := NF.algebra (Const := Const) (Var := Var) (Hom := Hom)
  have equality := derivation.sound
    (fun c => ({([], Particle.const c)} : NF Const Var Hom))
    (fun v => ({([], Particle.var v)} : NF Const Var Hom))
  simpa only [Term.eval_normalForm] using equality

namespace NF

/-- Derivably equal terms have identical normal forms. -/
theorem completeness {left right : Term Const Var Hom} (derivation : Derives left right) :
    left.normalize = right.normalize := derivation.normalize_eq

/-- A complete characterization of the equational theory by finite-set equality. -/
theorem normalize_eq_iff_derives {left right : Term Const Var Hom} :
    left.normalize = right.normalize ↔ Derives left right :=
  ⟨soundness, completeness⟩

/-- A complete characterization of validity in all ACUIh algebras. -/
theorem normalize_eq_iff_semanticallyEquivalent {left right : Term Const Var Hom} :
    left.normalize = right.normalize ↔ SemanticallyEquivalent left right :=
  normalize_eq_iff_derives.trans soundness_and_completeness

/-- A reified list represents exactly those terms whose normal form is its set of members. -/
theorem reifyList_derives_iff (summands : List (Summand Const Var Hom))
    (term : Term Const Var Hom) :
    Derives (reifyList summands) term ↔ summands.toFinset = term.normalize := by
  rw [← normalize_eq_iff_derives, normalize_reifyList]

/-- The same characterization holds for equality in every ACUIh algebra. -/
theorem reifyList_semanticallyEquivalent_iff (summands : List (Summand Const Var Hom))
    (term : Term Const Var Hom) :
    SemanticallyEquivalent (reifyList summands) term ↔
      summands.toFinset = term.normalize := by
  rw [← soundness_and_completeness, reifyList_derives_iff]

/-- Reordering or repeating list members changes no represented term equivalence class. -/
theorem reifyList_congr_iff (left right : List (Summand Const Var Hom)) :
    Derives (reifyList left) (reifyList right) ↔ left.toFinset = right.toFinset := by
  rw [reifyList_derives_iff, normalize_reifyList]

/-- Interpretation of a reified list depends exactly on its finite-set interpretation. -/
@[simp] theorem eval_reifyList {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α)
    (summands : List (Summand Const Var Hom)) :
    (reifyList summands).eval interpretConst interpretVar =
      eval interpretConst interpretVar summands.toFinset := by
  have equality := Term.eval_normalize interpretConst interpretVar (reifyList summands)
  rw [normalize_reifyList] at equality
  exact equality.symm

/-- The certified output represents precisely the terms with the requested normal form. -/
theorem reifyWith_derives_iff (normal : NF Const Var Hom)
    (summands : List (Summand Const Var Hom)) (enumerates : summands.toFinset = normal)
    (term : Term Const Var Hom) :
    Derives (reifyWith normal summands enumerates).val term ↔ normal = term.normalize := by
  rw [reifyWith_val, reifyList_derives_iff, enumerates]

/-- Certified reification preserves interpretation of the requested normal form in every algebra. -/
@[simp] theorem eval_reifyWith {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α) (normal : NF Const Var Hom)
    (summands : List (Summand Const Var Hom)) (enumerates : summands.toFinset = normal) :
    (reifyWith normal summands enumerates).val.eval interpretConst interpretVar =
      eval interpretConst interpretVar normal := by
  rw [reifyWith_val, eval_reifyList, enumerates]

/-- Normalization followed by reification recovers a derivably equivalent term. -/
theorem reify_normalize (term : Term Const Var Hom) :
    Derives term.normalize.reify term :=
  soundness (normalize_reify term.normalize)

/-- Reification preserves the interpretation of a normal form in every algebra. -/
@[simp] theorem eval_reify {α : Type x} [ACUIh Hom α]
    (interpretConst : Const → α) (interpretVar : Var → α) (normal : NF Const Var Hom) :
    normal.reify.eval interpretConst interpretVar = eval interpretConst interpretVar normal := by
  have equality := Term.eval_normalize interpretConst interpretVar normal.reify
  rw [normalize_reify] at equality
  exact equality.symm

/-- Reification does not identify distinct normal forms, even as raw terms. -/
theorem reify_injective :
    Function.Injective (reify (Const := Const) (Var := Var) (Hom := Hom)) := by
  intro left right equality
  have normalized := congrArg Term.normalize equality
  simpa only [normalize_reify] using normalized

/-- Different normal forms are separated by their own concrete ACUIh model. -/
theorem separates {left right : Term Const Var Hom}
    (different : left.normalize ≠ right.normalize) :
    letI := algebra (Const := Const) (Var := Var) (Hom := Hom)
    left.eval (fun c => ({([], Particle.const c)} : NF Const Var Hom))
        (fun v => ({([], Particle.var v)} : NF Const Var Hom)) ≠
      right.eval (fun c => ({([], Particle.const c)} : NF Const Var Hom))
        (fun v => ({([], Particle.var v)} : NF Const Var Hom)) := by
  simpa only [Term.eval_normalForm] using different

end NF

/-- Decide ACUIh derivability by computing and comparing normal forms. -/
instance decidableDerives (left right : Term Const Var Hom) : Decidable (Derives left right) :=
  if equality : left.normalize = right.normalize then
    isTrue (NF.soundness equality)
  else
    isFalse (fun derivation => equality derivation.normalize_eq)

end ACUIhE.ACUIh
