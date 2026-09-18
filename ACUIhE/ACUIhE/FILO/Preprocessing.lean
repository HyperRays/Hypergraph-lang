import ACUIhE.FILO.Preprocessing.Signature

/-! # End-to-end correctness of FILO preprocessing (§4.2–4.4) -/

namespace ACUIhE.FILO.Preprocessing

universe u v w

variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- The generic goal for one input constant. All results are plain data. -/
def compile (p : Problem Const Var Hom) (c : Const) :
    Components.System (Flat.Variable Const Var Hom) Hom :=
  FlatteningII.normalize (Projection.compile (FlatteningI.compile p) c)

/-- Raw matrix unifiability is equivalent to solvability of the computed
generic systems. There are no intermediate-correctness assumptions. -/
theorem unifiable_iff (p : Problem Const Var Hom) :
    p.Unifiable ↔ ∀ c ∈ p.constantNames, (compile p c).Solvable := by
  rw [Projection.unifiable_iff]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro _
  exact (FlatteningII.normalize_solvable_iff _).symm

end ACUIhE.FILO.Preprocessing
