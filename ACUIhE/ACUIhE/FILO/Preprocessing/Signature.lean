import ACUIhE.FILO.Preprocessing.FlatteningII

/-!
# Closing the finite-signature condition of flattening II

The restricted interpretation is constructed from any model solution. Thus
the top-level preprocessing equivalence has no signature hypothesis on input
substitutions and imposes no finiteness assumption on the type of role names.
-/

namespace ACUIhE.FILO

open ACUIh.Linear

universe v w

namespace Components

structure System (Var : Type v) (Hom : Type w) where
  roles : List Hom
  flat : Goal Var Hom

variable {Var : Type v} {Hom : Type w} [DecidableEq Hom]

/-- The finite alphabet is part of the generic system's semantic contract. -/
def System.Solution (system : System Var Hom) (iv : Column Var Hom) : Prop :=
  (∀ v, Language.Supported system.roles.toFinset (iv v)) ∧ Holds system.flat iv

def System.Solvable (system : System Var Hom) : Prop := ∃ iv, system.Solution iv

end Components

namespace FlatteningII

variable {Var : Type v} {Hom : Type w} [DecidableEq Hom]

local instance : ACUIh Hom (WordPolynomial Hom) := Column.algebra

def particleRoles : Flat.Particle Unit Var Hom → List Hom
  | .atom _ => []
  | .hom r _ => [r]

def conceptRoles (ps : Flat.Concept Unit Var Hom) : List Hom := ps.flatMap particleRoles

def roles (m : Flat.Model Unit Var Hom) : List Hom :=
  ((Projection.constraints m).flatMap fun q => conceptRoles q.left ++ conceptRoles q.right).dedup

theorem atom_eval_restrict (alphabet : Finset Hom) (iv : Column Var Hom) (a : Flat.Atom Unit Var) :
    a.eval (fun _ => (1 : WordPolynomial Hom)) (fun v => Language.restrict alphabet (iv v)) =
      Language.restrict alphabet (a.eval (fun _ => 1) iv) := by
  cases a with
  | const c => exact (Language.restrict_one alphabet).symm
  | var v => rfl

theorem particle_eval_restrict (alphabet : Finset Hom) (iv : Column Var Hom)
    (p : Flat.Particle Unit Var Hom) (included : ∀ r ∈ particleRoles p, r ∈ alphabet) :
    p.eval (fun _ => (1 : WordPolynomial Hom)) (fun v => Language.restrict alphabet (iv v)) =
      Language.restrict alphabet (p.eval (fun _ => 1) iv) := by
  cases p with
  | atom a => exact atom_eval_restrict alphabet iv a
  | hom r a =>
    change WordPolynomial.generator r * a.eval (fun _ => 1) _ =
      Language.restrict alphabet (WordPolynomial.generator r * a.eval (fun _ => 1) iv)
    rw [atom_eval_restrict, Language.restrict_prefix alphabet (included r (by simp [particleRoles]))]

theorem concept_eval_restrict (alphabet : Finset Hom) (iv : Column Var Hom)
    (ps : Flat.Concept Unit Var Hom) (included : ∀ r ∈ conceptRoles ps, r ∈ alphabet) :
    ps.eval (fun _ => (1 : WordPolynomial Hom)) (fun v => Language.restrict alphabet (iv v)) =
      Language.restrict alphabet (ps.eval (fun _ => 1) iv) := by
  induction ps with
  | nil => exact (Language.restrict_zero alphabet).symm
  | cons p ps ih =>
    have hp : ∀ r ∈ particleRoles p, r ∈ alphabet :=
      fun r hr => included r (List.mem_flatMap.mpr ⟨p, by simp, hr⟩)
    have ht : ∀ r ∈ conceptRoles ps, r ∈ alphabet := by
      intro r hr
      obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hr
      exact included r (List.mem_flatMap.mpr ⟨a, List.mem_cons_of_mem p ha, hm⟩)
    change p.eval _ _ + Flat.Concept.eval _ _ ps = Language.restrict alphabet (p.eval _ _ + Flat.Concept.eval _ _ ps)
    rw [particle_eval_restrict alphabet iv p hp, ih ht, Language.restrict_add]

theorem model_restrict (m : Flat.Model Unit Var Hom) (iv : Column Var Hom)
    (solution : m.Holds (fun _ => 1) iv) :
    m.Holds (fun _ => 1) (fun v => Language.restrict (roles m).toFinset (iv v)) := by
  apply (Projection.constraints_iff m _ _).mp
  intro q hq
  have left : ∀ r ∈ conceptRoles q.left, r ∈ (roles m).toFinset := by
    intro r hr
    exact List.mem_toFinset.mpr (List.mem_dedup.mpr (List.mem_flatMap.mpr
      ⟨q, hq, List.mem_append_left _ hr⟩))
  have right : ∀ r ∈ conceptRoles q.right, r ∈ (roles m).toFinset := by
    intro r hr
    exact List.mem_toFinset.mpr (List.mem_dedup.mpr (List.mem_flatMap.mpr
      ⟨q, hq, List.mem_append_right _ hr⟩))
  have original := (Projection.constraints_iff m _ _).mpr solution q hq
  have restricted := congrArg (Language.restrict (roles m).toFinset) original
  change Flat.Concept.eval _ _ q.left + Flat.Concept.eval _ _ q.right = _
  rw [concept_eval_restrict _ iv q.left left, concept_eval_restrict _ iv q.right right]
  exact (Language.restrict_add _ _ _).symm.trans restricted

/-- Fully specified, executable generic-goal construction. -/
def normalize (m : Flat.Model Unit Var Hom) : Components.System Var Hom :=
  ⟨roles m, compile (roles m) m⟩

/-- Flattening II preserves and reflects solvability without assuming that
an arbitrary input solution already uses only the finite role signature. -/
theorem normalize_solvable_iff (m : Flat.Model Unit Var Hom) :
    (normalize m).Solvable ↔ m.Solvable (fun _ => (1 : WordPolynomial Hom)) := by
  constructor
  · rintro ⟨iv, supported, solution⟩
    exact ⟨iv, (compile_correct (roles m) iv supported m).mp solution⟩
  · rintro ⟨iv, solution⟩
    let restricted := fun v => Language.restrict (roles m).toFinset (iv v)
    have supported : ∀ v, Language.Supported (roles m).toFinset (restricted v) :=
      fun v => Language.restrict_supported _ _
    exact ⟨restricted, supported, (compile_correct (roles m) restricted supported m).mpr
      (model_restrict m iv solution)⟩

end FlatteningII

end ACUIhE.FILO
