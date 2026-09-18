import Mathlib.Logic.Equiv.Defs

/-! # Representation-independent transfer machinery

This foundational module does not import any fragment, normalizer, or equation
proof. Both the concrete transfer API and the shared relation laws use it.
-/

namespace ACUIhE.Transfer

universe u v w x

section Generic

variable {Raw : Type u} {Normal : Type v}

/-- A property that depends only on algebraic meaning, not the chosen raw syntax. -/
def Invariant (Equal : Raw → Raw → Prop) (P : Raw → Prop) : Prop :=
  ∀ ⦃a b⦄, Equal a b → (P a ↔ P b)

/-- A relation that respects algebraic equality in both arguments. -/
def Invariant₂ (Equal : Raw → Raw → Prop) (R : Raw → Raw → Prop) : Prop :=
  ∀ ⦃a a' b b'⦄, Equal a a' → Equal b b' → (R a b ↔ R a' b')

/-- A canonical representation of a raw equality relation, with a certified reifier. -/
structure NormalForm (Raw : Type u) (Normal : Type v) (Equal : Raw → Raw → Prop) where
  normalize : Raw → Normal
  reify : Normal → Raw
  normalize_reify : ∀ n, normalize (reify n) = n
  equal_iff_normalize_eq : ∀ a b, Equal a b ↔ normalize a = normalize b

namespace NormalForm

variable {Equal : Raw → Raw → Prop} (F : NormalForm Raw Normal Equal)

theorem normalize_surjective : Function.Surjective F.normalize :=
  fun n => ⟨F.reify n, F.normalize_reify n⟩

/-- Normalizing and reifying recovers the original algebraic meaning. -/
theorem reify_normalize (t : Raw) : Equal (F.reify (F.normalize t)) t :=
  (F.equal_iff_normalize_eq _ _).mpr (F.normalize_reify _)

theorem reify_equal_iff (a b : Normal) : Equal (F.reify a) (F.reify b) ↔ a = b := by
  rw [F.equal_iff_normalize_eq, F.normalize_reify, F.normalize_reify]

/-- Transfer any algebraically invariant predicate to the canonical representative. -/
theorem predicate_iff {P : Raw → Prop} (hP : Invariant Equal P) (t : Raw) :
    P t ↔ P (F.reify (F.normalize t)) :=
  (hP (F.reify_normalize t)).symm

/-- Binary properties, including equations and inequalities, transfer argumentwise. -/
theorem relation_iff {R : Raw → Raw → Prop} (hR : Invariant₂ Equal R) (a b : Raw) :
    R a b ↔ R (F.reify (F.normalize a)) (F.reify (F.normalize b)) :=
  (hR (F.reify_normalize a) (F.reify_normalize b)).symm

/-- A graph/NF theorem may be proved on normalized raw terms without missing any case. -/
theorem forall_normalize_iff (Q : Normal → Prop) :
    (∀ n, Q n) ↔ ∀ t, Q (F.normalize t) := by
  constructor
  · exact fun h t => h (F.normalize t)
  · intro h n
    simpa only [F.normalize_reify] using h (F.reify n)

theorem exists_normalize_iff (Q : Normal → Prop) :
    (∃ n, Q n) ↔ ∃ t, Q (F.normalize t) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨F.reify n, (F.normalize_reify n).symm ▸ hn⟩
  · rintro ⟨t, ht⟩
    exact ⟨F.normalize t, ht⟩

theorem forall₂_normalize_iff (Q : Normal → Normal → Prop) :
    (∀ a b, Q a b) ↔ ∀ a b, Q (F.normalize a) (F.normalize b) := by
  constructor
  · exact fun h a b => h (F.normalize a) (F.normalize b)
  · intro h a b
    simpa only [F.normalize_reify] using h (F.reify a) (F.reify b)

/-- Prove an invariant raw-term property once on all canonical representatives. -/
theorem forall_reify_iff {P : Raw → Prop} (hP : Invariant Equal P) :
    (∀ t, P t) ↔ ∀ n, P (F.reify n) := by
  constructor
  · exact fun h n => h (F.reify n)
  · exact fun h t => (F.predicate_iff hP t).mpr (h (F.normalize t))

theorem exists_reify_iff {P : Raw → Prop} (hP : Invariant Equal P) :
    (∃ t, P t) ↔ ∃ n, P (F.reify n) := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨F.normalize t, (F.predicate_iff hP t).mp ht⟩
  · rintro ⟨n, hn⟩
    exact ⟨F.reify n, hn⟩

theorem forall₂_reify_iff {R : Raw → Raw → Prop} (hR : Invariant₂ Equal R) :
    (∀ a b, R a b) ↔ ∀ a b, R (F.reify a) (F.reify b) := by
  constructor
  · exact fun h a b => h (F.reify a) (F.reify b)
  · exact fun h a b => (F.relation_iff hR a b).mpr (h (F.normalize a) (F.normalize b))

/-- Transfer a universally quantified theorem between separately defined predicates.
Only their compatibility on normalized terms must be established. -/
theorem forall_transfer {P : Raw → Prop} {Q : Normal → Prop}
    (compatible : ∀ t, P t ↔ Q (F.normalize t)) :
    (∀ t, P t) ↔ ∀ n, Q n := by
  rw [F.forall_normalize_iff]
  exact ⟨fun h t => (compatible t).mp (h t), fun h t => (compatible t).mpr (h t)⟩

theorem exists_transfer {P : Raw → Prop} {Q : Normal → Prop}
    (compatible : ∀ t, P t ↔ Q (F.normalize t)) :
    (∃ t, P t) ↔ ∃ n, Q n := by
  rw [F.exists_normalize_iff]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, (compatible t).mp ht⟩,
    fun ⟨t, ht⟩ => ⟨t, (compatible t).mpr ht⟩⟩

end NormalForm
end Generic

/-- A faithful interpretation: raw algebraic equality is equality of represented values.
Unlike `NormalForm`, this does not require surjectivity or a raw reifier. -/
structure EqualityModel (Raw : Type u) (Normal : Type v) (Equal : Raw → Raw → Prop) where
  normalize : Raw → Normal
  equal_iff : ∀ a b, Equal a b ↔ normalize a = normalize b

namespace EqualityModel

variable {Raw : Type u} {Normal : Type v} {Equal : Raw → Raw → Prop}
variable (M : EqualityModel Raw Normal Equal)

include M

theorem refl (a : Raw) : Equal a a := (M.equal_iff a a).mpr rfl

theorem symm {a b : Raw} (h : Equal a b) : Equal b a :=
  (M.equal_iff b a).mpr ((M.equal_iff a b).mp h).symm

theorem trans {a b c : Raw} (ab : Equal a b) (bc : Equal b c) : Equal a c :=
  (M.equal_iff a c).mpr (((M.equal_iff a b).mp ab).trans ((M.equal_iff b c).mp bc))

theorem unary_congr (f : Raw → Raw) (g : Normal → Normal)
    (commutes : ∀ a, M.normalize (f a) = g (M.normalize a))
    {a b : Raw} (h : Equal a b) : Equal (f a) (f b) := by
  rw [M.equal_iff, commutes, commutes, (M.equal_iff a b).mp h]

theorem unary_inj (f : Raw → Raw) (g : Normal → Normal)
    (commutes : ∀ a, M.normalize (f a) = g (M.normalize a))
    (injective : Function.Injective g) {a b : Raw} (h : Equal (f a) (f b)) :
    Equal a b := by
  apply (M.equal_iff a b).mpr
  apply injective
  simpa only [commutes] using (M.equal_iff (f a) (f b)).mp h

theorem binary_congr (f : Raw → Raw → Raw) (g : Normal → Normal → Normal)
    (commutes : ∀ a b, M.normalize (f a b) = g (M.normalize a) (M.normalize b))
    {a b c d : Raw} (ab : Equal a b) (cd : Equal c d) : Equal (f a c) (f b d) := by
  rw [M.equal_iff, commutes, commutes, (M.equal_iff a b).mp ab, (M.equal_iff c d).mp cd]

end EqualityModel

/-- A faithful interpretation that also preserves the ACUI addition operation. -/
structure AdditiveModel (Raw : Type u) (Normal : Type v) (Equal : Raw → Raw → Prop)
    (add : Raw → Raw → Raw) extends EqualityModel Raw Normal Equal where
  join : Normal → Normal → Normal
  map_add : ∀ a b, normalize (add a b) = join (normalize a) (normalize b)
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)
  join_comm : ∀ a b, join a b = join b a
  join_idem : ∀ a, join a a = a

namespace AdditiveModel

variable {Raw : Type u} {Normal : Type v} {Equal : Raw → Raw → Prop}
variable {add : Raw → Raw → Raw} (M : AdditiveModel Raw Normal Equal add)

include M

theorem add_congr {a b c d : Raw} (ab : Equal a b) (cd : Equal c d) :
    Equal (add a c) (add b d) :=
  M.toEqualityModel.binary_congr add M.join M.map_add ab cd

/-- Transfer additive inequality without requiring any extra order on raw syntax. -/
theorem below_iff (a b : Raw) :
    Equal (add a b) b ↔ M.join (M.normalize a) (M.normalize b) = M.normalize b := by
  rw [M.equal_iff, M.map_add]

theorem below_refl (a : Raw) : Equal (add a a) a :=
  (M.below_iff a a).mpr (M.join_idem _)

theorem below_trans {a b c : Raw} (ab : Equal (add a b) b) (bc : Equal (add b c) c) :
    Equal (add a c) c := by
  apply (M.below_iff a c).mpr
  have hab := (M.below_iff a b).mp ab
  have hbc := (M.below_iff b c).mp bc
  calc
    M.join (M.normalize a) (M.normalize c) =
        M.join (M.normalize a) (M.join (M.normalize b) (M.normalize c)) := by rw [hbc]
    _ = M.join (M.join (M.normalize a) (M.normalize b)) (M.normalize c) :=
      (M.join_assoc _ _ _).symm
    _ = M.normalize c := by rw [hab, hbc]

theorem below_antisymm {a b : Raw} (ab : Equal (add a b) b) (ba : Equal (add b a) a) :
    Equal a b :=
  (M.equal_iff a b).mpr
    (((M.below_iff b a).mp ba).symm.trans
      ((M.join_comm _ _).trans ((M.below_iff a b).mp ab)))

theorem equal_below {a b : Raw} (h : Equal a b) : Equal (add a b) b := by
  apply (M.below_iff a b).mpr
  rw [(M.equal_iff a b).mp h, M.join_idem]

theorem equal_iff_below_below (a b : Raw) :
    Equal a b ↔ Equal (add a b) b ∧ Equal (add b a) a :=
  ⟨fun h => ⟨M.equal_below h, M.equal_below (M.toEqualityModel.symm h)⟩,
    fun h => M.below_antisymm h.1 h.2⟩

end AdditiveModel

/-- A certified normal-form interface supplies a faithful equality interpretation. -/
def NormalForm.toEqualityModel {Raw : Type u} {Normal : Type v} {Equal : Raw → Raw → Prop}
    (F : NormalForm Raw Normal Equal) : EqualityModel Raw Normal Equal where
  normalize := F.normalize
  equal_iff := F.equal_iff_normalize_eq

end ACUIhE.Transfer
