import ACUIhE.ACUIESolver.Matching.Constraints

/-!
# Canonical ranks for ordered groups

A positive group's rank is the number of elements in that group and all lower
positive groups. Thus ranks are determined by the ordered groups, not chosen
numeric labels. Canonicalization preserves zero, equality and strict order,
and therefore preserves the full matching constraints exactly.
-/

namespace ACUIhE.ACUIESolver.Matching

open ACUIhE.ACUIESolver.Finite Layers

variable {n : Nat}

def canonicalizeLabels (labels : Labels n) : Labels n := fun i =>
  ⟨(Finset.univ.filter (fun j => labels j ≠ 0 ∧ labels j ≤ labels i)).card,
    Nat.lt_succ_of_le (by simpa using (Finset.card_le_univ
      (Finset.univ.filter (fun j => labels j ≠ 0 ∧ labels j ≤ labels i))))⟩

theorem canonicalizeLabels_strict {labels : Labels n} {i j : Fin n}
    (h : labels i < labels j) : canonicalizeLabels labels i < canonicalizeLabels labels j := by
  change (Finset.univ.filter (fun k => labels k ≠ 0 ∧ labels k ≤ labels i)).card <
    (Finset.univ.filter (fun k => labels k ≠ 0 ∧ labels k ≤ labels j)).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨hk.1, le_trans hk.2 h.le⟩
  · intro he
    have hn : labels j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) h)
    have hj : j ∈ Finset.univ.filter (fun k => labels k ≠ 0 ∧ labels k ≤ labels j) := by simp [hn]
    rw [← he] at hj
    have hh := (Finset.mem_filter.mp hj).2.2
    exact (not_le_of_gt h) hh

@[simp] theorem canonicalizeLabels_zero (labels : Labels n) (i : Fin n) :
    canonicalizeLabels labels i = 0 ↔ labels i = 0 := by
  constructor
  · intro h
    by_contra hn
    have hi : i ∈ Finset.univ.filter (fun j => labels j ≠ 0 ∧ labels j ≤ labels i) := by simp [hn]
    have hp := Finset.card_pos.mpr ⟨i, hi⟩
    have hv := congrArg Fin.val h
    change (Finset.univ.filter (fun j => labels j ≠ 0 ∧ labels j ≤ labels i)).card = 0 at hv
    omega
  · intro h
    apply Fin.ext
    simp [canonicalizeLabels, h]

@[simp] theorem canonicalizeLabels_eq (labels : Labels n) (i j : Fin n) :
    canonicalizeLabels labels i = canonicalizeLabels labels j ↔ labels i = labels j := by
  constructor
  · intro h
    rcases lt_trichotomy (labels i) (labels j) with hi | he | hj
    · exact ((ne_of_lt (canonicalizeLabels_strict hi)) h).elim
    · exact he
    · exact ((ne_of_gt (canonicalizeLabels_strict hj)) h).elim
  · intro h
    apply Fin.ext
    simp only [canonicalizeLabels, h]

@[simp] theorem canonicalizeLabels_lt (labels : Labels n) (i j : Fin n) :
    canonicalizeLabels labels i < canonicalizeLabels labels j ↔ labels i < labels j := by
  constructor
  · intro h
    rcases lt_trichotomy (labels i) (labels j) with hi | he | hj
    · exact hi
    · exact (ne_of_lt h ((canonicalizeLabels_eq labels i j).mpr he)).elim
    · exact (lt_asymm h (canonicalizeLabels_strict hj)).elim
  · exact canonicalizeLabels_strict

@[simp] theorem canonicalizeLabels_le (labels : Labels n) (i j : Fin n) :
    canonicalizeLabels labels i ≤ canonicalizeLabels labels j ↔ labels i ≤ labels j := by
  simp only [le_iff_lt_or_eq, canonicalizeLabels_lt, canonicalizeLabels_eq]

@[simp] theorem canonicalizeLabels_idempotent (labels : Labels n) :
    canonicalizeLabels (canonicalizeLabels labels) = canonicalizeLabels labels := by
  funext i
  apply Fin.ext
  change (Finset.univ.filter (fun j => canonicalizeLabels labels j ≠ 0 ∧
    canonicalizeLabels labels j ≤ canonicalizeLabels labels i)).card = _
  simp only [ne_eq, canonicalizeLabels_zero, canonicalizeLabels_le]
  rfl

def CanonicalLabels (labels : Labels n) : Prop := canonicalizeLabels labels = labels

/-- Ordered groups have one canonical encoding, regardless of original numeric labels. -/
theorem canonicalLabels_unique {a b : Labels n} (ha : CanonicalLabels a) (hb : CanonicalLabels b)
    (hz : ∀ i, a i = 0 ↔ b i = 0) (ho : ∀ i j, a i ≤ a j ↔ b i ≤ b j) : a = b := by
  rw [← ha, ← hb]
  funext i
  apply Fin.ext
  change (Finset.univ.filter (fun j => a j ≠ 0 ∧ a j ≤ a i)).card =
    (Finset.univ.filter (fun j => b j ≠ 0 ∧ b j ≤ b i)).card
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, hz, ho]

universe u v
variable {Const : Type u} {Var : Type v} [DecidableEq Const] [DecidableEq Var]

omit [DecidableEq Const] [DecidableEq Var] in
@[simp] theorem names_canonicalize (ts : List (ACUIE.Term Const Var))
    (labels : Labels ts.length) (i : Fin ts.length) :
    names ts (canonicalizeLabels labels) i = names ts labels i := by
  ext j
  simp only [mem_names, canonicalizeLabels_eq, ne_eq, canonicalizeLabels_zero]

@[simp] theorem lower_canonicalize (labels : Labels n) (i : Fin n) :
    lower (canonicalizeLabels labels) i = lower labels i := by
  ext j
  simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and, canonicalizeLabels_lt]

theorem nodeConstraints_canonicalize (ts : List (ACUIE.Term Const Var))
    (labels : Labels ts.length) (i : Fin ts.length) :
    nodeConstraints ts (canonicalizeLabels labels) i = nodeConstraints ts labels i := by
  unfold nodeConstraints
  cases ts.get i <;> simp only [names_canonicalize, lower_canonicalize]

/-- Symmetry removal preserves the flat system itself, not merely satisfiability. -/
theorem constraints_canonicalize (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (labels : Labels ts.length) :
    constraints ts p (canonicalizeLabels labels) = constraints ts p labels := by
  have hn : nodeConstraints ts (canonicalizeLabels labels) = nodeConstraints ts labels :=
    funext (nodeConstraints_canonicalize ts labels)
  simp only [constraints, hn]

end ACUIhE.ACUIESolver.Matching
