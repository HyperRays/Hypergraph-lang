import ACUIhE.ACUIESolver.Matching.Search

/-!
# Compatibility interface for the replaced finite solver

These names now forward to ordered E-matching and Horn propagation. The old
row/rank enumerator has been removed; this module contains no alternate solver.
-/

namespace ACUIhE.ACUIESolver.Finite

universe u v
variable {Const : Type u} {Var : Type v} [DecidableEq Const] [DecidableEq Var]

abbrev findTable (p : Problem Const Var) := Matching.findTable p

theorem findTable_sound (p : Problem Const Var) {d : Table (pool p).length}
    (h : findTable p = some d) : Table.Valid (pool p) p d := Matching.findTable_sound p h

theorem findTable_none_iff (p : Problem Const Var) :
    findTable p = none ↔ ∀ d : Table (pool p).length, ¬ Table.Valid (pool p) p d := by
  rw [findTable, Matching.findTable_none_iff, unifiable_iff_exists_valid, not_exists]

theorem findTable_none_iff_not_unifiable (p : Problem Const Var) :
    findTable p = none ↔ ¬ p.Unifiable := Matching.findTable_none_iff p

abbrev unify (p : Problem Const Var) := Matching.unify p

theorem unify_sound (p : Problem Const Var) {σ : ACUIE.Substitution Const Var Var}
    (h : unify p = some σ) : p.IsUnifier σ := Matching.unify_sound p h

theorem unify_none_iff (p : Problem Const Var) : unify p = none ↔ ¬ p.Unifiable :=
  Matching.unify_none_iff p

theorem unify_complete (p : Problem Const Var) (h : p.Unifiable) :
    ∃ σ, unify p = some σ := Matching.unify_complete p h

end ACUIhE.ACUIESolver.Finite
