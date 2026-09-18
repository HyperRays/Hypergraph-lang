import ACUIhE.ACUIESolver.Finite.Reconstruction
import ACUIhE.ACUIESolver.Matching.Iteration

/-!
# Cached bottom-up reconstruction

Each round builds an array of named terms once and refers to the previous
array's terms when constructing E children. This avoids recursively recomputing
the same named dependency. The cache agrees exactly (syntactically) with the
semantic reconstruction already proved correct, at every round and index.
-/

namespace ACUIhE.ACUIESolver.Matching

open ACUIhE.ACUIESolver.Finite

universe u v w
variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Var]

def atomCache (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    Nat → Vector (ACUIE.Term Const Target) ts.length :=
  Iteration.run (Table.atom ts d 0) (fun previous i => match ts.get i with
      | .const c => .const c
      | .free a => .free (join previous (Table.lookup ts d a))
      | _ => .zero)

theorem atomCache_eq (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (k : Nat) (i : Fin ts.length) :
    (atomCache (Target := Target) ts d k)[i.val] = Table.atom ts d k i := by
  induction k generalizing i with
  | zero => simp only [atomCache, Iteration.run_zero]
  | succ k ih =>
    simp only [atomCache, Iteration.run_succ, Table.atom]
    cases hi : ts.get i with
    | zero | const | var | add => rfl
    | free a =>
      dsimp only
      congr 1
      apply join_congr
      intro j _
      exact ih j

def reconstruct (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    ACUIE.Substitution Const Var Target :=
  let cached := atomCache ts d (ts.length + 1)
  fun v => join (fun i => cached[i.val]) (Table.lookup ts d (.var v))

theorem reconstruct_eq (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    reconstruct (Target := Target) ts d = Table.reconstruct ts d := by
  funext v
  apply join_congr
  intro i _
  exact atomCache_eq ts d (ts.length + 1) i

theorem reconstruct_sound (p : Problem Const Var) (d : Table (pool p).length)
    (h : Table.Valid (pool p) p d) : p.IsUnifier (reconstruct (Target := Target) (pool p) d) := by
  rw [reconstruct_eq]
  exact Table.reconstruct_sound p d h

end ACUIhE.ACUIESolver.Matching
