import ACUIhE.ACUIESolver.Matching.FiniteRules
import ACUIhE.ACUIESolver.Finite.Table
import Mathlib.Data.List.FinRange

/-!
# Ordered E-matching branches as flat layer constraints

Only E labels are searched. Label zero commits an E node to zero; equal
positive labels identify E nodes. Labels also order dependencies. The layer
solver computes every occurrence row, including all shared-variable rows.

The exact compiler theorem connects these constraints to the existing semantic
reconstruction interface. No substitution is constructed or validated here.
-/

namespace ACUIhE.ACUIESolver.Matching

open ACUIhE.ACUIESolver.Finite Layers

universe u v
variable {Const : Type u} {Var : Type v} [DecidableEq Const] [DecidableEq Var]

abbrev Labels (n : Nat) := Fin n → Fin (n + 1)

def isEdge : ACUIE.Term Const Var → Bool
  | .free _ => true
  | _ => false

def edges (ts : List (ACUIE.Term Const Var)) : Finset (Fin ts.length) :=
  Finset.univ.filter (fun i => isEdge (ts.get i) = true)

def edgeCount (ts : List (ACUIE.Term Const Var)) : Nat := (edges ts).card

def names (ts : List (ACUIE.Term Const Var)) (labels : Labels ts.length)
    (i : Fin ts.length) : Finset (Fin ts.length) :=
  Rules.group (edges ts) labels i

omit [DecidableEq Const] [DecidableEq Var] in
@[simp] theorem mem_names (ts : List (ACUIE.Term Const Var)) (labels : Labels ts.length)
    (i j : Fin ts.length) : j ∈ names ts labels i ↔
      isEdge (ts.get j) = true ∧ labels j = labels i ∧ labels i ≠ 0 := by simp [names, edges]

def table (labels : Labels n) (rows : Rows n) : Table n := ⟨rows, labels⟩

def lookupExpr (ts : List (ACUIE.Term Const Var)) (t : ACUIE.Term Const Var) : Expr ts.length :=
  ⟨∅, Finset.univ.filter (fun i => ts.get i = t)⟩

@[simp] theorem eval_lookupExpr (ts : List (ACUIE.Term Const Var)) (t : ACUIE.Term Const Var)
    (labels : Labels ts.length) (rows : Rows ts.length) :
    (lookupExpr ts t).eval rows = Table.lookup ts (table labels rows) t := by
  simp [lookupExpr, Expr.eval, Table.lookup, table]

def childExpr (ts : List (ACUIE.Term Const Var)) (j : Fin ts.length) : Expr ts.length :=
  match ts.get j with
  | .free b => lookupExpr ts b
  | _ => Expr.atoms ∅

theorem compatibleConstraints_exact (ts : List (ACUIE.Term Const Var))
    (labels : Labels ts.length) (rows : Rows ts.length) (a : ACUIE.Term Const Var)
    (i : Fin ts.length) :
    Holds (((List.finRange ts.length).filter (fun j => j ∈ names ts labels i)).flatMap
      (fun j => equation (childExpr ts j) (lookupExpr ts a))) rows ↔
      ∀ j ∈ names ts labels i, Table.Compatible ts (table labels rows) a j := by
  rw [holds_flatMap]
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro hj
  have edge := ((mem_names ts labels i j).mp hj).1
  cases he : ts.get j <;> simp only [he, isEdge, Bool.false_eq_true] at edge
  rename_i b
  simp only [childExpr, he, holds_equation, eval_lookupExpr ts (labels := labels),
    Table.Compatible]

def lower (labels : Labels n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => labels j < labels i)

def nodeConstraints (ts : List (ACUIE.Term Const Var)) (labels : Labels ts.length)
    (i : Fin ts.length) : System ts.length :=
  let self := lookupExpr ts (ts.get i)
  match ts.get i with
  | .zero => equation self (Expr.atoms ∅)
  | .var _ => []
  | .const c => equation self (Expr.atoms (Finset.univ.filter (fun j => ts.get j = .const c)))
  | .add a b => equation self ((lookupExpr ts a).union (lookupExpr ts b))
  | .free a =>
    FiniteRules.compile (Rules.complete self (lookupExpr ts a) (childExpr ts)
      (names ts labels i) (lower labels i))

def ExactNames (ts : List (ACUIE.Term Const Var)) (labels : Labels ts.length)
    (rows : Rows ts.length) : Prop :=
  ∀ i, isEdge (ts.get i) = true →
    Table.lookup ts (table labels rows) (ts.get i) = names ts labels i

theorem nodeConstraints_exact (ts : List (ACUIE.Term Const Var)) (labels : Labels ts.length)
    (rows : Rows ts.length) (i : Fin ts.length) :
    Holds (nodeConstraints ts labels i) rows ↔
      Table.Row ts (table labels rows) (ts.get i) ∧
      Table.RankRow ts (table labels rows) i ∧
      (isEdge (ts.get i) = true →
        Table.lookup ts (table labels rows) (ts.get i) = names ts labels i) := by
  cases hi : ts.get i with
  | zero => simp [nodeConstraints, hi, Table.Row, Table.RankRow, isEdge, eval_lookupExpr ts (labels := labels), -List.get_eq_getElem]
  | var x => simp [nodeConstraints, hi, Table.Row, Table.RankRow, isEdge, -List.get_eq_getElem]
  | const c => simp [nodeConstraints, hi, Table.Row, Table.RankRow, isEdge, eval_lookupExpr ts (labels := labels), -List.get_eq_getElem]
  | add a b => simp [nodeConstraints, hi, Table.Row, Table.RankRow, isEdge, eval_lookupExpr ts (labels := labels), -List.get_eq_getElem]
  | free a =>
    have conditional : Holds (if names ts labels i = ∅ then
        equation (lookupExpr ts a) (Expr.atoms ∅) else []) rows ↔
        (names ts labels i = ∅ → Table.lookup ts (table labels rows) a = ∅) := by
      split_ifs <;> simp_all only [holds_equation, eval_lookupExpr ts (labels := labels), Expr.eval_atoms, holds_nil,
        true_implies, false_implies]
    simp only [nodeConstraints, hi, FiniteRules.compile_complete, holds_append, holds_equation,
      eval_lookupExpr ts (labels := labels),
      Expr.eval_atoms, conditional, compatibleConstraints_exact, Table.Row, Table.RankRow,
      isEdge, eq_self, true_implies]
    have rank : Holds [(lookupExpr ts a, Expr.atoms (lower labels i))] rows ↔
        ∀ j ∈ Table.lookup ts (table labels rows) a, labels j < labels i := by
      simp [Holds, eval_lookupExpr ts (labels := labels), lower, Finset.subset_iff]
    rw [rank]
    change (((_ ∧ _) ∧ _) ∧ _) ↔ (((_ → _) ∧ _) ∧ _ ∧ _)
    constructor
    · rintro ⟨⟨⟨he, hz⟩, hc⟩, hr⟩
      refine ⟨⟨?_, ?_⟩, hr, he⟩
      · simpa only [he] using hz
      · simpa only [he] using hc
    · rintro ⟨⟨hz, hc⟩, hr, he⟩
      refine ⟨⟨⟨he, ?_⟩, ?_⟩, hr⟩
      · simpa only [he] using hz
      · simpa only [he] using hc

def constraints (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (labels : Labels ts.length) : System ts.length :=
  (List.finRange ts.length).flatMap (nodeConstraints ts labels) ++
  p.flatMap (fun q => equation (lookupExpr ts q.left) (lookupExpr ts q.right))

theorem constraints_exact (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (labels : Labels ts.length) (rows : Rows ts.length) :
    Holds (constraints ts p labels) rows ↔
      Table.Valid ts p (table labels rows) ∧ ExactNames ts labels rows := by
  simp only [constraints, holds_append, holds_flatMap, List.mem_finRange, forall_true_left,
    nodeConstraints_exact, holds_equation, eval_lookupExpr ts (labels := labels), Table.Valid, Table.Ranked, ExactNames]
  aesop

def solveBranch (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (labels : Labels ts.length) : Option (Table ts.length) :=
  (Layers.solve (constraints ts p labels)).map (table labels)

theorem solveBranch_sound (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (labels : Labels ts.length) {d : Table ts.length} (h : solveBranch ts p labels = some d) :
    Table.Valid ts p d := by
  obtain ⟨rows, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ((constraints_exact ts p labels rows).mp (Layers.solve_sound _ hr)).1

theorem solveBranch_complete (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var)
    (labels : Labels ts.length) (rows : Rows ts.length)
    (valid : Table.Valid ts p (table labels rows)) (exactNames : ExactNames ts labels rows) :
    ∃ d, solveBranch ts p labels = some d := by
  obtain ⟨r, hr⟩ := Layers.solve_complete _ ((constraints_exact ts p labels rows).mpr ⟨valid, exactNames⟩)
  exact ⟨table labels r, by simp [solveBranch, hr]⟩

end ACUIhE.ACUIESolver.Matching
