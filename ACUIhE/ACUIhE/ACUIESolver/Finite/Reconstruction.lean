import ACUIhE.ACUIESolver.Finite.Table

/-!
# Reconstruction from ranked finite constraints

The reconstruction function takes plain table data, not a correctness proof.
Its fixed iteration count follows from the finite ranks. Soundness is proved
separately for tables produced by the constraint solver.
-/

namespace ACUIhE.ACUIESolver.Finite.Table

universe u v w z
variable {Const : Type u} {Var : Type v} {Target : Type w}
variable [DecidableEq Const] [DecidableEq Var]

def atom (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    Nat → Fin ts.length → ACUIE.Term Const Target
  | 0, i => match ts.get i with
    | .const c => .const c
    | _ => .zero
  | k + 1, i => match ts.get i with
    | .const c => .const c
    | .free a => .free (join (atom ts d k) (lookup ts d a))
    | _ => .zero

theorem atom_const (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    {i : Fin ts.length} {c : Const} (h : ts.get i = .const c) (k : Nat) :
    atom (Target := Target) ts d k i = .const c := by cases k <;> simp only [atom, h]

theorem atom_free_succ (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    {i : Fin ts.length} {a : ACUIE.Term Const Var} (h : ts.get i = .free a) (k : Nat) :
    atom (Target := Target) ts d (k + 1) i = .free (join (atom ts d k) (lookup ts d a)) := by
  simp only [atom, h]

/-- Once the rank has been passed, further iterations do not change an atom. -/
theorem atom_stable (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (ranked : Ranked ts d) (k : Nat) (i : Fin ts.length) (bound : (d.rank i).val < k) :
    atom (Target := Target) ts d (k + 1) i = atom ts d k i := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases hi : ts.get i with
    | zero | const | var | add => simp only [atom, hi]
    | free a =>
      rw [atom_free_succ ts d hi, atom_free_succ ts d hi]
      congr 1
      apply join_congr
      intro j hj
      apply ih
      have lower := rank_child ranked hi hj
      change (d.rank j).val < (d.rank i).val at lower
      omega

def named (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    Fin ts.length → ACUIE.Term Const Target := atom ts d (ts.length + 1)

def decode (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (s : Finset (Fin ts.length)) : ACUIE.Term Const Target := join (named ts d) s

def reconstruct (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    ACUIE.Substitution Const Var Target := fun v => decode ts d (lookup ts d (.var v))

@[simp] theorem decode_empty (ts : List (ACUIE.Term Const Var)) (d : Table ts.length) :
    decode (Target := Target) ts d ∅ = .zero := join_empty _

theorem named_const (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    {i : Fin ts.length} {c : Const} (h : ts.get i = .const c) :
    named (Target := Target) ts d i = .const c := atom_const ts d h _

theorem named_free (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (ranked : Ranked ts d) {i : Fin ts.length} {a : ACUIE.Term Const Var}
    (h : ts.get i = .free a) :
    named (Target := Target) ts d i = .free (decode ts d (lookup ts d a)) := by
  rw [named, atom_free_succ ts d h]
  congr 1
  apply join_congr
  intro j hj
  symm
  apply atom_stable ts d ranked
  have lower := rank_child ranked h hj
  have upper := (d.rank i).isLt
  change (d.rank j).val < (d.rank i).val at lower
  omega

theorem eval_decode_union {α : Type z} [ACUIE α]
    (ts : List (ACUIE.Term Const Var)) (d : Table ts.length)
    (s t : Finset (Fin ts.length)) (ic : Const → α) (iv : Target → α) :
    (decode ts d (s ∪ t)).eval ic iv = (decode ts d s).eval ic iv + (decode ts d t).eval ic iv := by
  simp only [decode, eval_join, sum_union]

theorem eval_reconstruct {α : Type z} [ACUIE α]
    (ts : List (ACUIE.Term Const Var)) (p : Problem Const Var) (d : Table ts.length)
    (closed : Closed ts) (valid : Valid ts p d) (t : ACUIE.Term Const Var)
    (member : t ∈ ts) (ic : Const → α) (iv : Target → α) :
    (t.substitute (reconstruct ts d)).eval ic iv = (decode ts d (lookup ts d t)).eval ic iv := by
  induction t with
  | zero =>
    have row := row_of_mem valid member
    change lookup ts d .zero = ∅ at row
    rw [row, decode_empty]
    rfl
  | var v => rfl
  | const c =>
    have row := row_of_mem valid member
    change lookup ts d (.const c) = _ at row
    change ic c = (decode ts d (lookup ts d (.const c))).eval ic iv
    rw [row, decode, eval_join]
    symm
    apply sum_constant
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp member
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    · intro i hi
      have eq : ts.get i = .const c := (Finset.mem_filter.mp hi).2
      rw [named_const ts d eq]
      rfl
  | add a b ha hb =>
    have row := row_of_mem valid member
    change lookup ts d (.add a b) = lookup ts d a ∪ lookup ts d b at row
    change (a.substitute _).eval ic iv + (b.substitute _).eval ic iv = _
    rw [row, eval_decode_union]
    exact congrArg₂ (· + ·) (ha (closed.add_left member)) (hb (closed.add_right member))
  | free a ha =>
    have row := row_of_mem valid member
    change (lookup ts d (.free a) = ∅ → lookup ts d a = ∅) ∧ _ at row
    change ACUIE.E ((a.substitute _).eval ic iv) = _
    rw [ha (closed.free_body member)]
    by_cases empty : lookup ts d (.free a) = ∅
    · rw [empty, row.1 empty, decode_empty]
      exact ACUIE.E_zero
    · conv_rhs => rw [decode, eval_join]
      symm
      apply sum_constant _ _ _ (Finset.nonempty_iff_ne_empty.mpr empty)
      intro j hj
      have compatible := row.2 j hj
      unfold Compatible at compatible
      cases hjt : ts.get j with
      | zero | const | var | add => simp only [hjt] at compatible
      | free b =>
        have eq : lookup ts d b = lookup ts d a := by simpa only [hjt] using compatible
        rw [named_free ts d valid.2.1 hjt, eq]
        rfl

/-- A satisfying finite table constructs a genuine unifier in the unchanged theory. -/
theorem reconstruct_sound (p : Problem Const Var) (d : Table (pool p).length)
    (valid : Valid (pool p) p d) : p.IsUnifier (reconstruct (Target := Target) (pool p) d) := by
  intro q hq α _ ic iv
  rw [eval_reconstruct (pool p) p d (pool_closed p) valid q.left (pool_left p hq),
    eval_reconstruct (pool p) p d (pool_closed p) valid q.right (pool_right p hq), valid.2.2 q hq]

end ACUIhE.ACUIESolver.Finite.Table
