import ACUIhE.Solver.Decomposition

/-! Eliminate explicitly determined variables, preserving the entire coupled
problem. Retain the substituted defining equation and reconstruct eliminated
bindings in reverse order. No guessed substitution is committed. -/

namespace ACUIhE.Solver.Elimination
universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
local notation "Ty" => Term Const Var Hom
local notation "Assignment" => Var → Graph Const Empty Hom

def freeVars : Ty → List Var
  | .zero | .const _ => []
  | .var v => [v]
  | .add a b => freeVars a ++ freeVars b
  | .hom _ a | .free a => freeVars a

def problemVariables (p : Problem Const Var Hom) : List Var :=
  (p.flatMap (fun q => freeVars q.left ++ freeVars q.right)).dedup

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
theorem eval_agrees {A : Type*} [ACUIhE Hom A] (t : Ty) (ic : Const → A)
    (iv jv : Var → A) (same : ∀ v ∈ freeVars t, iv v = jv v) :
    t.eval ic iv = t.eval ic jv := by
  induction t with
  | zero | const => rfl
  | var v => exact same v (by simp [freeVars])
  | add a b ia ib =>
    simp only [Term.eval]
    rw [ia (fun v h => same v (List.mem_append_left _ h)),
      ib (fun v h => same v (List.mem_append_right _ h))]
  | hom h a ih => exact congrArg (H h) (ih same)
  | free a ih => exact congrArg (E (Hom := Hom)) (ih same)

/-- Reject only a closed equation whose canonical ground values differ. -/
def groundCheck (p : Problem Const Var Hom) : Bool := p.all fun q =>
  if freeVars q.left = [] ∧ freeVars q.right = [] then
    decide (q.left.eval Graph.constant (fun _ => (0 : Graph Const Empty Hom)) =
      q.right.eval Graph.constant (fun _ => (0 : Graph Const Empty Hom)))
  else true

omit [DecidableEq Var] in
theorem groundCheck_complete (p : Problem Const Var Hom) (iv : Assignment)
    (valid : p.IsSolution iv) : groundCheck p = true := by
  apply List.all_eq_true.mpr
  intro q hq
  split_ifs with closed
  · apply decide_eq_true
    have left := eval_agrees q.left Graph.constant iv (fun _ => (0 : Graph Const Empty Hom))
      (by simp [closed.1])
    have right := eval_agrees q.right Graph.constant iv (fun _ => (0 : Graph Const Empty Hom))
      (by simp [closed.2])
    exact left.symm.trans ((valid q hq).trans right)
  · rfl

def binding (v : Var) (q : Equation Const Var Hom) : Option Ty :=
  match q.left, q.right with
  | .var w, t => if w = v ∧ v ∉ freeVars t then some t else none
  | t, .var w => if w = v ∧ v ∉ freeVars t then some t else none
  | _, _ => none

omit [DecidableEq Const] [DecidableEq Hom] in
theorem binding_value (v : Var) (q : Equation Const Var Hom) (t : Ty)
    (h : binding v q = some t) (iv : Assignment) (valid : q.Holds Graph.constant iv) :
    iv v = t.eval Graph.constant iv := by
  rcases q with ⟨a, b⟩
  cases a <;> cases b <;> simp only [binding, Equation.left, Equation.right] at h
  all_goals try cases h
  all_goals (split_ifs at h; simp_all [Equation.Holds, Generic.Equation.Holds, Term.eval])
  all_goals subst t; simp_all [Term.eval]

def pick (v : Var) : Problem Const Var Hom → Option Ty
  | [] => none
  | q :: rest => (binding v q).orElse (fun _ => pick v rest)

omit [DecidableEq Const] [DecidableEq Hom] in
theorem pick_value (v : Var) (p : Problem Const Var Hom) (t : Ty)
    (h : pick v p = some t) (iv : Assignment) (valid : p.IsSolution iv) :
    iv v = t.eval Graph.constant iv := by
  induction p with
  | nil => simp [pick] at h
  | cons q rest ih =>
    cases hb : binding v q with
    | none =>
      apply ih (by simpa [pick, hb] using h)
      exact fun r hr => valid r (List.mem_cons_of_mem _ hr)
    | some value =>
      have same : value = t := by simpa [pick, hb] using h
      subst value
      exact binding_value v q t hb iv (valid q (by simp))

def substitution (v : Var) (t : Ty) (w : Var) : Ty := if w = v then t else .var w

def extend (v : Var) (t : Ty) (iv : Assignment) : Assignment :=
  fun w => (substitution v t w).eval Graph.constant iv

def rewrite (v : Var) (t : Ty) (p : Problem Const Var Hom) : Problem Const Var Hom :=
  p.map (fun q => ⟨q.left.substitute (substitution v t), q.right.substitute (substitution v t)⟩)

omit [DecidableEq Const] [DecidableEq Hom] in
theorem rewrite_correct (v : Var) (t : Ty) (p : Problem Const Var Hom) (iv : Assignment) :
    (rewrite v t p).IsSolution iv ↔ p.IsSolution (extend v t iv) := by
  simp only [rewrite, Problem.IsSolution, Problem.Holds, List.forall_mem_map,
    Equation.Holds, Generic.Equation.Holds, Term.eval_substitute]
  rfl

omit [DecidableEq Const] [DecidableEq Hom] in
theorem extend_eq (v : Var) (p : Problem Const Var Hom) (t : Ty)
    (h : pick v p = some t) (iv : Assignment) (valid : p.IsSolution iv) :
    extend v t iv = iv := by
  funext w
  simp only [extend, substitution]
  split_ifs with same
  · subst w
    exact (pick_value v p t h iv valid).symm
  · rfl

structure Result (Const : Type u) (Var : Type v) (Hom : Type w) where
  problem : Problem Const Var Hom
  restore : (Var → Graph Const Empty Hom) → (Var → Graph Const Empty Hom)

/-- Find a currently determined variable. Variables without a binding remain
pending, since another elimination can expose a binding for them. -/
def select : List Var → Problem Const Var Hom → Option (Var × Ty)
  | [], _ => none
  | v :: vs, p =>
      match pick v p with
      | none => select vs p
      | some t => some (v, t)

omit [DecidableEq Const] [DecidableEq Hom] in
theorem select_spec (vs : List Var) (p : Problem Const Var Hom) (v : Var) (t : Ty)
    (found : select vs p = some (v, t)) : v ∈ vs ∧ pick v p = some t := by
  induction vs with
  | nil => simp [select] at found
  | cons w ws ih =>
    cases hp : pick w p with
    | none =>
      obtain ⟨member, chosen⟩ := ih (by simpa [select, hp] using found)
      exact ⟨List.mem_cons_of_mem _ member, chosen⟩
    | some a =>
      have same : (w, a) = (v, t) := by simpa [select, hp] using found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ⟨by simp, hp⟩

omit [DecidableEq Const] [DecidableEq Hom] in
theorem select_progress (vs : List Var) (p : Problem Const Var Hom) (v : Var) (t : Ty)
    (found : select vs p = some (v, t)) : (vs.erase v).length < vs.length := by
  have smaller := List.length_erase_add_one (select_spec vs p v t found).1
  omega

/-- Every recursive step removes a selected input variable. No iteration
budget is used; termination follows from the pending list's strict decrease. -/
def go (vs : List Var) (p : Problem Const Var Hom) : Result Const Var Hom :=
  match _found : select vs p with
  | none => ⟨p, id⟩
  | some (v, t) =>
      let r := go (vs.erase v) (Decomposition.run (rewrite v t p))
      ⟨r.problem, fun iv => extend v t (r.restore iv)⟩
termination_by vs.length
decreasing_by exact select_progress vs p v t _found

theorem go_sound (vs : List Var) (p : Problem Const Var Hom) (iv : Assignment)
    (valid : (go vs p).problem.IsSolution iv) : p.IsSolution ((go vs p).restore iv) := by
  cases found : select vs p with
  | none => rw [go, found] at valid ⊢; exact valid
  | some pair =>
    obtain ⟨v, t⟩ := pair
    rw [go, found] at valid ⊢
    have sub := go_sound (vs.erase v) (Decomposition.run (rewrite v t p)) iv valid
    have rewritten := (Decomposition.run_correct _ _).mp sub
    exact (rewrite_correct v t p _).mp rewritten
termination_by vs.length
decreasing_by exact select_progress vs p v t found

theorem go_complete (vs : List Var) (p : Problem Const Var Hom) (iv : Assignment)
    (valid : p.IsSolution iv) : (go vs p).problem.IsSolution iv := by
  cases found : select vs p with
  | none => rw [go, found]; exact valid
  | some pair =>
    obtain ⟨v, t⟩ := pair
    rw [go, found]
    have chosen := (select_spec vs p v t found).2
    have rewritten : (rewrite v t p).IsSolution iv :=
      (rewrite_correct v t p iv).mpr ((extend_eq v p t chosen iv valid).symm ▸ valid)
    have decomp := (Decomposition.run_correct _ iv).mpr rewritten
    exact go_complete (vs.erase v) _ iv decomp
termination_by vs.length
decreasing_by exact select_progress vs p v t found

def run (p : Problem Const Var Hom) : Result Const Var Hom :=
  go (problemVariables p) (Decomposition.run p)

theorem run_sound (p : Problem Const Var Hom) (iv : Assignment)
    (valid : (run p).problem.IsSolution iv) : p.IsSolution ((run p).restore iv) :=
  (Decomposition.run_correct p _).mp (go_sound _ _ iv valid)

theorem run_complete (p : Problem Const Var Hom) (iv : Assignment)
    (valid : p.IsSolution iv) : (run p).problem.IsSolution iv :=
  go_complete _ _ iv ((Decomposition.run_correct p iv).mpr valid)

theorem run_unifiable_iff (p : Problem Const Var Hom) :
    (run p).problem.Unifiable ↔ p.Unifiable := by
  rw [Problem.unifiable_iff_graph, Problem.unifiable_iff_graph]
  exact ⟨fun ⟨iv, h⟩ => ⟨_, run_sound p iv h⟩,
    fun ⟨iv, h⟩ => ⟨iv, run_complete p iv h⟩⟩

end ACUIhE.Solver.Elimination
