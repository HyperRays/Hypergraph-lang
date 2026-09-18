import ACUIhE.Solver.Projection
import ACUIhE.Solver.Problem

set_option autoImplicit false

/-! Necessary equalities from uniquely matched, nonzero E summands. The
original equation is retained: this is neither positional cancellation nor
a bijective matching assumption. Constant tests reuse the existing solver
compatibility and positivity checks through the existing graph projection. -/

namespace ACUIhE.Solver.ForcedMatching
open ACUIh.Linear
universe u v w
variable {Const : Type u} {Var : Type v} {Hom : Type w}
variable [DecidableEq Const] [DecidableEq Hom]
local notation "Ty" => Term Const Var Hom
local notation "G" => Graph Const Empty Hom
local notation "Assignment" => Var → G

/-- The outer constant-word layer; E children contribute no such atoms. -/
def outer : Ty → ACUIh.Term Const Var Hom
  | .zero | .free _ => .zero
  | .const c => .const c
  | .var v => .var v
  | .add a b => .add (outer a) (outer b)
  | .hom h a => .hom h (outer a)

def noChildren : Fin 0 → G := Fin.elim0

theorem outer_project (t : Ty) (iv : Assignment) :
    instantiateNF (Projection.matrix noChildren iv) (lift (n := 0) (outer t)) =
      Projection.project noChildren (t.eval Graph.constant iv) := by
  induction t with
  | zero => exact (Projection.project_zero noChildren).symm
  | const c => exact (Projection.project_constant noChildren c).symm
  | var v => exact Row.toNF_ofNF _
  | add a b ia ib =>
    simpa only [outer, lift, instantiateNF, Term.eval, Projection.project_add] using
      congrArg₂ (· ∪ ·) ia ib
  | hom h a ih =>
    change ACUIh.NF.prepend h (instantiateNF (Projection.matrix noChildren iv) (lift (outer a))) =
      Projection.project noChildren (Graph.hom h (a.eval Graph.constant iv))
    rw [Projection.project_hom, ih]
  | free a ih =>
    change ∅ = Projection.project noChildren (Graph.free (a.eval Graph.constant iv))
    simp [Projection.project_free, ACUIESolver.Matching.WordRules.atoms]

theorem outer_compatible (a b : Ty) (iv : Assignment)
    (eq : a.eval Graph.constant iv = b.eval Graph.constant iv) :
    compatible (outer a) (outer b) = true := by
  have projected := congrArg (Projection.project noChildren) eq
  rw [← outer_project a iv, ← outer_project b iv] at projected
  simpa only [compatible_lift] using
    compatible_necessary (lift (n := 0) (outer a)) (lift (outer b))
      (Projection.matrix noChildren iv) projected

theorem outer_nonzero (a : Ty) (iv : Assignment) (required : hasConstant (outer a) = true) :
    a.eval Graph.constant iv ≠ 0 := by
  intro zero
  have present := constant_nonempty (lift (n := 0) (outer a))
    (Projection.matrix noChildren iv) (by simpa only [hasConstant_lift] using required)
  rw [outer_project, zero, Projection.project_zero] at present
  exact Finset.not_nonempty_empty present

/-- Collect all E children across association and zero; an exposed variable
or a different summand shape prevents this reduction. -/
def bodies : Ty → Option (List Ty)
  | .zero => some []
  | .free a => some [a]
  | .add a b => do return (← bodies a) ++ (← bodies b)
  | _ => none

def evalBodies (iv : Assignment) : List Ty → G
  | [] => 0
  | a :: rest => Graph.free (a.eval Graph.constant iv) + evalBodies iv rest

omit [DecidableEq Const] [DecidableEq Hom] in
theorem evalBodies_append (iv : Assignment) (as bs : List Ty) :
    evalBodies iv (as ++ bs) = evalBodies iv as + evalBodies iv bs := by
  induction as with
  | nil =>
    simp only [evalBodies, List.nil_append]
    rw [ACUIhE.add_comm (Hom := Hom) (0 : G), ACUIhE.add_zero (Hom := Hom)]
  | cons a as ih =>
    simp only [List.cons_append, evalBodies, ih, ACUIhE.add_assoc (Hom := Hom)]

omit [DecidableEq Const] [DecidableEq Hom] in
theorem bodies_eval (t : Ty) (xs : List Ty) (h : bodies t = some xs) (iv : Assignment) :
    t.eval Graph.constant iv = evalBodies iv xs := by
  induction t generalizing xs with
  | zero => cases Option.some.inj h; rfl
  | free a =>
    cases Option.some.inj h
    exact (ACUIhE.add_zero (Hom := Hom) (Graph.free (a.eval Graph.constant iv))).symm
  | const | var | hom => simp [bodies] at h
  | add a b ia ib =>
    cases ha : bodies a <;> cases hb : bodies b <;> simp [bodies, ha, hb] at h
    subst xs
    simp only [Term.eval, ia _ ha, ib _ hb, evalBodies_append]

theorem mem_evalBodies (iv : Assignment) (xs : List Ty) (s : Graph.Summand Const Empty Hom) :
    s ∈ (evalBodies iv xs).layer ↔
      ∃ b ∈ xs, s ∈ (Graph.free (b.eval Graph.constant iv)).layer := by
  induction xs with
  | nil => simp [evalBodies]
  | cons a as ih => simp [evalBodies, Graph.layer_add, ih]

theorem free_member_iff (a b : G) (ha : a ≠ 0) :
    ([], Sum.inr ⟨a, ha⟩) ∈ (Graph.free b).layer ↔ a = b := by
  by_cases hb : b = 0
  · subst b
    simp [show Graph.free (0 : G) = 0 from rfl, ha]
  · simp [Graph.layer_free_of_ne_zero b hb]

theorem match_exists (as bs : List Ty) (iv : Assignment)
    (eq : evalBodies iv as = evalBodies iv bs) (a : Ty) (member : a ∈ as)
    (nonzero : a.eval Graph.constant iv ≠ 0) :
    ∃ b ∈ bs, a.eval Graph.constant iv = b.eval Graph.constant iv := by
  have present : ([], Sum.inr ⟨a.eval Graph.constant iv, nonzero⟩) ∈ (evalBodies iv as).layer :=
    (mem_evalBodies iv as _).mpr ⟨a, member, (free_member_iff _ _ nonzero).mpr rfl⟩
  rw [eq] at present
  obtain ⟨b, hb, same⟩ := (mem_evalBodies iv bs _).mp present
  exact ⟨b, hb, (free_member_iff _ _ nonzero).mp same⟩

variable [DecidableEq Var]

def candidates (a : Ty) (bs : List Ty) : List Ty :=
  (bs.filter (fun b => compatible (outer a) (outer b))).dedup

def forced (a : Ty) (bs : List Ty) : Option Ty :=
  if hasConstant (outer a) then
    match candidates a bs with
    | [b] => some b
    | _ => none
  else none

theorem forced_spec (a : Ty) (bs : List Ty) (b : Ty) (h : forced a bs = some b) :
    hasConstant (outer a) = true ∧ candidates a bs = [b] := by
  unfold forced at h
  split at h
  · rename_i required
    cases hc : candidates a bs with
    | nil => simp [hc] at h
    | cons c cs =>
      cases cs with
      | nil => have same : c = b := by simpa [hc] using h
               exact ⟨required, by rw [same]⟩
      | cons d ds => simp [hc] at h
  · cases h

theorem forced_eq (as bs : List Ty) (iv : Assignment)
    (eq : evalBodies iv as = evalBodies iv bs) (a : Ty) (member : a ∈ as)
    (b : Ty) (h : forced a bs = some b) : a.eval Graph.constant iv = b.eval Graph.constant iv := by
  obtain ⟨required, only⟩ := forced_spec a bs b h
  obtain ⟨c, hc, same⟩ := match_exists as bs iv eq a member (outer_nonzero a iv required)
  have candidate : c ∈ candidates a bs := by
    exact List.mem_dedup.mpr (List.mem_filter.mpr ⟨hc, outer_compatible a c iv same⟩)
  rw [only, List.mem_singleton] at candidate
  subst c
  exact same

def derive (as bs : List Ty) : Problem Const Var Hom :=
  as.flatMap fun a => match forced a bs with
    | some b => [⟨a, b⟩]
    | none => []

theorem derive_sound (as bs : List Ty) (iv : Assignment)
    (eq : evalBodies iv as = evalBodies iv bs) : (derive as bs).IsSolution iv := by
  intro q hq
  obtain ⟨a, ha, hq⟩ := List.mem_flatMap.mp hq
  cases h : forced a bs with
  | none => simp [h] at hq
  | some b =>
    have same : q = ⟨a, b⟩ := by simpa [h] using hq
    subst q
    exact forced_eq as bs iv eq a ha b h

/-- Check both directions independently. Multiple summands may force the same
partner; no partner is consumed and no original constraint is removed. -/
def consequences (a b : Ty) : Problem Const Var Hom :=
  match bodies a, bodies b with
  | some as, some bs => derive as bs ++ derive bs as
  | _, _ => []

theorem consequences_sound (a b : Ty) (iv : Assignment)
    (eq : a.eval Graph.constant iv = b.eval Graph.constant iv) :
    (consequences a b).IsSolution iv := by
  cases ha : bodies a <;> cases hb : bodies b <;> simp only [consequences, ha, hb]
  all_goals try exact fun q hq => (List.not_mem_nil hq).elim
  rename_i as bs
  have same : evalBodies iv as = evalBodies iv bs :=
    (bodies_eval a as ha iv).symm.trans (eq.trans (bodies_eval b bs hb iv))
  intro q hq
  exact (List.mem_append.mp hq).elim (derive_sound as bs iv same q)
    (derive_sound bs as iv same.symm q)

def extra (p : Problem Const Var Hom) : Problem Const Var Hom :=
  p.flatMap (fun q => consequences q.left q.right)

theorem extra_sound (p : Problem Const Var Hom) (iv : Assignment) (valid : p.IsSolution iv) :
    (extra p).IsSolution iv := by
  intro q hq
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.mp hq
  exact consequences_sound r.left r.right iv (valid r hr) q hq

end ACUIhE.Solver.ForcedMatching
