import ACUIhE.Solver

set_option autoImplicit false

/-!
A small experiment in checking parameters as temporary constants.

Run from Hypergraph-ml/lean: `lake env lean QuantifierPrototype.lean`

The terms, equality, substitution, O constructors, and solver are ACUIhE's.
`Free ⊕ Param` records which variables a scope binds. `freeze` moves only
those parameters into a disjoint constant namespace for a solver call.
Instantiation uses the existing substitution on the original scoped term.

This verifies the scope operations and explicit example constraints. It does
not infer which parameters a let-binding may generalize or translate an AST.
-/

namespace QuantifierPrototype
open ACUIhE

section Scope

variable {C F P H : Type}

/-- Move bound parameters to fresh constants; keep free unknowns solvable.
This changes names and their roles, not any algebraic operation. -/
def freeze : Term C (F ⊕ P) H → Term (C ⊕ P) F H
  | .zero => .zero
  | .const c => .const (.inl c)
  | .var (.inl v) => .var v
  | .var (.inr p) => .const (.inr p)
  | .add a b => .add (freeze a) (freeze b)
  | .hom h a => .hom h (freeze a)
  | .free a => .free (freeze a)

/-- Each use chooses arguments for this scope's parameters. Free names stay shared. -/
def instantiate (t : Term C (F ⊕ P) H) (args : P → Term C F H) : Term C F H :=
  t.substitute (Sum.elim Term.var args)

theorem eval_freeze {A : Type} [ACUIhE H A]
    (t : Term C (F ⊕ P) H) (ic : C ⊕ P → A) (iv : F → A) :
    (freeze t).eval ic iv =
      t.eval (fun c => ic (.inl c)) (Sum.elim iv (fun p => ic (.inr p))) := by
  induction t with
  | var v => cases v <;> rfl
  | zero | const => rfl
  | add a b ha hb => simp only [freeze, Term.eval, ha, hb]
  | hom h a ha => simp only [freeze, Term.eval, ha]
  | free a ha => simp only [freeze, Term.eval, ha]

/-- An equality checked with arbitrary parameter constants holds at every
instantiation, including arguments containing free variables, sums, h, and E. -/
theorem frozen_equal_instantiates {a b : Term C (F ⊕ P) H}
    (checked : (freeze a).Equal (freeze b)) (args : P → Term C F H) :
    (instantiate a args).Equal (instantiate b args) := by
  intro A _ ic iv
  have h := checked (Sum.elim ic (fun p => (args p).eval ic iv)) iv
  simp only [eval_freeze, Sum.elim_inl, Sum.elim_inr] at h
  have env : (fun v => (Sum.elim Term.var args v).eval ic iv) =
      Sum.elim iv (fun p => (args p).eval ic iv) := by
    funext v
    cases v <;> rfl
  simp only [instantiate, Term.eval_substitute, env]
  exact h

def freezeProblem (p : Solver.Problem C (F ⊕ P) H) : Solver.Problem (C ⊕ P) F H :=
  p.map fun q => ⟨freeze q.left, freeze q.right⟩

/-- A successful frozen check gives a solution for EVERY interpretation of
the parameters. Local unknowns may depend on those parameters in the answer.
This is a consequence of the existing solver's soundness theorem.
It is not permission to generalize variables belonging to an enclosing binding. -/
theorem frozen_solve_sound [DecidableEq C] [DecidableEq F]
    [DecidableEq P] [DecidableEq H]
    (p : Solver.Problem C (F ⊕ P) H)
    {solution : F → Graph (C ⊕ P) Empty H}
    (found : Solver.solve (freezeProblem p) = some solution)
    {A : Type} [ACUIhE H A] (ic : C → A) (params : P → A) :
    p.Holds ic (Sum.elim
      (fun v => Graph.eval (Sum.elim ic params) Empty.elim (solution v)) params) := by
  intro q hq
  have h := Solver.solve_sound_eval (freezeProblem p) found (Sum.elim ic params)
    ⟨freeze q.left, freeze q.right⟩ (List.mem_map.mpr ⟨q, hq, rfl⟩)
  change (freeze q.left).eval _ _ = (freeze q.right).eval _ _ at h
  simp only [eval_freeze, Sum.elim_inl, Sum.elim_inr] at h
  exact h

end Scope

namespace Examples

inductive Constant where
  | arrow | int | string
  deriving DecidableEq

inductive Label where
  | domain | codomain
  deriving DecidableEq

inductive Unknown where
  | first | second | resultFirst | resultSecond | captured
  deriving DecidableEq

abbrev Parameter := Fin 1
abbrev Ty := Term Constant Unknown Label
abbrev ScopedTy := Term Constant (Unknown ⊕ Parameter) Label

/-- Raw syntax for the existing, tagged O constructor for function types. -/
abbrev arrow {C V : Type} (tag : C) (a b : Term C V Label) : Term C V Label :=
  .free (.add (.const tag)
    (.add (.hom .domain a) (.add (.hom .codomain b) .zero)))

theorem arrow_is_O {C V A : Type} [ACUIhE Label A]
    (tag : C) (ic : C → A) (iv : V → A) (a b : Term C V Label) :
    (arrow tag a b).eval ic iv =
      O ic (fun i => if i = 1 then Label.domain else Label.codomain)
        tag [a.eval ic iv, b.eval ic iv] := rfl

abbrev parameter : ScopedTy := .var (.inr 0)

/-- forall a. a -> a -/
def identity : ScopedTy := arrow .arrow parameter parameter

theorem identity_at (t : Ty) : instantiate identity (fun _ => t) =
    arrow .arrow t t := rfl

-- Checking fun x -> x: x has parameter type a; infer the result type R.
def identityCheck : Solver.Problem Constant (Unknown ⊕ Parameter) Label :=
  [⟨identity, arrow .arrow parameter (.var (.inl .resultFirst))⟩]

theorem identity_check_unifier : (freezeProblem identityCheck).IsUnifier
    (fun _ => .const (.inr (0 : Parameter)) :
      Unknown → Term (Constant ⊕ Parameter) Unknown Label) := by
  intro q hq
  simp only [freezeProblem, identityCheck, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hq
  subst q
  exact Term.Equal.refl _

theorem identity_check_succeeds :
    ∃ solution, Solver.solve (freezeProblem identityCheck) = some solution :=
  Solver.solve_complete_of_unifier _ _ identity_check_unifier

-- The executable solver actually returns R = the rigid parameter constant.
#guard match Solver.solve (freezeProblem identityCheck) with
  | none => false
  | some solution => decide (solution .resultFirst = Graph.constant (.inr (0 : Parameter)))

-- Claiming fun x -> 1 : forall a. a -> a requires Int = a.
def badIdentity : Solver.Problem Constant (Unknown ⊕ Parameter) Label :=
  [⟨.const .int, parameter⟩]

-- Leaving a solvable would accept this by choosing a = Int.
#guard Solver.isUnifiable badIdentity
#guard !(Solver.isUnifiable (freezeProblem badIdentity))

theorem bad_identity_rejected : ¬ (freezeProblem badIdentity).Unifiable := by
  rintro ⟨σ, hσ⟩
  have h : (.const (.inl .int) : Term (Constant ⊕ Parameter) Unknown Label).Equal
      (.const (.inr (0 : Parameter))) :=
    hσ ⟨.const (.inl .int), .const (.inr (0 : Parameter))⟩
    (by simp [freezeProblem, badIdentity, freeze])
  have layers := congrArg Graph.layer
    (h (Graph.constant : Constant ⊕ Parameter → Graph (Constant ⊕ Parameter) Unknown Label)
      Graph.ofVariable)
  simp [Term.eval, Graph.layer_constant] at layers

-- let id = fun x -> x in (id 1, id "one")
-- Each occurrence instantiates the SAME scoped type with a distinct unknown.
def identityUses : Solver.Problem Constant Unknown Label :=
  [⟨instantiate identity (fun _ => .var .first),
      arrow .arrow (.const .int) (.var .resultFirst)⟩,
   ⟨instantiate identity (fun _ => .var .second),
      arrow .arrow (.const .string) (.var .resultSecond)⟩]

def expectedUses : Unknown → Ty
  | .first | .resultFirst => .const .int
  | .second | .resultSecond => .const .string
  | .captured => .zero

theorem identity_uses_unifier : identityUses.IsUnifier expectedUses := by
  intro q hq
  simp only [identityUses, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> exact Term.Equal.refl _

theorem identity_uses_succeed : ∃ solution, Solver.solve identityUses = some solution :=
  Solver.solve_complete_of_unifier _ _ identity_uses_unifier

#guard match Solver.solve identityUses with
  | none => false
  | some solution => [Unknown.first, .second, .resultFirst, .resultSecond].all fun v =>
      decide (solution v = (expectedUses v).eval Graph.constant (fun _ => 0))

-- A captured y : b in fun x -> y gives forall a. a -> b.
-- Only a belongs to this scope. Both uses retain the very same b.
def returnsCaptured : ScopedTy := arrow .arrow parameter (.var (.inl .captured))

theorem captured_stays_shared (t : Ty) :
    instantiate returnsCaptured (fun _ => t) = arrow .arrow t (.var .captured) := rfl

-- Requiring the two results to be Int and String would constrain that same b twice.
def conflictingCapture : Solver.Problem Constant Unknown Label :=
  [⟨.var .captured, .const .int⟩, ⟨.var .captured, .const .string⟩]

theorem captured_conflict_rejected : ¬ conflictingCapture.Unifiable := by
  rintro ⟨σ, hσ⟩
  have hi : (σ .captured).Equal (.const .int) :=
    hσ ⟨.var .captured, .const .int⟩ (by simp [conflictingCapture])
  have hs : (σ .captured).Equal (.const .string) :=
    hσ ⟨.var .captured, .const .string⟩ (by simp [conflictingCapture])
  have h : (.const .int : Ty).Equal (.const .string) :=
    Term.Equal.trans (Term.Equal.symm hi) hs
  have layers := congrArg Graph.layer
    (h (Graph.constant : Constant → Graph Constant Unknown Label) Graph.ofVariable)
  simp [Term.eval, Graph.layer_constant] at layers

#guard !(Solver.isUnifiable conflictingCapture)

end Examples

-- Proof audit: no admitted facts or unchecked computation in these theorems.
#print axioms frozen_equal_instantiates
#print axioms frozen_solve_sound
#print axioms Examples.identity_check_succeeds
#print axioms Examples.bad_identity_rejected
#print axioms Examples.identity_uses_succeed
#print axioms Examples.captured_conflict_rejected

end QuantifierPrototype
