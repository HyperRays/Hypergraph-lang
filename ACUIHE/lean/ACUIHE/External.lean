import ACUIHE.Solver.Substitution
import ACUIHE.Solver.Search

/-!
# External replacement API

This module keeps language-defined replacement rules outside the ACUIhE
algebra and its decision procedure. A caller first rewrites an inequality
with an ordered list of ground block replacements and then passes the result
to the unchanged solver.

Rules are deliberately operational. One rule replaces every occurrence of
its canonical `pattern` by its canonical `replacement`; a rule list is applied
once, from left to right. No termination or confluence claim is needed because
this module does not iterate rules to a fixed point.

The helper `BlockReplacement.ofSubsumption lower upper` encodes the external
fact `lower <= upper` as the absorption-preserving replacement
`upper -> upper + lower`. The sum exists only in the solver representation;
it need not be constructible in the source language.
-/

namespace ACUIHE.External

open ACUIHE.Solver

universe u v w

/-- A canonical solver block containing no solver variables. -/
abbrev GroundNormalForm
    (Const : Type u) (Hom : Type w)
    [Encodable Const] [Encodable Hom] :=
  NormalForm Const (Fin 0) Hom

/--
An externally supplied, directed replacement between ground solver blocks.

The fields need not already be canonical: `BlockReplacement.rewrite`
canonicalizes them before matching. An empty pattern is treated as a no-op,
since it would otherwise match every canonical node.
-/
structure BlockReplacement
    (Const : Type u) (Hom : Type w)
    [Encodable Const] [Encodable Hom] where
  pattern : GroundNormalForm Const Hom
  replacement : GroundNormalForm Const Hom

namespace BlockReplacement

/-- Construct a ground block replacement directly from raw terms. -/
def ofTerms
    {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (pattern replacement : Term Const (Fin 0) Hom) :
    BlockReplacement Const Hom where
  pattern := normalize pattern
  replacement := normalize replacement

/--
Encode an external subsumption fact `lower <= upper` without identifying the
two blocks. Replacing `upper` by `upper + lower` makes `lower` lie below the
encoded upper block in the ordinary ACUI order.
-/
def ofSubsumption
    {Const : Type u} {Hom : Type w}
    [Encodable Const] [Encodable Hom]
    (lower upper : GroundNormalForm Const Hom) :
    BlockReplacement Const Hom where
  pattern := upper
  replacement := upper + lower

/-- Lift a ground block into a normal form with arbitrary solver variables. -/
def liftGround
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (block : GroundNormalForm Const Hom) :
    NormalForm Const Var Hom :=
  substituteNormalForm (fun impossible => Fin.elim0 impossible) block

/--
Apply one external rule to every matching canonical block in `target`.

Matching and abstraction use `reverseSubstituteCanonicalBlock`. The fresh
`Sum.inr ()` variable cannot collide with a caller variable. Expanding that
placeholder with `replacement`, rather than with the original pattern, turns
the existing reversible abstraction into a directed replacement.
-/
def rewrite
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rule : BlockReplacement Const Hom)
    (target : NormalForm Const Var Hom) : NormalForm Const Var Hom :=
  let pattern : NormalForm Const Var Hom := liftGround rule.pattern
  let replacement : NormalForm Const Var Hom := liftGround rule.replacement
  let canonicalTarget := canonicalize target
  if pattern = ∅ then
    canonicalTarget
  else
    let abstracted : NormalForm Const (Sum Var Unit) Hom :=
      reverseSubstituteCanonicalBlock
        Sum.inl (.inr ()) pattern canonicalTarget
    substituteNormalForm
      (fun source =>
        match source with
        | .inl name => .var name
        | .inr _ => reify replacement)
      abstracted

/-- Applying one external replacement always returns a canonical form. -/
theorem rewrite_isCanonical
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rule : BlockReplacement Const Hom)
    (target : NormalForm Const Var Hom) :
    IsCanonical (rule.rewrite target) := by
  simp only [rewrite]
  split
  · exact canonicalize_idempotent target
  · exact substituteNormalForm_isCanonical _ _

end BlockReplacement

/--
Apply an ordered list of external replacements once from left to right.

Each individual rule replaces all of its matches. A later rule therefore
sees the canonical result produced by every preceding rule.
-/
def rewriteAll
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    List (BlockReplacement Const Hom) →
      NormalForm Const Var Hom → NormalForm Const Var Hom
  | [], target => canonicalize target
  | rule :: rules, target => rewriteAll rules (rule.rewrite target)

/-- An ordered external rewrite pass always returns a canonical form. -/
theorem rewriteAll_isCanonical
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (target : NormalForm Const Var Hom) :
    IsCanonical (rewriteAll rules target) := by
  induction rules generalizing target with
  | nil => exact canonicalize_idempotent target
  | cons rule rules inductionHypothesis =>
      exact inductionHypothesis (rule.rewrite target)

/-- Rewrite both sides of an inequality for consumption by any solver backend. -/
def rewriteInequality
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom) :
    NormalForm Const Var Hom × NormalForm Const Var Hom :=
  (rewriteAll rules left, rewriteAll rules right)

/-- The solution predicate for the inequality after its external rewrite pass. -/
def IsRewrittenSolution
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom)
    (assignment : Var → GroundNormalForm Const Hom) : Prop :=
  IsSolvedInequality
    (ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules left))
    (ACUIHE.Solver.Search.applyGroundAssignment assignment
      (rewriteAll rules right))

/--
Run the unchanged, exact ACUIhE solver after applying external replacements.

The result is intentionally specified against `IsRewrittenSolution`: arbitrary
external rules are language semantics, not additional ACUIhE equations.
-/
def solveACUIhE?
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom) :
    Option (Var → GroundNormalForm Const Hom) :=
  ACUIHE.Solver.Search.solveACUIhE?
    (rewriteAll rules left) (rewriteAll rules right)

/-- Every assignment returned by the external wrapper solves the rewritten problem. -/
theorem solveACUIhE?_sound
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom)
    {assignment : Var → GroundNormalForm Const Hom}
    (found : solveACUIhE? rules left right = some assignment) :
    IsRewrittenSolution rules left right assignment := by
  unfold solveACUIhE? at found
  unfold IsRewrittenSolution
  exact ACUIHE.Solver.Search.solveACUIhE?_sound
    (rewriteAll rules left) (rewriteAll rules right) found

/-- Every solution of the externally rewritten problem is found. -/
theorem solveACUIhE?_complete
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom)
    (solution : ∃ assignment : Var → GroundNormalForm Const Hom,
      IsRewrittenSolution rules left right assignment) :
    ∃ assignment, solveACUIhE? rules left right = some assignment := by
  unfold IsRewrittenSolution at solution
  unfold solveACUIhE?
  exact ACUIHE.Solver.Search.solveACUIhE?_complete
    (rewriteAll rules left) (rewriteAll rules right) solution

/-- Wrapper failure is exactly unsatisfiability of the externally rewritten problem. -/
theorem solveACUIhE?_eq_none_iff
    {Const Var Hom : Type u}
    [FinEnum Const] [Encodable Const]
    [FinEnum Var] [Encodable Var]
    [FinEnum Hom] [Encodable Hom]
    (rules : List (BlockReplacement Const Hom))
    (left right : NormalForm Const Var Hom) :
    solveACUIhE? rules left right = none ↔
      ¬ ∃ assignment : Var → GroundNormalForm Const Hom,
        IsRewrittenSolution rules left right assignment := by
  unfold solveACUIhE? IsRewrittenSolution
  exact ACUIHE.Solver.Search.solveACUIhE?_eq_none_iff
    (rewriteAll rules left) (rewriteAll rules right)

end ACUIHE.External
