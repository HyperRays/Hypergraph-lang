import ACUIHE.Solver.Descent

/-! Variable substitution on terms and its induced action on normal forms. -/

namespace ACUIHE

universe u v w x y z

namespace Term

/--
Extend a substitution on variables to a homomorphism on terms.

The source and target variable types may differ. Constants and named
homomorphisms are left unchanged.
-/
def substitute
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    (substitution : SourceVar → Term Const TargetVar Hom) :
    Term Const SourceVar Hom → Term Const TargetVar Hom
  | .zero => .zero
  | .const name => .const name
  | .var name => substitution name
  | .add left right =>
      .add (substitute substitution left) (substitute substitution right)
  | .hom name body => .hom name (substitute substitution body)
  | .free body => .free (substitute substitution body)

@[simp]
theorem substitute_zero
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} (substitution : SourceVar → Term Const TargetVar Hom) :
    substitute substitution (.zero : Term Const SourceVar Hom) = .zero :=
  rfl

@[simp]
theorem substitute_const
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} (substitution : SourceVar → Term Const TargetVar Hom)
    (name : Const) :
    substitute substitution (.const name : Term Const SourceVar Hom) =
      .const name :=
  rfl

@[simp]
theorem substitute_var
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} (substitution : SourceVar → Term Const TargetVar Hom)
    (name : SourceVar) :
    substitute substitution (.var name : Term Const SourceVar Hom) =
      substitution name :=
  rfl

@[simp]
theorem substitute_add
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} (substitution : SourceVar → Term Const TargetVar Hom)
    (left right : Term Const SourceVar Hom) :
    substitute substitution (.add left right) =
      .add (substitute substitution left) (substitute substitution right) :=
  rfl

@[simp]
theorem substitute_hom
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} (substitution : SourceVar → Term Const TargetVar Hom)
    (name : Hom) (body : Term Const SourceVar Hom) :
    substitute substitution (.hom name body) =
      .hom name (substitute substitution body) :=
  rfl

@[simp]
theorem substitute_free
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} (substitution : SourceVar → Term Const TargetVar Hom)
    (body : Term Const SourceVar Hom) :
    substitute substitution (.free body) =
      .free (substitute substitution body) :=
  rfl

/-- Replacing every variable by itself leaves a term unchanged. -/
@[simp]
theorem substitute_variables
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (term : Term Const Var Hom) :
    substitute (fun name => .var name) term = term := by
  induction term <;> simp_all

/-- Successive substitutions compose by substituting into the first range. -/
theorem substitute_substitute
    {Const : Type u} {SourceVar : Type v} {MiddleVar : Type w}
    {TargetVar : Type x} {Hom : Type y}
    (first : SourceVar → Term Const MiddleVar Hom)
    (second : MiddleVar → Term Const TargetVar Hom)
    (term : Term Const SourceVar Hom) :
    substitute second (substitute first term) =
      substitute (fun name => substitute second (first name)) term := by
  induction term <;> simp_all

/-- Evaluation after substitution is evaluation under the substituted valuation. -/
theorem eval_substitute
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} {Alpha : Type z} [ACUIhE Hom Alpha]
    (substitution : SourceVar → Term Const TargetVar Hom)
    (interpretConst : Const → Alpha) (interpretVar : TargetVar → Alpha)
    (term : Term Const SourceVar Hom) :
    (substitute substitution term).eval interpretConst interpretVar =
      term.eval interpretConst
        (fun name => (substitution name).eval interpretConst interpretVar) := by
  induction term <;> simp_all [Term.eval]

end Term

/-- Applying a variable substitution to both sides preserves derivability. -/
theorem Derives.substitute
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x} (substitution : SourceVar → Term Const TargetVar Hom)
    {left right : Term Const SourceVar Hom} (derivation : Derives left right) :
    Derives (Term.substitute substitution left)
      (Term.substitute substitution right) := by
  induction derivation with
  | refl => exact Derives.refl _
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ leftHypothesis rightHypothesis =>
      exact leftHypothesis.trans rightHypothesis
  | add_congr _ _ leftHypothesis rightHypothesis =>
      exact Derives.add_congr leftHypothesis rightHypothesis
  | hom_congr name _ inductionHypothesis =>
      exact Derives.hom_congr name inductionHypothesis
  | free_congr _ inductionHypothesis =>
      exact Derives.free_congr inductionHypothesis
  | free_inj _ inductionHypothesis =>
      exact Derives.free_inj inductionHypothesis
  | add_assoc => exact Derives.add_assoc _ _ _
  | add_comm => exact Derives.add_comm _ _
  | add_zero => exact Derives.add_zero _
  | add_idem => exact Derives.add_idem _
  | hom_add => exact Derives.hom_add _ _ _
  | hom_zero => exact Derives.hom_zero _
  | free_zero => exact Derives.free_zero

namespace Solver

open NormalForm.Internal

/-- Every variable substitution respects the ACUIhE theory. -/
theorem substitute_respectsDerives
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    (substitution : SourceVar → Term Const TargetVar Hom) :
    RespectsDerives (Term.substitute substitution) := by
  intro left right derivation
  exact derivation.substitute substitution

/-!
## Recursive canonical-block matching

A canonical normal form is recursive only through `E` bodies.  Homomorphisms
are represented by paths on summands, so descending through a homomorphism
does not create another normal-form node at which a block can match.

The private term traversal below is applied only to a reified normal form.  It
uses the term tree to reach each `E` body without exposing the private normal-
form representation.  Every such body is normalized before the ACUI
containment test is performed.
-/

/-- Search the reification of a normal form for a matching canonical block in
one of its recursively nested `E` bodies. -/
private def termContainsCanonicalBlock
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (block : NormalForm Const Var Hom) :
    Term Const Var Hom → Bool
  | .zero => false
  | .const _ => false
  | .var _ => false
  | .add left right =>
      termContainsCanonicalBlock block left ||
        termContainsCanonicalBlock block right
  | .hom _ body => termContainsCanonicalBlock block body
  | .free body =>
      if block + normalize body = normalize body then
        true
      else
        termContainsCanonicalBlock block body

/--
Whether `block` matches a block of summands at the root of `target` or at any
recursively nested canonical `E` body.

This is structural matching of canonical normal forms.  In particular,
homomorphism paths remain part of their summands: a commonly prefixed image of
`block` is not treated as a separate nested match.
-/
def matchesCanonicalBlock
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (block target : NormalForm Const Var Hom) : Bool :=
  if block + target = target then
    true
  else
    termContainsCanonicalBlock block (reify target)

/-- The propositional form of executable canonical-block matching. -/
def CanonicalBlockMatches
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (block target : NormalForm Const Var Hom) : Prop :=
  matchesCanonicalBlock block target = true

/-- A block contained at the current canonical node is a match. -/
theorem canonicalBlockMatches_of_below
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {block target : NormalForm Const Var Hom}
    (contained : Below (Hom := Hom) block target) :
    CanonicalBlockMatches block target := by
  change block + target = target at contained
  unfold CanonicalBlockMatches matchesCanonicalBlock
  rw [if_pos contained]

/-- Every canonical normal form matches itself at its root. -/
@[simp]
theorem canonicalBlockMatches_self
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    CanonicalBlockMatches normalForm normalForm := by
  apply canonicalBlockMatches_of_below
  exact ACUIhE.add_idem (Hom := Hom) normalForm

/-- A match anywhere in a canonical `E` body is found by recursive matching. -/
theorem canonicalBlockMatches_wrapE
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {block body : NormalForm Const Var Hom}
    (bodyCanonical : IsCanonical body)
    (bodyMatch : CanonicalBlockMatches block body) :
    CanonicalBlockMatches block (wrapE body) := by
  by_cases bodyZero : body = ∅
  · subst body
    rw [wrapE_empty]
    exact bodyMatch
  · rw [wrapE_of_ne_empty bodyZero]
    unfold CanonicalBlockMatches matchesCanonicalBlock at bodyMatch ⊢
    split
    · rfl
    · unfold reify
      rw [NormalForm.fold_singleton]
      change
        (termContainsCanonicalBlock block
          (.add (.free (reify body)) .zero)) = true
      simp only [termContainsCanonicalBlock, Bool.or_false]
      change
        (if block + canonicalize body = canonicalize body then true else _) = true
      rw [bodyCanonical]
      exact bodyMatch

/-- A block contained at a canonical `E` body is found beneath the wrapper. -/
theorem canonicalBlockMatches_wrapE_of_below
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {block body : NormalForm Const Var Hom}
    (bodyCanonical : IsCanonical body)
    (contained : Below (Hom := Hom) block body) :
    CanonicalBlockMatches block (wrapE body) :=
  canonicalBlockMatches_wrapE bodyCanonical
    (canonicalBlockMatches_of_below contained)

/-!
## Reverse substitution of canonical blocks

The recursive implementation works directly on the public normal-form
representation.  At each canonical node it removes the summands of `block`
when they are contained there, inserts the chosen placeholder variable, and
continues recursively through every unmatched `E` body.  Homomorphism paths
remain attached to their summands and are not treated as recursive nodes.

Source and target variable types are independent.  Unmatched target variables
are transported to the source type by the caller-supplied `rename` function.
-/

/-- The representation-level implementation of recursive block replacement. -/
private def reverseSubstituteCanonicalBlockRaw
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (rename : TargetVar → SourceVar) (placeholder : SourceVar)
    (block : RawNormalForm Const TargetVar Hom)
    (target : NormalForm Const TargetVar Hom) :
    NormalForm Const SourceVar Hom :=
  let matchesHere := block ∪ target.raw = target.raw
  let rewritten :=
    (target.raw.codes.attach.sort
      (fun left right => left.1 ≤ right.1)).foldr
      (fun code rest =>
        if matchesHere ∧ code.1 ∈ block.codes then
          rest
        else
          match decoded :
              Encodable.decode₂ (RawNormalSummand Const TargetVar Hom) code.1 with
          | none => rest
          | some (path, .constant name) =>
              ({(path, .constant name)} : NormalForm Const SourceVar Hom) ∪ rest
          | some (path, .variable name) =>
              ({(path, .variable (rename name))} :
                  NormalForm Const SourceVar Hom) ∪ rest
          | some (path, .eOperator body) =>
              have bodyMembership :
                  (path, RawNormalAtom.eOperator body) ∈
                    RecursiveFinset.toFinset target.raw := by
                unfold RecursiveFinset.toFinset
                simp only [Finset.mem_filterMap]
                exact ⟨code.1, code.property, decoded⟩
              let bodyNormalForm : NormalForm Const TargetVar Hom :=
                ⟨body, by
                  have atomValid := target.valid.nested _ bodyMembership
                  cases atomValid with
                  | eOperator bodyValid => exact bodyValid⟩
              let rewrittenBody :=
                reverseSubstituteCanonicalBlockRaw rename placeholder block
                  bodyNormalForm
              ({(path, .eOperator rewrittenBody)} :
                  NormalForm Const SourceVar Hom) ∪ rest)
      (∅ : NormalForm Const SourceVar Hom)
  if matchesHere then
    variableForm placeholder ∪ rewritten
  else
    rewritten
termination_by rawNormalFormMeasure target.raw
decreasing_by
  exact rawNormalFormMeasure_lt_of_decode_eOperator code.property decoded

/--
Replace every recursively matched occurrence of `block` in `target` by
`placeholder`.

Both arguments are intended to be canonical normal forms.  Matching occurs at
the root and at genuine nested `E` bodies, exactly as in
`matchesCanonicalBlock`.  Variables in unmatched summands are mapped from
`TargetVar` to `SourceVar` using `rename`.
-/
def reverseSubstituteCanonicalBlock
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (rename : TargetVar → SourceVar) (placeholder : SourceVar)
    (block target : NormalForm Const TargetVar Hom) :
    NormalForm Const SourceVar Hom :=
  reverseSubstituteCanonicalBlockRaw rename placeholder block.raw target

/-- Replacing a complete block by a placeholder leaves only the placeholder. -/
@[simp]
theorem reverseSubstituteCanonicalBlock_self
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (rename : TargetVar → SourceVar) (placeholder : SourceVar)
    (block : NormalForm Const TargetVar Hom) :
    reverseSubstituteCanonicalBlock rename placeholder block block =
      variableForm placeholder := by
  unfold reverseSubstituteCanonicalBlock
  rw [reverseSubstituteCanonicalBlockRaw]
  simp only [rawUnion_self, ↓reduceIte]
  generalize
    block.raw.codes.attach.sort (fun left right => left.1 ≤ right.1) = codes
  induction codes with
  | nil => exact ACUIhE.add_zero (Hom := Hom) (variableForm placeholder)
  | cons code codes inductionHypothesis =>
      simp only [List.foldr_cons]
      rw [if_pos ⟨True.intro, code.property⟩]
      exact inductionHypothesis

/--
The fixed substitution accompanying a reverse block substitution: the
placeholder expands to `block`, and every other source variable uses the
caller-supplied target-term substitution `fallback`.
-/
def fixedBlockSubstitution
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    [DecidableEq SourceVar]
    (placeholder : SourceVar) (block : NormalForm Const TargetVar Hom)
    (fallback : SourceVar → Term Const TargetVar Hom) :
    SourceVar → Term Const TargetVar Hom :=
  fun name => if name = placeholder then reify block else fallback name

@[simp]
theorem fixedBlockSubstitution_placeholder
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    [DecidableEq SourceVar]
    (placeholder : SourceVar) (block : NormalForm Const TargetVar Hom)
    (fallback : SourceVar → Term Const TargetVar Hom) :
    fixedBlockSubstitution placeholder block fallback placeholder = reify block := by
  simp [fixedBlockSubstitution]

@[simp]
theorem fixedBlockSubstitution_of_ne
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    [DecidableEq SourceVar]
    (placeholder : SourceVar) (block : NormalForm Const TargetVar Hom)
    (fallback : SourceVar → Term Const TargetVar Hom)
    {name : SourceVar} (different : name ≠ placeholder) :
    fixedBlockSubstitution placeholder block fallback name = fallback name := by
  simp [fixedBlockSubstitution, different]

/--
The action of a variable substitution on normal forms, obtained by descending
its extension to terms.
-/
def substituteNormalForm
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (substitution : SourceVar → Term Const TargetVar Hom) :
    NormalForm Const SourceVar Hom → NormalForm Const TargetVar Hom :=
  induce (Term.substitute substitution)

/-- Substitution on normal forms commutes with normalization. -/
theorem substituteNormalForm_normalize
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (substitution : SourceVar → Term Const TargetVar Hom)
    (term : Term Const SourceVar Hom) :
    substituteNormalForm substitution (normalize term) =
      normalize (Term.substitute substitution term) :=
  induce_normalize (Term.substitute substitution)
    (substitute_respectsDerives substitution) term

/-- Every result of normal-form substitution is canonical. -/
theorem substituteNormalForm_isCanonical
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (substitution : SourceVar → Term Const TargetVar Hom)
    (normalForm : NormalForm Const SourceVar Hom) :
    IsCanonical (substituteNormalForm substitution normalForm) :=
  induce_isCanonical (Term.substitute substitution) normalForm

/-- Normal-form substitution preserves canonical forms. -/
theorem substituteNormalForm_preservesCanonical
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    (substitution : SourceVar → Term Const TargetVar Hom) :
    PreservesCanonical (substituteNormalForm substitution) :=
  induce_preservesCanonical (Term.substitute substitution)

/-- The identity substitution canonicalizes an arbitrary normal form. -/
@[simp]
theorem substituteNormalForm_variables
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    substituteNormalForm (fun name => .var name) normalForm =
      canonicalize normalForm := by
  unfold substituteNormalForm induce canonicalize
  rw [Term.substitute_variables]

/-- Composition of substitutions is respected after descent to normal forms. -/
theorem substituteNormalForm_substituteNormalForm
    {Const : Type u} {SourceVar : Type v} {MiddleVar : Type w}
    {TargetVar : Type x} {Hom : Type y}
    [Encodable Const] [Encodable SourceVar] [Encodable MiddleVar]
    [Encodable TargetVar] [Encodable Hom]
    (first : SourceVar → Term Const MiddleVar Hom)
    (second : MiddleVar → Term Const TargetVar Hom)
    (normalForm : NormalForm Const SourceVar Hom) :
    substituteNormalForm second (substituteNormalForm first normalForm) =
      substituteNormalForm
        (fun name => Term.substitute second (first name)) normalForm := by
  change
    induce (Term.substitute second)
        (normalize (Term.substitute first (reify normalForm))) =
      normalize
        (Term.substitute (fun name => Term.substitute second (first name))
          (reify normalForm))
  rw [induce_normalize (Term.substitute second)
    (substitute_respectsDerives second)]
  rw [Term.substitute_substitute]

/-- Expanding a completely abstracted block recovers its canonicalization. -/
theorem substituteNormalForm_reverseSubstituteCanonicalBlock_self
    {Const : Type u} {SourceVar : Type v} {TargetVar : Type w}
    {Hom : Type x}
    [Encodable Const] [Encodable SourceVar] [Encodable TargetVar] [Encodable Hom]
    [DecidableEq SourceVar]
    (rename : TargetVar → SourceVar) (placeholder : SourceVar)
    (block : NormalForm Const TargetVar Hom)
    (fallback : SourceVar → Term Const TargetVar Hom) :
    substituteNormalForm (fixedBlockSubstitution placeholder block fallback)
        (reverseSubstituteCanonicalBlock rename placeholder block block) =
      canonicalize block := by
  rw [reverseSubstituteCanonicalBlock_self]
  change
    substituteNormalForm (fixedBlockSubstitution placeholder block fallback)
        (normalize (.var placeholder : Term Const SourceVar Hom)) =
      canonicalize block
  rw [substituteNormalForm_normalize]
  simp [fixedBlockSubstitution, canonicalize]

end Solver

end ACUIHE
