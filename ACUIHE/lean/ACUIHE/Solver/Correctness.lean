import ACUIHE.Completeness
import ACUIHE.NormalForm.Core

namespace ACUIHE.Solver

universe u v w

private instance {Const : Type u} {Var : Type v} {Hom : Type w} :
    Std.Commutative
      (fun left right : TermModel Const Var Hom => left + right) :=
  ⟨by
    intro left right
    refine Quotient.inductionOn₂ left right ?_
    intro left right
    exact Quotient.sound (Derives.add_comm left right)⟩

private instance {Const : Type u} {Var : Type v} {Hom : Type w} :
    Std.Associative
      (fun left right : TermModel Const Var Hom => left + right) :=
  ⟨by
    intro left middle right
    refine Quotient.inductionOn₃ left middle right ?_
    intro left middle right
    exact Quotient.sound (Derives.add_assoc left middle right)⟩

private instance {Const : Type u} {Var : Type v} {Hom : Type w} :
    Std.IdempotentOp
      (fun left right : TermModel Const Var Hom => left + right) :=
  ⟨by
    intro value
    refine Quotient.inductionOn value ?_
    intro value
    exact Quotient.sound (Derives.add_idem value)⟩

private def modelPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (path : List Hom) (body : TermModel Const Var Hom) :
    TermModel Const Var Hom :=
  path.foldr (fun name inner => TermModel.hom name inner) body

private def modelSum
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    TermModel Const Var Hom :=
  NormalForm.fold
    0
    (fun left right => left + right)
    (fun path name => modelPath path (TermModel.ofTerm (.const name)))
    (fun path name => modelPath path (TermModel.ofTerm (.var name)))
    (fun path body => modelPath path (TermModel.free body))
    normalForm

private theorem model_zero_add
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (value : TermModel Const Var Hom) : 0 + value = value := by
  refine Quotient.inductionOn value ?_
  intro value
  exact Quotient.sound
    ((Derives.add_comm (.zero : Term Const Var Hom) value).trans
      (Derives.add_zero value))

private theorem model_add_zero
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (value : TermModel Const Var Hom) : value + 0 = value := by
  refine Quotient.inductionOn value ?_
  intro value
  exact Quotient.sound (Derives.add_zero value)

@[simp]
private theorem ofTerm_zero
    {Const : Type u} {Var : Type v} {Hom : Type w} :
    TermModel.ofTerm (.zero : Term Const Var Hom) = 0 :=
  rfl

@[simp]
private theorem ofTerm_add
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (left right : Term Const Var Hom) :
    TermModel.ofTerm (.add left right) =
      TermModel.ofTerm left + TermModel.ofTerm right :=
  rfl

private theorem ofTerm_reifyPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (path : List Hom) (body : Term Const Var Hom) :
    TermModel.ofTerm (reifyPath path body) =
      modelPath path (TermModel.ofTerm body) := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      simp only [reifyPath, modelPath, List.foldr_cons]
      change TermModel.hom name
          (TermModel.ofTerm (reifyPath path body)) =
        TermModel.hom name (modelPath path (TermModel.ofTerm body))
      rw [inductionHypothesis]

private theorem ofTerm_reify
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : NormalForm Const Var Hom) :
    TermModel.ofTerm (reify normalForm) = modelSum normalForm := by
  unfold reify modelSum
  apply NormalForm.fold_hom
  · rfl
  · intro left right
    rfl
  · intro path name
    exact ofTerm_reifyPath path (.const name)
  · intro path name
    exact ofTerm_reifyPath path (.var name)
  · intro path body
    rw [ofTerm_reifyPath]
    rfl

@[simp]
private theorem modelSum_empty
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    modelSum (∅ : NormalForm Const Var Hom) = 0 := by
  unfold modelSum
  exact NormalForm.fold_empty _ _ _ _ _

@[simp]
private theorem modelSum_constantForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Const) :
    modelSum (constantForm (Var := Var) (Hom := Hom) name) =
      TermModel.ofTerm (.const name) := by
  unfold modelSum constantForm
  rw [NormalForm.fold_singleton, model_add_zero]
  rfl

@[simp]
private theorem modelSum_variableForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Var) :
    modelSum (variableForm (Const := Const) (Hom := Hom) name) =
      TermModel.ofTerm (.var name) := by
  unfold modelSum variableForm
  rw [NormalForm.fold_singleton, model_add_zero]
  rfl

private theorem modelSum_union
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : NormalForm Const Var Hom) :
    modelSum (left ∪ right) = modelSum left + modelSum right := by
  unfold modelSum
  apply NormalForm.fold_union
  exact model_add_zero

private theorem model_hom_zero
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (name : Hom) :
    TermModel.hom (Const := Const) (Var := Var) name 0 = 0 :=
  Quotient.sound (Derives.hom_zero name)

private theorem model_hom_add
    {Const : Type u} {Var : Type v} {Hom : Type w}
    (name : Hom) (left right : TermModel Const Var Hom) :
    TermModel.hom name (left + right) =
      TermModel.hom name left + TermModel.hom name right := by
  refine Quotient.inductionOn₂ left right ?_
  intro left right
  exact Quotient.sound (Derives.hom_add name left right)

private theorem modelSum_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (normalForm : NormalForm Const Var Hom) :
    modelSum (prefixHom name normalForm) =
      TermModel.hom name (modelSum normalForm) := by
  unfold modelSum
  apply NormalForm.fold_prefixHom
  · exact model_add_zero
  · exact model_hom_zero name
  · exact model_hom_add name
  · intro path constantName
    rfl
  · intro path variableName
    rfl
  · intro path body
    rfl

private theorem model_free_zero
    {Const : Type u} {Var : Type v} {Hom : Type w} :
    TermModel.free (Const := Const) (Var := Var) (Hom := Hom) 0 = 0 :=
  Quotient.sound Derives.free_zero

private theorem modelSum_wrapE
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (body : NormalForm Const Var Hom) :
    modelSum (wrapE body) = TermModel.free (modelSum body) := by
  by_cases bodyZero : body = ∅
  · subst body
    rw [wrapE_empty, modelSum_empty]
    exact model_free_zero.symm
  · rw [wrapE_of_ne_empty bodyZero]
    unfold modelSum
    rw [NormalForm.fold_singleton, model_add_zero]
    rfl

private theorem ofTerm_eq_modelSum_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) :
    TermModel.ofTerm term = modelSum (normalize term) := by
  induction term with
  | zero => exact modelSum_empty.symm
  | const name => exact modelSum_constantForm name |>.symm
  | var name => exact modelSum_variableForm name |>.symm
  | add left right leftHypothesis rightHypothesis =>
      change TermModel.ofTerm left + TermModel.ofTerm right =
        modelSum (normalize left ∪ normalize right)
      rw [leftHypothesis, rightHypothesis, modelSum_union]
  | hom name body inductionHypothesis =>
      change TermModel.hom name (TermModel.ofTerm body) =
        modelSum (prefixHom name (normalize body))
      rw [modelSum_prefixHom name (normalize body), inductionHypothesis]
  | free body inductionHypothesis =>
      change TermModel.free (TermModel.ofTerm body) =
        modelSum (wrapE (normalize body))
      rw [modelSum_wrapE, inductionHypothesis]

/-- Every term derives the reification of its computed normal form. -/
theorem derives_reify_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (term : Term Const Var Hom) :
    Derives term (reify (normalize term)) := by
  apply Quotient.exact (s := derivationSetoid Const Var Hom)
  change TermModel.ofTerm term = TermModel.ofTerm (reify (normalize term))
  rw [ofTerm_eq_modelSum_normalize, ofTerm_reify]

/-- Equal computed normal forms give a derivation between the original terms. -/
theorem derives_of_normalize_eq
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : Term Const Var Hom}
    (equality : normalize left = normalize right) :
    Derives left right := by
  have leftDerivation : Derives left (reify (normalize left)) :=
    derives_reify_normalize left
  have rightDerivation : Derives right (reify (normalize right)) :=
    derives_reify_normalize right
  rw [equality] at leftDerivation
  exact leftDerivation.trans rightDerivation.symm

theorem derives_iff_normalize_eq
    {left right : Term Const Var Hom}
    [Encodable Const] [Encodable Var] [Encodable Hom]:
    Derives left right ↔ normalize left = normalize right :=
  ⟨normalize_eq_of_derives, derives_of_normalize_eq⟩

end ACUIHE.Solver
