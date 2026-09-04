import ACUIHE.External.Batch

/-!
# Hypergraph language types

This is the language-specific layer over ACUIhE.  The proved solver remains
unchanged: this module only fixes the constants and homomorphism names used by
the hypergraph language and records the external undirected-edge subsumption.
-/

namespace HypergraphML.External

open ACUIHE
open ACUIHE.Solver
open ACUIHE.External

/--
The bridge interns source names into finite numeric tables.  Natural numbers
are used here so the language laws are independent of any one program's table
size; the FFI layer validates and narrows them to `Fin n` before solving.
-/
abbrev TypeConstant := Nat
abbrev TypeHom := Nat

namespace BuiltinConstant
def int : TypeConstant := 0
def decimal : TypeConstant := 1
def string : TypeConstant := 2
def set : TypeConstant := 3
def option : TypeConstant := 4
def edge : TypeConstant := 5
def undirectedEdge : TypeConstant := 6
def opaqueTag : TypeConstant := 7
def opaqueEq : TypeConstant := 8
end BuiltinConstant

namespace BuiltinHom
def setElement : TypeHom := 0
def optionSome : TypeHom := 1
def optionNone : TypeHom := 2
def edgeTail : TypeHom := 3
def edgeHead : TypeHom := 4
def edgePayload : TypeHom := 5
def opaqueHide : TypeHom := 6
def opaqueMarker : TypeHom := 7
end BuiltinHom

abbrev TypeTerm (Variable : Type) := Term TypeConstant Variable TypeHom
abbrev GroundTypeTerm := TypeTerm (Fin 0)
abbrev CanonicalType (Variable : Type) [Encodable Variable] :=
  NormalForm TypeConstant Variable TypeHom
abbrev GroundCanonicalType := CanonicalType (Fin 0)

local instance rawSummandDecidableEq {Variable : Type} [Encodable Variable] :
    DecidableEq
      (ACUIHE.Solver.NormalForm.Internal.RawNormalSummand
        TypeConstant Variable TypeHom) :=
  Encodable.decidableEqOfEncodable _

private def sumTerms {Variable : Type} : List (TypeTerm Variable) → TypeTerm Variable
  | [] => .zero
  | term :: terms => .add term (sumTerms terms)

/-- A primitive scalar type.  `EmptySet` is represented by `empty`, not here. -/
def primitive {Variable : Type} (identity : TypeConstant) : TypeTerm Variable :=
  .const identity

/-- The bottom type and the element type of the empty set literal. -/
def empty {Variable : Type} : TypeTerm Variable := .zero

/-- `Set<T> = S_setElement(C_Set, T)`. -/
def set {Variable : Type} (element : TypeTerm Variable) : TypeTerm Variable :=
  .add (.const BuiltinConstant.set) (.hom BuiltinHom.setElement element)

/--
All structs and enums share this encoding.  Each member occurrence supplies
its own homomorphism tag; enum constructor arity remains runtime information.
-/
def named {Variable : Type} (name : TypeConstant)
    (members : List (TypeHom × TypeTerm Variable)) : TypeTerm Variable :=
  .free <| .add (.const name) <|
    sumTerms (members.map fun member => .hom member.1 member.2)

/-- The predeclared option signature.  The nullary `None` contributes zero. -/
def option {Variable : Type} (payload : TypeTerm Variable) : TypeTerm Variable :=
  named BuiltinConstant.option
    [(BuiltinHom.optionSome, payload), (BuiltinHom.optionNone, .zero)]

/-- Directed edges are ordinary named structs with special source syntax. -/
def edge {Variable : Type} (tail head payload : TypeTerm Variable) :
    TypeTerm Variable :=
  named BuiltinConstant.edge
    [(BuiltinHom.edgeTail, set tail), (BuiltinHom.edgeHead, set head),
      (BuiltinHom.edgePayload, option payload)]

/-- Undirected edges have the same fields and a distinct declaration name. -/
def undirectedEdge {Variable : Type} (tail head payload : TypeTerm Variable) :
    TypeTerm Variable :=
  named BuiltinConstant.undirectedEdge
    [(BuiltinHom.edgeTail, set tail), (BuiltinHom.edgeHead, set head),
      (BuiltinHom.edgePayload, option payload)]

/-- Graph is the transparent source-language alias from the specification. -/
def graph {Variable : Type} (tail head payload : TypeTerm Variable) :
    TypeTerm Variable :=
  set (.add (edge tail head payload) (undirectedEdge tail head payload))

/-- The internal opaque wrapper retains its hidden type and nominal marker. -/
def opaqueType {Variable : Type} (hidden marker : TypeTerm Variable) :
    TypeTerm Variable :=
  named BuiltinConstant.opaqueTag
    [(BuiltinHom.opaqueHide, hidden), (BuiltinHom.opaqueMarker, marker)]

/-- Equality deliberately projects only the marker of an opaque value. -/
def opaqueEqualityProjection {Variable : Type}
    (_hidden marker : TypeTerm Variable) : TypeTerm Variable :=
  named BuiltinConstant.opaqueEq [(BuiltinHom.opaqueMarker, marker)]

@[simp] theorem opaqueEqualityProjection_ignores_hidden {Variable : Type}
    (leftHidden rightHidden marker : TypeTerm Variable) :
    opaqueEqualityProjection leftHidden marker =
      opaqueEqualityProjection rightHidden marker := rfl

/-- Canonical type union is the join induced by ACUI addition. -/
def join {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) : CanonicalType Variable :=
  left + right

@[simp] theorem canonical_add_raw {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) :
    (left + right).raw = left.raw ∪ right.raw := rfl

theorem below_join_left {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) :
    Below (Hom := TypeHom) left (join left right) := by
  unfold Below join
  calc
    left + (left + right) = (left + left) + right :=
      (ACUIhE.add_assoc (Hom := TypeHom) left left right).symm
    _ = left + right := congrArg (fun value => value + right)
      (ACUIhE.add_idem (Hom := TypeHom) left)

theorem below_join_right {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) :
    Below (Hom := TypeHom) right (join left right) := by
  have commutative : join left right = join right left := by
    unfold join
    exact ACUIhE.add_comm (Hom := TypeHom) left right
  rw [commutative]
  exact below_join_left right left

theorem join_least {Variable : Type} [Encodable Variable]
    (left right upper : CanonicalType Variable)
    (leftBelow : Below (Hom := TypeHom) left upper)
    (rightBelow : Below (Hom := TypeHom) right upper) :
    Below (Hom := TypeHom) (join left right) upper := by
  unfold Below join at *
  calc
    (left + right) + upper = left + (right + upper) :=
      ACUIhE.add_assoc (Hom := TypeHom) left right upper
    _ = left + upper := congrArg (fun value => left + value) rightBelow
    _ = upper := leftBelow

/-- Canonical intersection of normal-form summands. -/
def meet {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) : CanonicalType Variable := by
  let _ := Encodable.decidableEqOfEncodable
    (ACUIHE.Solver.NormalForm.Internal.RawNormalSummand
      TypeConstant Variable TypeHom)
  exact
    { raw := ACUIHE.Solver.RecursiveFinset.ofFinset
        (ACUIHE.Solver.RecursiveFinset.toFinset left.raw ∩
          ACUIHE.Solver.RecursiveFinset.toFinset right.raw)
      valid := by
        apply ACUIHE.Solver.NormalForm.Internal.ValidNode.normalForm
        · simp [ACUIHE.Solver.RecursiveFinset.Valid]
        · intro summand membership
          have inIntersection :
              summand ∈ ACUIHE.Solver.RecursiveFinset.toFinset left.raw ∩
                ACUIHE.Solver.RecursiveFinset.toFinset right.raw := by
            simpa using membership
          exact left.valid.nested summand (Finset.mem_inter.mp inIntersection).1 }

@[simp] theorem meet_raw {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) :
    (meet left right).raw = ACUIHE.Solver.RecursiveFinset.ofFinset
      (ACUIHE.Solver.RecursiveFinset.toFinset left.raw ∩
        ACUIHE.Solver.RecursiveFinset.toFinset right.raw) := by
  rfl

theorem meet_below_left {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) :
    Below (Hom := TypeHom) (meet left right) left := by
  let _ := Encodable.decidableEqOfEncodable
    (ACUIHE.Solver.NormalForm.Internal.RawNormalSummand
      TypeConstant Variable TypeHom)
  unfold Below
  apply NormalForm.ext_raw
  rw [canonical_add_raw, meet_raw]
  let leftSet := ACUIHE.Solver.RecursiveFinset.toFinset left.raw
  let rightSet := ACUIHE.Solver.RecursiveFinset.toFinset right.raw
  calc
    ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) ∪ left.raw =
        ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) ∪
          ACUIHE.Solver.RecursiveFinset.ofFinset leftSet :=
      congrArg (fun value =>
        ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) ∪ value)
        left.valid.outer.symm
    _ = ACUIHE.Solver.RecursiveFinset.ofFinset ((leftSet ∩ rightSet) ∪ leftSet) :=
      (ACUIHE.Solver.RecursiveFinset.ofFinset_union _ _).symm
    _ = ACUIHE.Solver.RecursiveFinset.ofFinset leftSet :=
      congrArg ACUIHE.Solver.RecursiveFinset.ofFinset
        (Finset.union_eq_right.mpr Finset.inter_subset_left)
    _ = left.raw := left.valid.outer

theorem meet_below_right {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) :
    Below (Hom := TypeHom) (meet left right) right := by
  let _ := Encodable.decidableEqOfEncodable
    (ACUIHE.Solver.NormalForm.Internal.RawNormalSummand
      TypeConstant Variable TypeHom)
  unfold Below
  apply NormalForm.ext_raw
  rw [canonical_add_raw, meet_raw]
  let leftSet := ACUIHE.Solver.RecursiveFinset.toFinset left.raw
  let rightSet := ACUIHE.Solver.RecursiveFinset.toFinset right.raw
  calc
    ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) ∪ right.raw =
        ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) ∪
          ACUIHE.Solver.RecursiveFinset.ofFinset rightSet :=
      congrArg (fun value =>
        ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) ∪ value)
        right.valid.outer.symm
    _ = ACUIHE.Solver.RecursiveFinset.ofFinset ((leftSet ∩ rightSet) ∪ rightSet) :=
      (ACUIHE.Solver.RecursiveFinset.ofFinset_union _ _).symm
    _ = ACUIHE.Solver.RecursiveFinset.ofFinset rightSet :=
      congrArg ACUIHE.Solver.RecursiveFinset.ofFinset
        (Finset.union_eq_right.mpr Finset.inter_subset_right)
    _ = right.raw := right.valid.outer

theorem meet_greatest {Variable : Type} [Encodable Variable]
    (lower left right : CanonicalType Variable)
    (belowLeft : Below (Hom := TypeHom) lower left)
    (belowRight : Below (Hom := TypeHom) lower right) :
    Below (Hom := TypeHom) lower (meet left right) := by
  let _ := Encodable.decidableEqOfEncodable
    (ACUIHE.Solver.NormalForm.Internal.RawNormalSummand
      TypeConstant Variable TypeHom)
  have lowerSubsetLeft :
      ACUIHE.Solver.RecursiveFinset.toFinset lower.raw ⊆
        ACUIHE.Solver.RecursiveFinset.toFinset left.raw := by
    unfold Below at belowLeft
    have rawEquality : lower.raw ∪ left.raw = left.raw := by
      simpa only [canonical_add_raw] using congrArg NormalFormImpl.raw belowLeft
    have decodedEquality := congrArg ACUIHE.Solver.RecursiveFinset.toFinset rawEquality
    rw [ACUIHE.Solver.RecursiveFinset.toFinset_union] at decodedEquality
    exact Finset.union_eq_right.mp decodedEquality
  have lowerSubsetRight :
      ACUIHE.Solver.RecursiveFinset.toFinset lower.raw ⊆
        ACUIHE.Solver.RecursiveFinset.toFinset right.raw := by
    unfold Below at belowRight
    have rawEquality : lower.raw ∪ right.raw = right.raw := by
      simpa only [canonical_add_raw] using congrArg NormalFormImpl.raw belowRight
    have decodedEquality := congrArg ACUIHE.Solver.RecursiveFinset.toFinset rawEquality
    rw [ACUIHE.Solver.RecursiveFinset.toFinset_union] at decodedEquality
    exact Finset.union_eq_right.mp decodedEquality
  unfold Below
  apply NormalForm.ext_raw
  rw [canonical_add_raw, meet_raw]
  let lowerSet := ACUIHE.Solver.RecursiveFinset.toFinset lower.raw
  let leftSet := ACUIHE.Solver.RecursiveFinset.toFinset left.raw
  let rightSet := ACUIHE.Solver.RecursiveFinset.toFinset right.raw
  have lowerSubsetIntersection : lowerSet ⊆ leftSet ∩ rightSet :=
    fun _ membership => Finset.mem_inter.mpr
      ⟨lowerSubsetLeft membership, lowerSubsetRight membership⟩
  calc
    lower.raw ∪ ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) =
        ACUIHE.Solver.RecursiveFinset.ofFinset lowerSet ∪
          ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) :=
      congrArg (fun value =>
        value ∪ ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet))
        lower.valid.outer.symm
    _ = ACUIHE.Solver.RecursiveFinset.ofFinset (lowerSet ∪ (leftSet ∩ rightSet)) :=
      (ACUIHE.Solver.RecursiveFinset.ofFinset_union _ _).symm
    _ = ACUIHE.Solver.RecursiveFinset.ofFinset (leftSet ∩ rightSet) :=
      congrArg ACUIHE.Solver.RecursiveFinset.ofFinset
        (Finset.union_eq_right.mpr lowerSubsetIntersection)

/-- Difference is statically left-biased; runtime membership does not widen it. -/
def differenceType {Variable : Type} [Encodable Variable]
    (left _right : CanonicalType Variable) : CanonicalType Variable := left

@[simp] theorem differenceType_eq_left {Variable : Type} [Encodable Variable]
    (left right : CanonicalType Variable) : differenceType left right = left := rfl

/-- A ground external rule implementing the irreversible edge demotion. -/
def undirectedEdgeSubsumption
    (tail head payload : GroundTypeTerm) :
    BlockReplacement TypeConstant TypeHom :=
  BlockReplacement.ofSubsumption
    (normalize (undirectedEdge tail head payload))
    (normalize (set (edge tail head payload)))

@[simp] theorem undirectedEdgeSubsumption_pattern
    (tail head payload : GroundTypeTerm) :
    (undirectedEdgeSubsumption tail head payload).pattern =
      normalize (set (edge tail head payload)) := rfl

@[simp] theorem undirectedEdgeSubsumption_replacement
    (tail head payload : GroundTypeTerm) :
    (undirectedEdgeSubsumption tail head payload).replacement =
      normalize (set (edge tail head payload)) +
        normalize (undirectedEdge tail head payload) := rfl

end HypergraphML.External
