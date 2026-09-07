import ACUIHE.Graph.Embedding
import ACUIHE.NormalForm.API

/-!
Normalization and reification for the graph representation of ACUIhE terms.

Normalization first uses the proved recursive ACUIhE normal form. Its
deterministic compilation then splits that form into ACUIh fragments in
dependency postorder. Equal `E` bodies are interned by their solver form, so
the graph shares them and every edge points to an earlier node.
-/

namespace ACUIHE.Graph.TermGraph

universe u v w x

private def reifyFragment
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    (resolve : Alien → ACUIHE.Term Const Var Hom) :
    ACUIh.Term (Atom Const Var Alien) Hom → ACUIHE.Term Const Var Hom
  | .zero => .zero
  | .atom (.constant name) => .const name
  | .atom (.variable name) => .var name
  | .atom (.alien reference) => .free (resolve reference)
  | .add left right =>
      .add (reifyFragment resolve left) (reifyFragment resolve right)
  | .hom name body => .hom name (reifyFragment resolve body)

private instance solverNormalFormUnionCommutative
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Commutative
      (fun left right : Solver.NormalForm Const Var Hom => left ∪ right) :=
  ⟨by
    intro left right
    exact ACUIhE.add_comm (Hom := Hom) left right⟩

private instance solverNormalFormUnionAssociative
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.Associative
      (fun left right : Solver.NormalForm Const Var Hom => left ∪ right) :=
  ⟨by
    intro left middle right
    exact ACUIhE.add_assoc (Hom := Hom) left middle right⟩

private instance solverNormalFormUnionIdempotent
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Std.IdempotentOp
      (fun left right : Solver.NormalForm Const Var Hom => left ∪ right) :=
  ⟨by
    intro value
    exact ACUIhE.add_idem (Hom := Hom) value⟩

private def solverPrefixPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (body : Solver.NormalForm Const Var Hom) :
    Solver.NormalForm Const Var Hom :=
  path.foldr (fun name inner => Solver.prefixHom name inner) body

private def interpretAtom
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (resolve : Alien → Solver.NormalForm Const Var Hom) :
    Atom Const Var Alien → Solver.NormalForm Const Var Hom
  | .constant name => Solver.constantForm name
  | .variable name => Solver.variableForm name
  | .alien reference => Solver.wrapE (resolve reference)

private def interpretSummand
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (resolve : Alien → Solver.NormalForm Const Var Hom)
    (summand : List Hom × Atom Const Var Alien) :
    Solver.NormalForm Const Var Hom :=
  solverPrefixPath summand.1 (interpretAtom resolve summand.2)

private def interpretNormalForm
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (resolve : Alien → Solver.NormalForm Const Var Hom)
    (normalForm : Fragment Const Var Hom Alien) :
    Solver.NormalForm Const Var Hom :=
  normalForm.fold (fun left right => left ∪ right) ∅
    (interpretSummand resolve)

private def interpretTerm
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (resolve : Alien → Solver.NormalForm Const Var Hom) :
    ACUIh.Term (Atom Const Var Alien) Hom → Solver.NormalForm Const Var Hom
  | .zero => ∅
  | .atom atom => interpretAtom resolve atom
  | .add left right => interpretTerm resolve left ∪ interpretTerm resolve right
  | .hom name body => Solver.prefixHom name (interpretTerm resolve body)

private theorem interpretNormalForm_empty
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (resolve : Alien → Solver.NormalForm Const Var Hom) :
    interpretNormalForm resolve ∅ = ∅ := by
  simp [interpretNormalForm]

private theorem interpretNormalForm_insert
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (resolve : Alien → Solver.NormalForm Const Var Hom)
    (summand : List Hom × Atom Const Var Alien)
    (normalForm : Fragment Const Var Hom Alien) :
    interpretNormalForm resolve (insert summand normalForm) =
      interpretSummand resolve summand ∪ interpretNormalForm resolve normalForm := by
  unfold interpretNormalForm
  exact Finset.fold_insert_idem

private theorem interpretNormalForm_union
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (resolve : Alien → Solver.NormalForm Const Var Hom)
    (left right : Fragment Const Var Hom Alien) :
    interpretNormalForm resolve (left ∪ right) =
      interpretNormalForm resolve left ∪ interpretNormalForm resolve right := by
  induction left using Finset.induction with
  | empty =>
      rw [Finset.empty_union, interpretNormalForm_empty]
      symm
      exact
        (Std.Commutative.comm
          (∅ : Solver.NormalForm Const Var Hom)
          (interpretNormalForm resolve right)).trans
        (ACUIhE.add_zero (Hom := Hom) _)
  | @insert summand left notMember inductionHypothesis =>
      rw [Finset.insert_union, interpretNormalForm_insert,
        interpretNormalForm_insert, inductionHypothesis]
      exact (Std.Associative.assoc _ _ _).symm

private theorem solverPrefixPath_cons
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (name : Hom) (path : List Hom) (body : Solver.NormalForm Const Var Hom) :
    solverPrefixPath (name :: path) body =
      Solver.prefixHom name (solverPrefixPath path body) := rfl

private theorem interpretNormalForm_prefixHom
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (resolve : Alien → Solver.NormalForm Const Var Hom)
    (name : Hom) (normalForm : Fragment Const Var Hom Alien) :
    interpretNormalForm resolve (ACUIh.NormalForm.prefixHom name normalForm) =
      Solver.prefixHom name (interpretNormalForm resolve normalForm) := by
  induction normalForm using Finset.induction with
  | empty => simp [interpretNormalForm_empty]
  | @insert summand normalForm notMember inductionHypothesis =>
      rcases summand with ⟨path, atom⟩
      rw [show ACUIh.NormalForm.prefixHom name
          (insert (path, atom) normalForm) =
        insert (name :: path, atom)
          (ACUIh.NormalForm.prefixHom name normalForm) by
        rw [ACUIh.NormalForm.prefixHom, Finset.map_insert]
        rfl]
      rw [interpretNormalForm_insert, interpretNormalForm_insert,
        inductionHypothesis, interpretSummand, solverPrefixPath_cons,
        Solver.prefixHom_union]
      rfl

private theorem interpretNormalForm_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (resolve : Alien → Solver.NormalForm Const Var Hom)
    (term : ACUIh.Term (Atom Const Var Alien) Hom) :
    interpretNormalForm resolve (ACUIh.Term.normalize term) =
      interpretTerm resolve term := by
  induction term with
  | zero => exact interpretNormalForm_empty resolve
  | atom atom =>
      rw [ACUIh.Term.normalize_atom, ACUIh.NormalForm.generator]
      change interpretNormalForm resolve (insert ([], atom) ∅) = _
      rw [
        interpretNormalForm_insert, interpretNormalForm_empty]
      exact ACUIhE.add_zero (Hom := Hom) _
  | add left right leftHypothesis rightHypothesis =>
      rw [ACUIh.Term.normalize_add, interpretNormalForm_union,
        leftHypothesis, rightHypothesis]
      rfl
  | hom name body inductionHypothesis =>
      rw [ACUIh.Term.normalize_hom, interpretNormalForm_prefixHom,
        inductionHypothesis]
      rfl

private theorem normalize_reifyFragment
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (resolve : Alien → ACUIHE.Term Const Var Hom)
    (term : ACUIh.Term (Atom Const Var Alien) Hom) :
    Solver.normalize (reifyFragment resolve term) =
      interpretTerm (fun reference => Solver.normalize (resolve reference)) term := by
  induction term with
  | zero => rfl
  | atom atom => cases atom <;> rfl
  | add left right leftHypothesis rightHypothesis =>
      rw [reifyFragment, Solver.normalize_add, interpretTerm,
        leftHypothesis, rightHypothesis]
  | hom name body inductionHypothesis =>
      rw [reifyFragment, Solver.normalize_hom, interpretTerm,
        inductionHypothesis]

private theorem normalize_reifyFragment_normalForm
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [Encodable Alien]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    [DecidableEq Alien]
    (resolve : Alien → ACUIHE.Term Const Var Hom)
    (normalForm : Fragment Const Var Hom Alien) :
    Solver.normalize
        (reifyFragment resolve (ACUIh.NormalForm.reify normalForm)) =
      interpretNormalForm
        (fun reference => Solver.normalize (resolve reference)) normalForm := by
  rw [normalize_reifyFragment, ← interpretNormalForm_normalize,
    ACUIh.NormalForm.normalize_reify]

/-- Reify the ACUIhE expression rooted at one graph node. -/
def reifyNode
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) (node : graph.NodeId) :
    ACUIHE.Term Const Var Hom :=
  reifyFragment
    (fun target =>
      reifyNode graph
        ⟨target.val, Nat.lt_trans target.isLt node.isLt⟩)
    (ACUIh.NormalForm.reify
      (Fragment.ofParts (graph.nodes node) (graph.edges node)))
termination_by node.val
decreasing_by exact target.isLt

/-- Reifying a node and normalizing interprets its stored ACUIh fragment. -/
private theorem normalize_reifyNode
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) (node : graph.NodeId) :
    Solver.normalize (reifyNode graph node) =
      interpretNormalForm
        (fun target =>
          Solver.normalize
            (reifyNode graph
              ⟨target.val, Nat.lt_trans target.isLt node.isLt⟩))
        (Fragment.ofParts (graph.nodes node) (graph.edges node)) := by
  rw [reifyNode, normalize_reifyFragment_normalForm]

/-- Reify the expression denoted by the root of a term graph. -/
def reify
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (graph : TermGraph Const Var Hom) : ACUIHE.Term Const Var Hom :=
  reifyNode graph graph.root

/-- Find the first occurrence of a value in a finite family. -/
private def findIndex? [DecidableEq α] (value : α) :
    {n : Nat} → (Fin n → α) → Option (Fin n)
  | 0, _ => none
  | n + 1, values =>
      let first : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      if values first = value then
        some first
      else
        (findIndex? value (fun index => values index.succ)).map Fin.succ

private theorem findIndex?_sound [DecidableEq α] (value : α)
    {n : Nat} (values : Fin n → α) {index : Fin n}
    (found : findIndex? value values = some index) :
    values index = value := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n inductionHypothesis =>
      simp only [findIndex?] at found
      split at found <;> rename_i equality
      · cases found
        exact equality
      · generalize recursiveEquality :
          findIndex? value (fun inner => values inner.succ) = recursive at found
        cases recursive with
        | none => simp at found
        | some inner =>
            simp only [Option.map_some, Option.some.injEq] at found
            subst index
            exact inductionHypothesis _ recursiveEquality

private theorem findIndex?_complete [DecidableEq α] (value : α)
    {n : Nat} (values : Fin n → α)
    (existsIndex : ∃ index, values index = value) :
    ∃ index, findIndex? value values = some index := by
  induction n with
  | zero =>
      rcases existsIndex with ⟨index, _⟩
      exact Fin.elim0 index
  | succ n inductionHypothesis =>
      simp only [findIndex?]
      split <;> rename_i firstEquality
      · exact ⟨⟨0, Nat.zero_lt_succ n⟩, rfl⟩
      · have tailExists : ∃ index : Fin n, values index.succ = value := by
          rcases existsIndex with ⟨index, equality⟩
          cases index using Fin.cases with
          | zero => exact False.elim (firstEquality equality)
          | succ inner => exact ⟨inner, equality⟩
        rcases inductionHypothesis (fun index => values index.succ) tailExists with
          ⟨index, found⟩
        exact ⟨index.succ, by rw [found]; rfl⟩

private def fragmentPath
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    (path : List Hom) (atom : Atom Const Var Alien) :
    ACUIh.Term (Atom Const Var Alien) Hom :=
  path.foldr (fun name body => .hom name body) (.atom atom)

private theorem interpretTerm_fragmentPath
    {Const : Type u} {Var : Type v} {Hom : Type w} {Alien : Type x}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (resolve : Alien → Solver.NormalForm Const Var Hom)
    (path : List Hom) (atom : Atom Const Var Alien) :
    interpretTerm resolve (fragmentPath path atom) =
      solverPrefixPath path (interpretAtom resolve atom) := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      simp only [fragmentPath, List.foldr_cons, interpretTerm,
        solverPrefixPath_cons]
      exact congrArg (Solver.prefixHom name) inductionHypothesis

/-- The alien forms mentioned by an open ACUIh fragment are allocated. -/
private def AliensIn
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (forms : List (Solver.NormalForm Const Var Hom)) :
    ACUIh.Term
      (Atom Const Var (Solver.NormalForm Const Var Hom)) Hom → Prop
  | .zero => True
  | .atom (.constant _) => True
  | .atom (.variable _) => True
  | .atom (.alien form) => form ∈ forms
  | .add left right => AliensIn forms left ∧ AliensIn forms right
  | .hom _ body => AliensIn forms body

private theorem AliensIn.mono
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {source target : List (Solver.NormalForm Const Var Hom)}
    {term : ACUIh.Term
      (Atom Const Var (Solver.NormalForm Const Var Hom)) Hom}
    (included : ∀ form, form ∈ source → form ∈ target)
    (available : AliensIn source term) : AliensIn target term := by
  induction term with
  | zero => trivial
  | atom atom =>
      cases atom with
      | constant => trivial
      | «variable» => trivial
      | alien form => exact included form available
  | add left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis available.1, rightHypothesis available.2⟩
  | hom name body inductionHypothesis => exact inductionHypothesis available

private theorem aliensIn_fragmentPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (forms : List (Solver.NormalForm Const Var Hom))
    (path : List Hom)
    (atom : Atom Const Var (Solver.NormalForm Const Var Hom))
    (available : AliensIn forms (.atom atom)) :
    AliensIn forms (fragmentPath path atom) := by
  induction path with
  | nil => exact available
  | cons name path inductionHypothesis =>
      exact inductionHypothesis

private structure NodeSpec
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  form : Solver.NormalForm Const Var Hom
  fragment : ACUIh.Term
    (Atom Const Var (Solver.NormalForm Const Var Hom)) Hom
  sound : interpretTerm (fun form => form) fragment = form

private def nodeForms
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (nodes : List (NodeSpec Const Var Hom)) :
    List (Solver.NormalForm Const Var Hom) :=
  nodes.map NodeSpec.form

private def appendUniqueNode
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (nodes : List (NodeSpec Const Var Hom)) (node : NodeSpec Const Var Hom) :
    List (NodeSpec Const Var Hom) :=
  if node.form ∈ nodeForms nodes then nodes else nodes ++ [node]

private def mergeNodes
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : List (NodeSpec Const Var Hom)) :
    List (NodeSpec Const Var Hom) :=
  right.foldl appendUniqueNode left

private theorem mem_nodeForms_appendUniqueNode_left
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {nodes : List (NodeSpec Const Var Hom)} {node : NodeSpec Const Var Hom}
    {form : Solver.NormalForm Const Var Hom}
    (membership : form ∈ nodeForms nodes) :
    form ∈ nodeForms (appendUniqueNode nodes node) := by
  unfold appendUniqueNode
  split
  · exact membership
  · simp only [nodeForms, List.map_append, List.mem_append]
    exact Or.inl membership

private theorem mem_nodeForms_appendUniqueNode_root
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (nodes : List (NodeSpec Const Var Hom)) (node : NodeSpec Const Var Hom) :
    node.form ∈ nodeForms (appendUniqueNode nodes node) := by
  unfold appendUniqueNode
  split <;> rename_i membership
  · exact membership
  · simp [nodeForms]

private theorem mem_nodeForms_mergeNodes_left
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : List (NodeSpec Const Var Hom))
    {form : Solver.NormalForm Const Var Hom}
    (membership : form ∈ nodeForms left) :
    form ∈ nodeForms (mergeNodes left right) := by
  induction right generalizing left with
  | nil => exact membership
  | cons node right inductionHypothesis =>
      exact inductionHypothesis (appendUniqueNode left node)
        (mem_nodeForms_appendUniqueNode_left membership)

private theorem mem_nodeForms_mergeNodes_right
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : List (NodeSpec Const Var Hom))
    {form : Solver.NormalForm Const Var Hom}
    (membership : form ∈ nodeForms right) :
    form ∈ nodeForms (mergeNodes left right) := by
  induction right generalizing left with
  | nil => simp [nodeForms] at membership
  | cons node right inductionHypothesis =>
      simp only [nodeForms, List.map_cons, List.mem_cons] at membership
      unfold mergeNodes
      simp only [List.foldl_cons]
      rcases membership with equality | membership
      · subst form
        exact mem_nodeForms_mergeNodes_left _ _
          (mem_nodeForms_appendUniqueNode_root left node)
      · exact inductionHypothesis (appendUniqueNode left node) membership

/-- A certificate that every node refers only to preceding nodes. -/
private inductive ClosedNodes
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    List (NodeSpec Const Var Hom) → Prop where
  | nil : ClosedNodes []
  | snoc {nodes : List (NodeSpec Const Var Hom)} {node : NodeSpec Const Var Hom}
      (closed : ClosedNodes nodes)
      (available : AliensIn (nodeForms nodes) node.fragment) :
      ClosedNodes (nodes ++ [node])

private theorem closedNodes_appendUniqueNode
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {nodes : List (NodeSpec Const Var Hom)} {node : NodeSpec Const Var Hom}
    (closed : ClosedNodes nodes)
    (available : AliensIn (nodeForms nodes) node.fragment) :
    ClosedNodes (appendUniqueNode nodes node) := by
  unfold appendUniqueNode
  split
  · exact closed
  · exact ClosedNodes.snoc closed available

private theorem closedNodes_mergeNodes
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {left right : List (NodeSpec Const Var Hom)}
    (leftClosed : ClosedNodes left) (rightClosed : ClosedNodes right) :
    ClosedNodes (mergeNodes left right) := by
  induction rightClosed generalizing left with
  | nil => simpa [mergeNodes] using leftClosed
  | @snoc right node rightClosed available inductionHypothesis =>
      rw [mergeNodes, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      apply closedNodes_appendUniqueNode
        (inductionHypothesis leftClosed)
      exact AliensIn.mono
        (fun form membership =>
          mem_nodeForms_mergeNodes_right left right membership)
        available

private theorem closedNodes_getElem
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {nodes : List (NodeSpec Const Var Hom)}
    (closed : ClosedNodes nodes) (index : Nat) (inBounds : index < nodes.length) :
    AliensIn (nodeForms (nodes.take index)) nodes[index].fragment := by
  induction closed with
  | nil => simp at inBounds
  | @snoc nodes node closed available inductionHypothesis =>
      by_cases earlier : index < nodes.length
      · rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
        rw [List.getElem_append_left earlier]
        exact inductionHypothesis earlier
      · have atEnd : index = nodes.length := by
          simp only [List.length_append, List.length_singleton] at inBounds
          omega
        subst index
        rw [List.take_left]
        simpa using available

private theorem ClosedNodes.available
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {nodes : List (NodeSpec Const Var Hom)}
    (closed : ClosedNodes nodes) (node : Fin nodes.length) :
    AliensIn (nodeForms (nodes.take node.val)) (nodes.get node).fragment := by
  rw [List.get_eq_getElem]
  exact closedNodes_getElem closed node.val node.isLt

private structure Compilation
    (Const : Type u) (Var : Type v) (Hom : Type w)
    [Encodable Const] [Encodable Var] [Encodable Hom] where
  nodes : List (NodeSpec Const Var Hom)
  root : NodeSpec Const Var Hom
  closed : ClosedNodes nodes
  rootAvailable : AliensIn (nodeForms nodes) root.fragment

private def compilationZero
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom] :
    Compilation Const Var Hom where
  nodes := []
  root := ⟨∅, .zero, rfl⟩
  closed := .nil
  rootAvailable := trivial

private def compilationAdd
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (left right : Compilation Const Var Hom) : Compilation Const Var Hom where
  nodes := mergeNodes left.nodes right.nodes
  root :=
    ⟨left.root.form ∪ right.root.form,
      .add left.root.fragment right.root.fragment,
      by rw [interpretTerm, left.root.sound, right.root.sound]⟩
  closed := closedNodes_mergeNodes left.closed right.closed
  rootAvailable := by
    constructor
    · exact AliensIn.mono (source := nodeForms left.nodes)
        (fun _ membership =>
          mem_nodeForms_mergeNodes_left left.nodes right.nodes membership)
        left.rootAvailable
    · exact AliensIn.mono (source := nodeForms right.nodes)
        (fun _ membership =>
          mem_nodeForms_mergeNodes_right left.nodes right.nodes membership)
        right.rootAvailable

private def compilationConstant
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Const) : Compilation Const Var Hom where
  nodes := []
  root :=
    ⟨solverPrefixPath path (Solver.constantForm name),
      fragmentPath path (.constant name),
      interpretTerm_fragmentPath (fun form => form) path (.constant name)⟩
  closed := .nil
  rootAvailable := aliensIn_fragmentPath [] path (.constant name) trivial

private def compilationVariable
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (name : Var) : Compilation Const Var Hom where
  nodes := []
  root :=
    ⟨solverPrefixPath path (Solver.variableForm name),
      fragmentPath path (.variable name),
      interpretTerm_fragmentPath (fun form => form) path (.variable name)⟩
  closed := .nil
  rootAvailable := aliensIn_fragmentPath [] path (.variable name) trivial

private def compilationEOperator
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (body : Compilation Const Var Hom) :
    Compilation Const Var Hom where
  nodes := appendUniqueNode body.nodes body.root
  root :=
    ⟨solverPrefixPath path (Solver.wrapE body.root.form),
      fragmentPath path (.alien body.root.form),
      interpretTerm_fragmentPath (fun form => form) path (.alien body.root.form)⟩
  closed := closedNodes_appendUniqueNode body.closed body.rootAvailable
  rootAvailable := by
    apply aliensIn_fragmentPath
    exact mem_nodeForms_appendUniqueNode_root body.nodes body.root

/-- Compile a recursive normal form to open fragments and a dependency order. -/
private def compile
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : Solver.NormalForm Const Var Hom) : Compilation Const Var Hom :=
  normalForm.fold compilationZero compilationAdd
    compilationConstant compilationVariable compilationEOperator

private theorem normalize_solverReifyPath
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (path : List Hom) (body : ACUIHE.Term Const Var Hom) :
    Solver.normalize (Solver.reifyPath path body) =
      solverPrefixPath path (Solver.normalize body) := by
  induction path with
  | nil => rfl
  | cons name path inductionHypothesis =>
      simp only [Solver.reifyPath, List.foldr_cons, Solver.normalize_hom,
        solverPrefixPath_cons]
      exact congrArg (Solver.prefixHom name) inductionHypothesis

/-- The form computed by compilation is precisely normal-form canonicalization. -/
private theorem compile_root_form
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (normalForm : Solver.NormalForm Const Var Hom) :
    (compile normalForm).root.form =
      Solver.normalize (Solver.reify normalForm) := by
  let semanticFold : Solver.NormalForm Const Var Hom :=
    normalForm.fold ∅ (fun left right => left ∪ right)
      (fun path name => solverPrefixPath path (Solver.constantForm name))
      (fun path name => solverPrefixPath path (Solver.variableForm name))
      (fun path body => solverPrefixPath path (Solver.wrapE body))
  have compilationProjection : (compile normalForm).root.form = semanticFold := by
    unfold compile semanticFold
    apply Solver.NormalForm.fold_hom
      (map := fun result : Compilation Const Var Hom => result.root.form)
    · rfl
    · intro left right
      rfl
    · intro path name
      rfl
    · intro path name
      rfl
    · intro path body
      rfl
  have normalizationProjection :
      Solver.normalize (Solver.reify normalForm) = semanticFold := by
    unfold Solver.reify semanticFold
    apply Solver.NormalForm.fold_hom
      (map := Solver.normalize)
    · rfl
    · intro left right
      rfl
    · intro path name
      exact normalize_solverReifyPath path (.const name)
    · intro path name
      exact normalize_solverReifyPath path (.var name)
    · intro path body
      exact normalize_solverReifyPath path (.free body)
  exact compilationProjection.trans normalizationProjection.symm

/-- Replace each open-fragment alien by its allocated graph-node reference. -/
private def allocateFragment
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {n : Nat} (available : Fin n → Solver.NormalForm Const Var Hom) :
    ACUIh.Term (Atom Const Var (Solver.NormalForm Const Var Hom)) Hom →
      ACUIh.Term (Atom Const Var (Fin n)) Hom
  | .zero => .zero
  | .atom (.constant name) => .atom (.constant name)
  | .atom (.variable name) => .atom (.variable name)
  | .atom (.alien form) =>
      match findIndex? form available with
      | none => .zero
      | some target => .atom (.alien target)
  | .add left right =>
      .add (allocateFragment available left) (allocateFragment available right)
  | .hom name body => .hom name (allocateFragment available body)

private def earlierSpecForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (specs : List (NodeSpec Const Var Hom))
    (node : Fin specs.length) (target : Fin node.val) :
    Solver.NormalForm Const Var Hom :=
  (specs.get ⟨target.val, Nat.lt_trans target.isLt node.isLt⟩).form

private def FormsAvailable
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    {n : Nat} (available : Fin n → Solver.NormalForm Const Var Hom) :
    ACUIh.Term (Atom Const Var (Solver.NormalForm Const Var Hom)) Hom → Prop
  | .zero => True
  | .atom (.constant _) => True
  | .atom (.variable _) => True
  | .atom (.alien form) => ∃ target, available target = form
  | .add left right =>
      FormsAvailable available left ∧ FormsAvailable available right
  | .hom _ body => FormsAvailable available body

private theorem formsAvailable_of_aliensIn_take
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    (specs : List (NodeSpec Const Var Hom)) (node : Fin specs.length)
    (term : ACUIh.Term
      (Atom Const Var (Solver.NormalForm Const Var Hom)) Hom)
    (available : AliensIn (nodeForms (specs.take node.val)) term) :
    FormsAvailable (earlierSpecForm specs node) term := by
  induction term with
  | zero => trivial
  | atom atom =>
      cases atom with
      | constant => trivial
      | «variable» => trivial
      | alien form =>
          rcases List.mem_iff_get.mp available with ⟨index, indexForm⟩
          have takeLength : (specs.take node.val).length = node.val := by
            simp [List.length_take]
          let target : Fin node.val :=
            ⟨index.val, by
              simpa [nodeForms, takeLength] using index.isLt⟩
          refine ⟨target, ?_⟩
          unfold earlierSpecForm
          rw [List.get_eq_getElem]
          rw [List.get_eq_getElem] at indexForm
          simpa [nodeForms, target] using indexForm
  | add left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis available.1, rightHypothesis available.2⟩
  | hom name body inductionHypothesis => exact inductionHypothesis available

private theorem interpretTerm_allocateFragment
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    {n : Nat} (available : Fin n → Solver.NormalForm Const Var Hom)
    (term : ACUIh.Term
      (Atom Const Var (Solver.NormalForm Const Var Hom)) Hom)
    (complete : FormsAvailable available term) :
    interpretTerm available (allocateFragment available term) =
      interpretTerm (fun form => form) term := by
  induction term with
  | zero => rfl
  | atom atom =>
      cases atom with
      | constant => rfl
      | «variable» => rfl
      | alien form =>
          rcases complete with ⟨target, targetForm⟩
          rcases findIndex?_complete form available ⟨target, targetForm⟩ with
            ⟨found, foundEquality⟩
          have foundForm := findIndex?_sound form available foundEquality
          simp only [allocateFragment, foundEquality, interpretTerm, interpretAtom]
          rw [foundForm]
  | add left right leftHypothesis rightHypothesis =>
      rw [allocateFragment, interpretTerm,
        leftHypothesis complete.1, rightHypothesis complete.2]
      rfl
  | hom name body inductionHypothesis =>
      rw [allocateFragment, interpretTerm,
        inductionHypothesis complete]
      rfl

private def fragmentAt
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (specs : List (NodeSpec Const Var Hom)) (node : Fin specs.length) :
    Fragment Const Var Hom (Fin node.val) :=
  ACUIh.Term.normalize
    (allocateFragment (earlierSpecForm specs node) (specs.get node).fragment)

private theorem interpretNormalForm_fragmentAt
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (specs : List (NodeSpec Const Var Hom)) (closed : ClosedNodes specs)
    (node : Fin specs.length) :
    interpretNormalForm (earlierSpecForm specs node) (fragmentAt specs node) =
      (specs.get node).form := by
  rw [fragmentAt, interpretNormalForm_normalize]
  rw [interpretTerm_allocateFragment]
  · exact (specs.get node).sound
  · exact formsAvailable_of_aliensIn_take specs node _
      (closed.available node)

private def graphOfSpecs
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (specs : List (NodeSpec Const Var Hom)) (root : Fin specs.length) :
    TermGraph Const Var Hom :=
  TermGraph.ofFragments specs.length (fragmentAt specs) root

private def graphNodeOfSpec
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (specs : List (NodeSpec Const Var Hom)) (root node : Fin specs.length) :
    (graphOfSpecs specs root).NodeId :=
  ⟨node.val, by simp [graphOfSpecs, TermGraph.ofFragments, node.isLt]⟩

private theorem normalize_reifyNode_graphOfSpecs
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (specs : List (NodeSpec Const Var Hom)) (closed : ClosedNodes specs)
    (root node : Fin specs.length) :
    Solver.normalize
        (reifyNode (graphOfSpecs specs root)
          (graphNodeOfSpec specs root node)) =
      (specs.get node).form := by
  rw [normalize_reifyNode]
  change interpretNormalForm
      (fun target =>
        Solver.normalize
          (reifyNode (graphOfSpecs specs root)
            ⟨target.val, Nat.lt_trans target.isLt node.isLt⟩))
      (Fragment.ofParts
        (fragmentAt specs node).nodePart
        (fragmentAt specs node).edgePart) = _
  rw [Fragment.ofParts_nodePart_edgePart]
  have resolverEquality :
      (fun target =>
        Solver.normalize
          (reifyNode (graphOfSpecs specs root)
            ⟨target.val, Nat.lt_trans target.isLt node.isLt⟩)) =
        earlierSpecForm specs node := by
    funext target
    simpa [graphNodeOfSpec, earlierSpecForm] using
      normalize_reifyNode_graphOfSpecs specs closed root
        ⟨target.val, Nat.lt_trans target.isLt node.isLt⟩
  rw [resolverEquality]
  exact interpretNormalForm_fragmentAt specs closed node
termination_by node.val
decreasing_by exact target.isLt

private def normalizeForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (normalForm : Solver.NormalForm Const Var Hom) : TermGraph Const Var Hom :=
  let compiled := compile normalForm
  let specs := compiled.nodes ++ [compiled.root]
  graphOfSpecs specs
    ⟨compiled.nodes.length, by simp [specs]⟩

/-- Normalize an ACUIhE term to its deterministic, dependency-ordered graph. -/
def normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (term : ACUIHE.Term Const Var Hom) : TermGraph Const Var Hom :=
  normalizeForm (Solver.normalize term)

private theorem normalize_reify_normalizeForm
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (normalForm : Solver.NormalForm Const Var Hom) :
    Solver.normalize (reify (normalizeForm normalForm)) =
      Solver.normalize (Solver.reify normalForm) := by
  let compiled := compile normalForm
  let specs := compiled.nodes ++ [compiled.root]
  let root : Fin specs.length :=
    ⟨compiled.nodes.length, by simp [specs]⟩
  have closed : ClosedNodes specs := by
    exact ClosedNodes.snoc compiled.closed compiled.rootAvailable
  have nodeSemantics :=
    normalize_reifyNode_graphOfSpecs specs closed root root
  calc
    Solver.normalize (reify (normalizeForm normalForm)) =
        (specs.get root).form := by
      change Solver.normalize
        (reifyNode (graphOfSpecs specs root) (graphOfSpecs specs root).root) = _
      have rootEquality :
          (graphOfSpecs specs root).root = graphNodeOfSpec specs root root := by
        apply Fin.ext
        rfl
      rw [rootEquality]
      exact nodeSemantics
    _ = compiled.root.form := by
      simp [specs, root]
    _ = Solver.normalize (Solver.reify normalForm) :=
      compile_root_form normalForm

/-- Reifying a normalized graph recovers the term's recursive normal form. -/
@[simp]
theorem normalize_reify_normalize
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    (term : ACUIHE.Term Const Var Hom) :
    Solver.normalize (reify (normalize term)) = Solver.normalize term := by
  rw [normalize, normalize_reify_normalizeForm]
  exact Solver.canonicalize_normalize term

/-- Graph normalization depends only on the recursive ACUIhE normal form. -/
theorem normalize_eq_of_solver_normalize_eq
    {Const : Type u} {Var : Type v} {Hom : Type w}
    [Encodable Const] [Encodable Var] [Encodable Hom]
    [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]
    {left right : ACUIHE.Term Const Var Hom}
    (equality : Solver.normalize left = Solver.normalize right) :
    normalize left = normalize right := by
  exact congrArg normalizeForm equality

end ACUIHE.Graph.TermGraph
