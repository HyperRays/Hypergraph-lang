import ACUIHE.Optimized.FILO.Kernel

/-!
# Soundness of FILO reconstruction

The central invariant relates a shortcut at a mirrored tree path to the
ordinary coefficient-first word represented there.  Exact resolver edges
ensure that a tracked atom `(X,p)` at path `q` can be unwound to a bare `X`
at a unique prefix of `q`, with `q = prefix ++ reverse p`.
-/

namespace ACUIHE.Solver.Search

universe u

namespace Tree

/-- Follow an explicit branch path and retain the reached subtree. -/
def descend? {Branch Label : Type u}
    (tree : Tree Branch Label) : List Branch → Option (Tree Branch Label)
  | [] => some tree
  | branch :: rest =>
      match tree with
      | .leaf _ => none
      | .node _ children => descend? (children branch) rest

@[simp]
theorem descend?_nil {Branch Label : Type u} (tree : Tree Branch Label) :
    tree.descend? [] = some tree := by
  cases tree <;> rfl

@[simp]
theorem descend?_leaf_cons {Branch Label : Type u}
    (label : Label) (branch : Branch) (rest : List Branch) :
    (Tree.leaf label).descend? (branch :: rest) = none := rfl

@[simp]
theorem descend?_node_cons {Branch Label : Type u}
    (label : Label) (children : Branch → Tree Branch Label)
    (branch : Branch) (rest : List Branch) :
    (Tree.node label children).descend? (branch :: rest) =
      (children branch).descend? rest := rfl

theorem descend?_append {Branch Label : Type u}
    (tree : Tree Branch Label) (first second : List Branch) :
    tree.descend? (first ++ second) =
      (tree.descend? first).bind fun subtree => subtree.descend? second := by
  induction first generalizing tree with
  | nil => simp
  | cons branch rest inductionHypothesis =>
      cases tree with
      | leaf label => simp [descend?]
      | node label children =>
          simp only [List.cons_append, descend?]
          exact inductionHypothesis (children branch)

@[simp]
theorem mem_language_iff_descend
    {Branch Label : Type u} [Fintype Branch] [DecidableEq Branch]
    (accept : Label → Bool) (tree : Tree Branch Label) (path : List Branch) :
    path ∈ tree.language accept ↔
      ∃ subtree, tree.descend? path = some subtree ∧
        accept subtree.root = true := by
  induction tree generalizing path with
  | leaf label =>
      cases path with
      | nil =>
          by_cases checked : accept label = true <;>
            simp [descend?, Tree.language, Tree.root, checked]
      | cons branch rest =>
          by_cases checked : accept label = true <;>
            simp [descend?, Tree.language, checked]
  | node label children inductionHypothesis =>
      cases path with
      | nil =>
          by_cases checked : accept label = true <;>
            simp [descend?, Tree.language, Tree.root, checked]
      | cons branch rest =>
          by_cases checked : accept label = true <;>
            simp [descend?, Tree.language, checked,
              inductionHypothesis branch]

end Tree

end ACUIHE.Solver.Search

namespace ACUIHE.Solver.Search.FiniteLanguageSystem

open ACUIHE.Optimized.FILO
open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

local instance encodableDecidableEqSound {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

variable {Row Variable Hom : Type u}
  [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]

theorem Derivation.descend
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree subtree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (derived : problem.Derivation tree) (path : List Hom)
    (reached : tree.descend? path = some subtree) :
    problem.Derivation subtree := by
  induction path generalizing tree with
  | nil =>
      simp only [Tree.descend?_nil, Option.some.injEq] at reached
      subst tree
      exact derived
  | cons role rest inductionHypothesis =>
      cases derived with
      | leaf valid terminal => simp at reached
      | @node shortcut children valid resolves descendants =>
          exact inductionHypothesis (descendants role) reached

/-- A tracked variable prefix forces the corresponding role child to exist.
This is where the leaf condition is used: a leaf claims that the empty child
resolves it, which is impossible while a defined prefixed atom is required. -/
theorem Derivation.extendVarOne
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (derived : problem.Derivation tree)
    (index : Variable) (tail : List Hom) (role : Hom)
    (tailPresent : Atom.var index tail ∈ tree.root)
    (bounded : (role :: tail).length ≤ problem.pathBound) :
    ∃ child,
      tree.descend? [role] = some child ∧
      Atom.var index (role :: tail) ∈ child.root ∧
      problem.Derivation child := by
  cases derived with
  | @leaf shortcut valid terminal =>
      have resolved := terminal role
      have condition := resolved.2 (Atom.var index (role :: tail))
        ((problem.var_mem_atoms_iff index (role :: tail)).mpr bounded)
      simp [resolveAtom] at condition
      exact False.elim (condition tailPresent)
  | @node shortcut children valid resolves descendants =>
      refine ⟨children role, by simp [Tree.descend?], ?_, descendants role⟩
      have condition := (resolves role).2 (Atom.var index (role :: tail))
        ((problem.var_mem_atoms_iff index (role :: tail)).mpr bounded)
      have equivalence : Atom.var index (role :: tail) ∈ (children role).root ↔
          Atom.var index tail ∈ shortcut := by
        simpa [resolveAtom] using condition
      exact equivalence.mpr tailPresent

theorem Derivation.extendConstantOne
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (derived : problem.Derivation tree)
    (tail : List Hom) (role : Hom)
    (tailPresent : Atom.constant tail ∈ tree.root)
    (bounded : (role :: tail).length ≤ problem.pathBound) :
    ∃ child,
      tree.descend? [role] = some child ∧
      Atom.constant (role :: tail) ∈ child.root ∧
      problem.Derivation child := by
  cases derived with
  | @leaf shortcut valid terminal =>
      have resolved := terminal role
      have condition := resolved.2 (Atom.constant (role :: tail))
        ((problem.constant_mem_atoms_iff (role :: tail)).mpr bounded)
      simp [resolveAtom] at condition
      exact False.elim (condition tailPresent)
  | @node shortcut children valid resolves descendants =>
      refine ⟨children role, by simp [Tree.descend?], ?_, descendants role⟩
      have condition := (resolves role).2 (Atom.constant (role :: tail))
        ((problem.constant_mem_atoms_iff (role :: tail)).mpr bounded)
      have equivalence : Atom.constant (role :: tail) ∈ (children role).root ↔
          Atom.constant tail ∈ shortcut := by
        simpa [resolveAtom] using condition
      exact equivalence.mpr tailPresent

theorem Derivation.extendVar
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (derived : problem.Derivation tree)
    (index : Variable) (path : List Hom)
    (barePresent : Atom.var index [] ∈ tree.root)
    (bounded : path.length ≤ problem.pathBound) :
    ∃ subtree,
      tree.descend? path.reverse = some subtree ∧
      Atom.var index path ∈ subtree.root := by
  induction path with
  | nil => exact ⟨tree, by simp, barePresent⟩
  | cons role tail inductionHypothesis =>
      have tailBound : tail.length ≤ problem.pathBound :=
        le_trans (Nat.le_succ tail.length) bounded
      rcases inductionHypothesis tailBound with
        ⟨middle, reachedMiddle, tailPresent⟩
      have middleDerived := derived.descend problem tail.reverse reachedMiddle
      rcases middleDerived.extendVarOne problem index tail role tailPresent bounded with
        ⟨child, reachedChild, childPresent, childDerived⟩
      refine ⟨child, ?_, childPresent⟩
      rw [List.reverse_cons, Tree.descend?_append, reachedMiddle]
      exact reachedChild

theorem Derivation.extendConstant
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (derived : problem.Derivation tree)
    (path : List Hom)
    (barePresent : Atom.constant [] ∈ tree.root)
    (bounded : path.length ≤ problem.pathBound) :
    ∃ subtree,
      tree.descend? path.reverse = some subtree ∧
      Atom.constant path ∈ subtree.root := by
  induction path with
  | nil => exact ⟨tree, by simp, barePresent⟩
  | cons role tail inductionHypothesis =>
      have tailBound : tail.length ≤ problem.pathBound :=
        le_trans (Nat.le_succ tail.length) bounded
      rcases inductionHypothesis tailBound with
        ⟨middle, reachedMiddle, tailPresent⟩
      have middleDerived := derived.descend problem tail.reverse reachedMiddle
      rcases middleDerived.extendConstantOne problem tail role tailPresent bounded with
        ⟨child, reachedChild, childPresent, childDerived⟩
      refine ⟨child, ?_, childPresent⟩
      rw [List.reverse_cons, Tree.descend?_append, reachedMiddle]
      exact reachedChild

/-- Backward semantic invariant at one reached node. -/
def NodeInvariant
    (_problem : FiniteLanguageSystem Row Variable Hom)
    (whole : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (mirrored : List Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) : Prop :=
  (∀ index path, Atom.var index path ∈ shortcut →
      ∃ base subtree,
        mirrored = base ++ path.reverse ∧
        whole.descend? base = some subtree ∧
        Atom.var index [] ∈ subtree.root) ∧
    ∀ path, Atom.constant path ∈ shortcut → mirrored = path.reverse

/-- The invariant recursively holds at every node of a derivation. -/
def Coherent
    (problem : FiniteLanguageSystem Row Variable Hom)
    (whole : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (mirrored : List Hom) :
    Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)) → Prop
  | .leaf shortcut => problem.NodeInvariant whole mirrored shortcut
  | .node shortcut children =>
      problem.NodeInvariant whole mirrored shortcut ∧
        ∀ role, problem.Coherent whole (mirrored ++ [role]) (children role)

theorem root_nodeInvariant
    (problem : FiniteLanguageSystem Row Variable Hom)
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (rootCompatible : problem.RootCompatible tree.root) :
    problem.NodeInvariant tree [] tree.root := by
  constructor
  · intro index path membership
    cases path with
    | nil => exact ⟨[], tree, by simp, by simp, membership⟩
    | cons head tail =>
        have atomInUniverse := rootCompatible.1 membership
        have condition := rootCompatible.2 (Atom.var index (head :: tail))
          atomInUniverse
        simp [rootAtomCompatible, membership] at condition
  · intro path membership
    cases path with
    | nil => rfl
    | cons head tail =>
        have atomInUniverse := rootCompatible.1 membership
        have condition := rootCompatible.2 (Atom.constant (head :: tail))
          atomInUniverse
        simp [rootAtomCompatible, membership] at condition

theorem child_nodeInvariant
    (problem : FiniteLanguageSystem Row Variable Hom)
    (whole : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (mirrored : List Hom)
    (parent child : Shortcut (Variable := Variable) (Hom := Hom))
    (parentInvariant : problem.NodeInvariant whole mirrored parent)
    (role : Hom) (resolves : problem.Resolves parent role child)
    (reached : ∃ subtree, whole.descend? (mirrored ++ [role]) = some subtree ∧
      subtree.root = child) :
    problem.NodeInvariant whole (mirrored ++ [role]) child := by
  constructor
  · intro index path membership
    cases path with
    | nil =>
        rcases reached with ⟨subtree, subtreeReached, rootEquality⟩
        exact ⟨mirrored ++ [role], subtree, by simp,
          subtreeReached, by simpa [rootEquality] using membership⟩
    | cons head tail =>
        have inUniverse := resolves.1 membership
        have condition := resolves.2 (Atom.var index (head :: tail)) inUniverse
        simp only [resolveAtom, decide_eq_true_eq] at condition
        have parts : head = role ∧ Atom.var index tail ∈ parent := by
          simpa [resolveAtom] using condition.mp membership
        rcases parentInvariant.1 index tail parts.2 with
          ⟨base, subtree, pathEquality, subtreeReached, barePresent⟩
        refine ⟨base, subtree, ?_, subtreeReached, barePresent⟩
        rw [pathEquality, parts.1, List.reverse_cons, List.append_assoc]
  · intro path membership
    cases path with
    | nil =>
        have inUniverse := resolves.1 membership
        have condition := resolves.2 (Atom.constant []) inUniverse
        simp [resolveAtom, membership] at condition
    | cons head tail =>
        have inUniverse := resolves.1 membership
        have condition := resolves.2 (Atom.constant (head :: tail)) inUniverse
        simp only [resolveAtom, decide_eq_true_eq] at condition
        have parts : head = role ∧ Atom.constant tail ∈ parent := by
          simpa [resolveAtom] using condition.mp membership
        rw [parentInvariant.2 tail parts.2, parts.1, List.reverse_cons]

theorem Derivation.coherentFrom
    (problem : FiniteLanguageSystem Row Variable Hom)
    (whole : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (derived : problem.Derivation tree)
    (mirrored : List Hom)
    (reached : whole.descend? mirrored = some tree)
    (nodeInvariant : problem.NodeInvariant whole mirrored tree.root) :
    problem.Coherent whole mirrored tree := by
  induction derived generalizing mirrored with
  | @leaf shortcut valid terminal => exact nodeInvariant
  | @node shortcut children valid resolves descendants inductionHypothesis =>
      refine ⟨nodeInvariant, ?_⟩
      intro role
      have childReached : whole.descend? (mirrored ++ [role]) =
          some (children role) := by
        rw [Tree.descend?_append, reached]
        simp [Tree.descend?]
      have childInvariant := problem.child_nodeInvariant
        whole mirrored shortcut (children role).root nodeInvariant role
        (resolves role) ⟨children role, childReached, rfl⟩
      exact inductionHypothesis role (mirrored ++ [role]) childReached childInvariant

theorem Derivation.coherent
    (problem : FiniteLanguageSystem Row Variable Hom)
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (derived : problem.Derivation tree)
    (rootCompatible : problem.RootCompatible tree.root) :
    problem.Coherent tree [] tree := by
  apply derived.coherentFrom problem tree [] (by simp)
  exact problem.root_nodeInvariant tree rootCompatible

omit [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom] in
theorem Coherent.nodeInvariant_of_descend
    (problem : FiniteLanguageSystem Row Variable Hom)
    {whole tree subtree :
      Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    {mirrored : List Hom}
    (coherent : problem.Coherent whole mirrored tree)
    (path : List Hom)
    (reached : tree.descend? path = some subtree) :
    problem.NodeInvariant whole (mirrored ++ path) subtree.root := by
  induction path generalizing tree mirrored with
  | nil =>
      simp only [Tree.descend?_nil, Option.some.injEq] at reached
      subst tree
      cases subtree with
      | leaf shortcut =>
          change problem.NodeInvariant whole mirrored shortcut at coherent
          simpa [Tree.root] using coherent
      | node shortcut children =>
          change problem.NodeInvariant whole mirrored shortcut ∧ _ at coherent
          simpa [Tree.root] using coherent.1
  | cons role rest inductionHypothesis =>
      cases tree with
      | leaf shortcut => simp at reached
      | node shortcut children =>
          have childCoherent := coherent.2 role
          have result := inductionHypothesis childCoherent reached
          simpa [List.append_assoc] using result

theorem Derivation.valid
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (derived : problem.Derivation tree) :
    problem.ShortcutValid tree.root := by
  cases derived with
  | leaf valid terminal => exact valid
  | node valid resolves children => exact valid

@[simp]
theorem mem_decode_iff
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (index : Variable) (word : List Hom) :
    word ∈ (decode tree index).paths ↔
      ∃ mirrored subtree,
        tree.descend? mirrored = some subtree ∧
        Atom.var index [] ∈ subtree.root ∧
        mirrored.reverse = word := by
  simp only [decode, Finset.mem_image]
  constructor
  · rintro ⟨mirrored, membership, equality⟩
    rcases (Tree.mem_language_iff_descend
      (fun shortcut : Shortcut (Variable := Variable) (Hom := Hom) =>
        decide (Atom.var index [] ∈ shortcut)) tree mirrored).mp membership with
      ⟨subtree, reached, accepted⟩
    exact ⟨mirrored, subtree, reached, of_decide_eq_true accepted, equality⟩
  · rintro ⟨mirrored, subtree, reached, membership, equality⟩
    refine ⟨mirrored, ?_, equality⟩
    apply (Tree.mem_language_iff_descend
      (fun shortcut : Shortcut (Variable := Variable) (Hom := Hom) =>
        decide (Atom.var index [] ∈ shortcut)) tree mirrored).mpr
    exact ⟨subtree, reached, decide_eq_true membership⟩

omit [FinEnum Row] in
theorem Coherent.atomHolds_of_reached
    (problem : FiniteLanguageSystem Row Variable Hom)
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (coherent : problem.Coherent tree [] tree)
    (mirrored : List Hom)
    {subtree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (reached : tree.descend? mirrored = some subtree)
    {atom : Atom Variable Hom} (membership : atom ∈ subtree.root) :
    AtomHolds (decode tree) mirrored.reverse atom := by
  have invariantWithNil :=
    coherent.nodeInvariant_of_descend problem mirrored reached
  have invariant : problem.NodeInvariant tree mirrored subtree.root := by
    simpa using invariantWithNil
  cases atom with
  | var index path =>
      rcases invariant.1 index path membership with
        ⟨base, baseTree, pathEquality, baseReached, barePresent⟩
      refine ⟨base.reverse, ?_, ?_⟩
      · apply (mem_decode_iff tree index base.reverse).mpr
        exact ⟨base, baseTree, baseReached, barePresent, rfl⟩
      · rw [pathEquality, List.reverse_append]
        simp
  | constant path =>
      have pathEquality := invariant.2 path membership
      rw [pathEquality]
      simp [AtomHolds]

theorem Derivation.reachVarAtom
    (problem : FiniteLanguageSystem Row Variable Hom)
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (derived : problem.Derivation tree)
    (index : Variable) (path word : List Hom)
    (holds : AtomHolds (decode tree) word (Atom.var index path))
    (bounded : path.length ≤ problem.pathBound) :
    ∃ subtree,
      tree.descend? word.reverse = some subtree ∧
      Atom.var index path ∈ subtree.root := by
  rcases holds with ⟨suffix, suffixMembership, equality⟩
  rcases (mem_decode_iff tree index suffix).mp suffixMembership with
    ⟨mirrored, baseTree, baseReached, barePresent, mirroredValue⟩
  have baseDerived := derived.descend problem mirrored baseReached
  rcases baseDerived.extendVar problem index path barePresent bounded with
    ⟨subtree, extension, membership⟩
  refine ⟨subtree, ?_, membership⟩
  have wordPath : word.reverse = mirrored ++ path.reverse := by
    rw [← equality, List.reverse_append, ← mirroredValue]
    simp
  rw [wordPath, Tree.descend?_append, baseReached]
  exact extension

theorem Derivation.reachConstantAtom
    (problem : FiniteLanguageSystem Row Variable Hom)
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (derived : problem.Derivation tree)
    (rootCompatible : problem.RootCompatible tree.root)
    (path word : List Hom)
    (holds : AtomHolds (decode tree) word (Atom.constant path))
    (bounded : path.length ≤ problem.pathBound) :
    ∃ subtree,
      tree.descend? word.reverse = some subtree ∧
      Atom.constant path ∈ subtree.root := by
  have bareInUniverse : Atom.constant [] ∈ problem.atoms :=
    (problem.constant_mem_atoms_iff []).mpr (by simp)
  have barePresent : Atom.constant [] ∈ tree.root := by
    have checked := rootCompatible.2 (Atom.constant []) bareInUniverse
    simpa [rootAtomCompatible] using checked
  rcases derived.extendConstant problem path barePresent bounded with
    ⟨subtree, reached, membership⟩
  subst word
  exact ⟨subtree, reached, membership⟩

theorem ShortcutValid.resolveRow
    (problem : FiniteLanguageSystem Row Variable Hom)
    {shortcut : Shortcut (Variable := Variable) (Hom := Hom)}
    (valid : problem.ShortcutValid shortcut)
    (row : Row) {target : Atom Variable Hom}
    (targetInLeft : target ∈ problem.sideAtoms false row)
    (targetPresent : target ∈ shortcut) :
    ∃ source ∈ problem.sideAtoms true row, source ∈ shortcut := by
  let clause : FlatClause Variable Hom :=
    { sources := problem.sideAtoms true row, target := target }
  have clauseMembership : clause ∈ problem.flatClauses := by
    apply Finset.mem_biUnion.mpr
    refine ⟨row, Finset.mem_univ row, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨target, targetInLeft, rfl⟩
  exact valid.2 clause clauseMembership targetPresent

/-- Every root-compatible FILO derivation decodes to a solution of the
original, unflattened finite-language inequalities. -/
theorem Derivation.decode_isSolution
    (problem : FiniteLanguageSystem Row Variable Hom)
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
    (derived : problem.Derivation tree)
    (rootCompatible : problem.RootCompatible tree.root) :
    problem.IsSolution (decode tree) := by
  have coherent := derived.coherent problem tree rootCompatible
  intro row
  apply (HomContext.le_iff_paths_subset _ _).mpr
  intro word leftMembership
  rcases (problem.mem_evaluate_iff_atom (decode tree) false row word).mp
      leftMembership with ⟨target, targetInLeft, targetHolds⟩
  have targetInUniverse := problem.sideAtoms_subset_atoms false row targetInLeft
  have targetBound : target.path.length ≤ problem.pathBound := by
    cases target with
    | var index path => simpa using (problem.var_mem_atoms_iff index path).mp targetInUniverse
    | constant path => simpa using (problem.constant_mem_atoms_iff path).mp targetInUniverse
  obtain ⟨subtree, reached, targetPresent⟩ :
      ∃ subtree, tree.descend? word.reverse = some subtree ∧
        target ∈ subtree.root := by
    cases target with
    | var index path =>
        exact derived.reachVarAtom problem tree index path word
          targetHolds targetBound
    | constant path =>
        exact derived.reachConstantAtom problem tree rootCompatible path word
          targetHolds targetBound
  have subtreeDerived := derived.descend problem word.reverse reached
  rcases subtreeDerived.valid problem |>.resolveRow problem row targetInLeft
      targetPresent with ⟨source, sourceInRight, sourcePresent⟩
  have sourceHolds : AtomHolds (decode tree) word source := by
    have atMirrored := coherent.atomHolds_of_reached problem tree word.reverse
      reached sourcePresent
    simpa using atMirrored
  exact (problem.mem_evaluate_iff_atom (decode tree) true row word).mpr
    ⟨source, sourceInRight, sourceHolds⟩

end ACUIHE.Solver.Search.FiniteLanguageSystem
