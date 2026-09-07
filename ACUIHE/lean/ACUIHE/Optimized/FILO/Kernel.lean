import ACUIHE.Optimized.FILO.Core
import ACUIHE.Solver.Search.Saturation

/-!
# Executable FILO shortcut search

The kernel searches the finite shortcut graph directly.  At a nonterminal
shortcut it resolves one child shortcut independently for every role.  The
height bound is the number of possible shortcuts and is justified below by
the ordinary finite-state productive fixed-point theorem; it is not caller
fuel and cannot weaken completeness.
-/

namespace ACUIHE.Solver.Search.FiniteLanguageSystem

open ACUIHE.Optimized.FILO
open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

universe u

local instance encodableDecidableEq {Alpha : Type*} [Encodable Alpha] :
    DecidableEq Alpha :=
  Encodable.decidableEqOfEncodable Alpha

variable {Row Variable Hom : Type u}
  [FinEnum Row] [FinEnum Variable] [FinEnum Hom] [Encodable Hom]

instance shortcutValidDecidable
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    Decidable (problem.ShortcutValid shortcut) := by
  unfold ShortcutValid
  infer_instance

instance rootCompatibleDecidable
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    Decidable (problem.RootCompatible shortcut) := by
  unfold RootCompatible
  infer_instance

instance resolvesDecidable
    (problem : FiniteLanguageSystem Row Variable Hom)
    (parent child : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) : Decidable (problem.Resolves parent role child) := by
  unfold Resolves
  infer_instance

instance terminalDecidable
    (problem : FiniteLanguageSystem Row Variable Hom)
    (shortcut : Shortcut (Variable := Variable) (Hom := Hom)) :
    Decidable (problem.Terminal shortcut) := by
  unfold Terminal
  infer_instance

/-- A finite derivation certified solely by flat-clause validity and the
exact FILO resolving relation. -/
inductive Derivation (problem : FiniteLanguageSystem Row Variable Hom) :
    Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)) → Prop where
  | leaf {shortcut} :
      problem.ShortcutValid shortcut →
      problem.Terminal shortcut →
      Derivation problem (.leaf shortcut)
  | node {shortcut children} :
      problem.ShortcutValid shortcut →
      (∀ role, problem.Resolves shortcut role (children role).root) →
      (∀ role, Derivation problem (children role)) →
      Derivation problem (.node shortcut children)

/-- Search one role-successor from an explicit candidate list. -/
def buildChild?
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom)))
    (build : Shortcut (Variable := Variable) (Hom := Hom) →
      Option (Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))))
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) :
    Option (Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))) :=
  Automaton.firstResult? (fun child =>
    if problem.Resolves parent role child then build child else none)
    candidates

/-- Construct a derivation of height at most `bound`.  Children are selected
by the FILO resolving relation, not by enumeration of pending automaton
states. -/
def build?
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom))) :
    Nat → Shortcut (Variable := Variable) (Hom := Hom) →
      Option (Tree Hom (Shortcut (Variable := Variable) (Hom := Hom)))
  | 0, shortcut =>
      if problem.ShortcutValid shortcut ∧ problem.Terminal shortcut then
        some (.leaf shortcut)
      else
        none
  | bound + 1, shortcut =>
      if _valid : problem.ShortcutValid shortcut then
        if _terminal : problem.Terminal shortcut then
          some (.leaf shortcut)
        else
          let child? := problem.buildChild? candidates
            (problem.build? candidates bound) shortcut
          if complete : ∀ role, (child? role).isSome then
            some (.node shortcut fun role =>
              (child? role).get (complete role))
          else
            none
      else
        none

theorem build?_root
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom))) :
    ∀ bound shortcut tree,
      problem.build? candidates bound shortcut = some tree →
        tree.root = shortcut := by
  intro bound
  cases bound with
  | zero =>
      intro shortcut tree found
      simp only [build?] at found
      split at found
      next accepted => cases found; rfl
      next rejected => simp at found
  | succ bound =>
      intro shortcut tree found
      simp only [build?] at found
      split at found
      next valid =>
        split at found
        next terminal => cases found; rfl
        next notTerminal =>
          split at found
          next complete => cases found; rfl
          next incomplete => simp at found
      next invalid => simp at found
theorem buildChild?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom)))
    (build : Shortcut (Variable := Variable) (Hom := Hom) →
      Option (Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))))
    (buildSound : ∀ shortcut tree, build shortcut = some tree →
      problem.Derivation tree)
    (buildRoot : ∀ shortcut tree, build shortcut = some tree →
      tree.root = shortcut)
    (parent : Shortcut (Variable := Variable) (Hom := Hom))
    (role : Hom) {tree}
    (found : problem.buildChild? candidates build parent role = some tree) :
    problem.Resolves parent role tree.root ∧ problem.Derivation tree := by
  unfold buildChild? at found
  rcases Automaton.firstResult?_sound _ _ found with ⟨child, _, childFound⟩
  split at childFound
  next resolves =>
    cases built : build child with
    | none => simp [built] at childFound
    | some childTree =>
        simp only [built] at childFound
        have treeEquality : childTree = tree := Option.some.inj childFound
        have derived := buildSound child childTree built
        have rootEquality := buildRoot child childTree built
        subst tree
        exact ⟨rootEquality ▸ resolves, derived⟩
  next doesNotResolve => simp at childFound

theorem build?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    (candidates : List (Shortcut (Variable := Variable) (Hom := Hom))) :
    ∀ bound shortcut tree,
      problem.build? candidates bound shortcut = some tree →
        problem.Derivation tree := by
  intro bound
  induction bound with
  | zero =>
      intro shortcut tree found
      simp only [build?] at found
      split at found
      next accepted =>
        cases found
        exact .leaf accepted.1 accepted.2
      next rejected => simp at found
  | succ bound inductionHypothesis =>
      intro shortcut tree found
      simp only [build?] at found
      split at found
      next valid =>
        split at found
        next terminal =>
          cases found
          exact .leaf valid terminal
        next notTerminal =>
          split at found
          next complete =>
            cases found
            apply Derivation.node valid
            · intro role
              have childFound := Option.some_get (complete role) |>.symm
              exact (problem.buildChild?_sound candidates
                (problem.build? candidates bound)
                (fun child childTree result =>
                  inductionHypothesis child childTree result)
                (fun child childTree result =>
                  problem.build?_root candidates bound child childTree result)
                shortcut role childFound).1
            · intro role
              have childFound := Option.some_get (complete role) |>.symm
              exact (problem.buildChild?_sound candidates
                (problem.build? candidates bound)
                (fun child childTree result =>
                  inductionHypothesis child childTree result)
                (fun child childTree result =>
                  problem.build?_root candidates bound child childTree result)
                shortcut role childFound).2
          next incomplete => simp at found
      next invalid => simp at found

/-- Search root-compatible shortcuts using the input-derived state bound. -/
def buildRoot?
    (problem : FiniteLanguageSystem Row Variable Hom) :
    Option (Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))) :=
  let candidates := problem.shortcutList
  Automaton.firstResult? (fun shortcut =>
    if problem.RootCompatible shortcut then
      problem.build? candidates problem.shortcutList.length shortcut
    else
      none) candidates

theorem buildRoot?_sound
    (problem : FiniteLanguageSystem Row Variable Hom)
    {tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))}
    (found : problem.buildRoot? = some tree) :
    problem.RootCompatible tree.root ∧ problem.Derivation tree := by
  unfold buildRoot? at found
  rcases Automaton.firstResult?_sound _ _ found with
    ⟨shortcut, _, shortcutFound⟩
  split at shortcutFound
  next rootCompatible =>
    cases built : problem.build? problem.shortcutList
        problem.shortcutList.length shortcut with
    | none => simp [built] at shortcutFound
    | some result =>
        simp only [built] at shortcutFound
        have treeEquality : result = tree := Option.some.inj shortcutFound
        have derived := problem.build?_sound problem.shortcutList
          problem.shortcutList.length shortcut result built
        have rootEquality := problem.build?_root problem.shortcutList
          problem.shortcutList.length shortcut result built
        subst tree
        exact ⟨rootEquality ▸ rootCompatible, derived⟩
  next incompatible => simp at shortcutFound

/-- Decode bare-variable membership at tree nodes back to ordinary,
coefficient-first words. -/
def decode
    (tree : Tree Hom (Shortcut (Variable := Variable) (Hom := Hom))) :
    Variable → HomContext Hom :=
  fun index =>
    ⟨(tree.language fun shortcut =>
        decide (Atom.var index [] ∈ shortcut)).image List.reverse⟩

end ACUIHE.Solver.Search.FiniteLanguageSystem
