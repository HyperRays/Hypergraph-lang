import HMEmbedding.Solver

set_option autoImplicit false

namespace HMEmbedding.Examples
open ACUIhE

abbrev int : Mono Nat := .base 0
abbrev string : Mono Nat := .base 1
abbrev fn (a b : Mono Nat) := Mono.op .fn a b
abbrev pair (a b : Mono Nat) := Mono.op .pair a b

def idScheme : Scheme source := ⟨{0}, fn (.var 0) (.var 0)⟩

theorem id_typed : Typing source [] (.lam (.var 0)) idScheme := by
  have body : Typing source [] (.lam (.var 0)) (.mono (fn (.var 0) (.var 0))) :=
    Typing.lam (Typing.var rfl)
  have generalized := Typing.gen (v := 0) body (by simp [environmentFV])
  simpa [Scheme.all, Scheme.mono, idScheme] using generalized

theorem id_instance (t : Mono Nat) : Instance idScheme (.mono (fn t t)) := by
  refine ⟨fun _ => t, ?_, ?_⟩
  · simp [idScheme, Scheme.instantiate, Scheme.mono, Mono.subst]
  · exact Finset.disjoint_empty_left _

-- literal 0 and literal 1 stand for values of Int and String respectively.
def mixedId : Expr := .letE (.lam (.var 0))
  (.pair (.app (.var 0) (.literal 0)) (.app (.var 0) (.literal 1)))

/-- Full derivation: let id = fun x -> x in (id 1, id "one"). -/
theorem mixed_id_typed : Typing source [] mixedId (.mono (pair int string)) := by
  apply Typing.letE (s := idScheme) id_typed
  apply Typing.pair
  · exact Typing.app (Typing.inst (Typing.var rfl) (id_instance int)) Typing.literal
  · exact Typing.app (Typing.inst (Typing.var rfl) (id_instance string)) Typing.literal

theorem mixed_id_embedded :
    Typing target [] mixedId (encoding.scheme (.mono (pair int string))) :=
  (full_hm_embedding [] mixedId _).mp mixed_id_typed

/-- The parameter can itself be a function type: let id = ... in id id. -/
theorem higher_order_id : Typing source []
    (.letE (.lam (.var 0)) (.app (.var 0) (.var 0))) (.mono (fn int int)) := by
  apply Typing.letE (s := idScheme) id_typed
  exact Typing.app
    (Typing.inst (Typing.var rfl) (id_instance (fn int int)))
    (Typing.inst (Typing.var rfl) (id_instance int))

def renamedId : Scheme source := ⟨{7}, fn (.var 7) (.var 7)⟩

/-- Bound names can be renamed in both directions by ordinary generic instantiation. -/
theorem id_alpha_renaming : Instance idScheme renamedId ∧ Instance renamedId idScheme := by
  constructor
  · refine ⟨fun _ => .var 7, ?_, ?_⟩ <;>
      simp [idScheme, renamedId, Scheme.instantiate, Scheme.fv, Mono.subst, Mono.fv]
  · refine ⟨fun _ => .var 0, ?_, ?_⟩ <;>
      simp [idScheme, renamedId, Scheme.instantiate, Scheme.fv, Mono.subst, Mono.fv]

-- forall a. a -> b, where b is the type of a captured value.
def captured : Scheme source := ⟨{0}, fn (.var 0) (.var 1)⟩
def capturedIncorrectly : Scheme source := ⟨{1}, fn (.var 1) (.var 1)⟩

theorem capture_rejected : ¬ Instance captured capturedIncorrectly := by
  rintro ⟨_, _, fresh⟩
  simp [captured, capturedIncorrectly, Scheme.fv, Mono.fv] at fresh

theorem captured_variable_not_generalizable :
    1 ∈ environmentFV [Scheme.mono (M := source) (.var 1)] := by
  simp [environmentFV, Scheme.fv, Scheme.mono, Mono.fv]

/-- Lambda-bound f retains one monotype: its parameter cannot become both bases. -/
def sharedParameter : Constraints := [(.var 0, int), (.var 0, string)]

theorem shared_parameter_rejected : ¬ HMUnifiable sharedParameter := by
  rintro ⟨s, hs⟩
  have hi := hs (.var 0, int) (by simp [sharedParameter])
  have ht := hs (.var 0, string) (by simp [sharedParameter])
  simp only [Mono.subst] at hi ht
  have impossible := hi.symm.trans ht
  cases impossible

def occurs : Constraints := [(.var 0, fn (.var 0) (.var 1))]

/-- Finite HM types reject X = O_arrow(X,Y); no solver-specific occurs axiom. -/
theorem occurs_rejected : ¬ HMUnifiable occurs := by
  rintro ⟨s, hs⟩
  have eq := hs (.var 0, fn (.var 0) (.var 1)) (by simp [occurs])
  change s 0 = fn (s 0) (s 1) at eq
  have sizes := congrArg sizeOf eq
  simp only [Mono.op.sizeOf_spec] at sizes
  omega

def independentUses : Constraints :=
  [(fn (.var 0) (.var 0), fn int (.var 2)),
   (fn (.var 1) (.var 1), fn string (.var 3))]

#guard Solver.isUnifiable (encodeConstraints independentUses)
#guard !(Solver.isUnifiable (encodeConstraints sharedParameter))
#guard !(Solver.isUnifiable (encodeConstraints occurs))

-- Inspect the actual reconstructed result, not just the decision bit.
#guard match Solver.solve (encodeConstraints independentUses) with
  | none => false
  | some s => decide (s 2 = Graph.constant (.base 0)) &&
      decide (s 3 = Graph.constant (.base 1))

end HMEmbedding.Examples
