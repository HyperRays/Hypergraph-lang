import ACUIHE.Optimized.FILO

/-! Small executable regression checks for the FILO decision boundary. -/

namespace ACUIHE.Optimized.FILO.Tests

open ACUIHE.Solver.Linear
open ACUIHE.Solver.Search

local instance testBoolFinEnum : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro value; cases value <;> simp)

def identitySystem : FiniteLanguageSystem Unit Unit Unit where
  coefficient _ _ _ := 1
  constant _ _ := 0

def impossibleSystem : FiniteLanguageSystem Unit (Fin 0) Unit where
  coefficient _ _ impossible := Fin.elim0 impossible
  constant side _ := if side then 0 else 1

/-- `{false} ⊆ X`: this forces the search to traverse one actual resolver
edge before it can close the witness. -/
def prefixedSystem : FiniteLanguageSystem Unit Unit Bool where
  coefficient side _ _ := if side then 1 else 0
  constant side _ := if side then 0 else HomContext.singleton [false]

def prefixedImpossibleSystem : FiniteLanguageSystem Unit (Fin 0) Bool where
  coefficient _ _ impossible := Fin.elim0 impossible
  constant side _ := if side then 0 else HomContext.singleton [false]

example : (solveFiniteLanguage? identitySystem).isSome = true := by
  native_decide

example : solveFiniteLanguage? impossibleSystem = none := by
  native_decide

example : (solveFiniteLanguage? prefixedSystem).isSome = true := by
  native_decide

example : solveFiniteLanguage? prefixedImpossibleSystem = none := by
  native_decide

/-- The existing solver is used only as a regression oracle here; it is not
an implementation dependency of the FILO backend. -/
example : (solveFiniteLanguage? identitySystem).isSome =
    identitySystem.solve?.isSome := by
  native_decide

example : (solveFiniteLanguage? impossibleSystem).isSome =
    impossibleSystem.solve?.isSome := by
  native_decide

example : (solveFiniteLanguage? prefixedSystem).isSome =
    prefixedSystem.solve?.isSome := by
  native_decide

example : (solveFiniteLanguage? prefixedImpossibleSystem).isSome =
    prefixedImpossibleSystem.solve?.isSome := by
  native_decide

end ACUIHE.Optimized.FILO.Tests
