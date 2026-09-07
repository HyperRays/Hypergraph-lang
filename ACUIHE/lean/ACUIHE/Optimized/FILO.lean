import ACUIHE.Optimized.FILO.E

/-!
# Exact FILO backend

Public entry points:

* `ACUIHE.Optimized.FILO.solveFiniteLanguage?`
* `ACUIHE.Optimized.FILO.solveColumn?`
* `ACUIHE.Optimized.FILO.solveColumnFamily?`
* `ACUIHE.Optimized.FILO.solveEConfiguration?`
* `ACUIHE.Optimized.FILO.solveACUIhE?`

Each solver has soundness, completeness, and exact-failure theorems where
appropriate.  The finite-language kernel is independent of the original and
optimized pending-state solvers.  The outer `E` certificate enumeration is
intentionally unchanged pending a separate algorithmic redesign.
-/
