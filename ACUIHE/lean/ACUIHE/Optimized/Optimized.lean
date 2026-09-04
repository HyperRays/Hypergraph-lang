import ACUIHE.Optimized.Optimized.E

/-!
Public import for the separate reachable-state ACUIhE solver.

The existing `ACUIHE.Solver.Search.solveACUIhE?` remains unchanged.  The new
entry point is `ACUIHE.Optimized.Optimized.solveACUIhE?` and accepts an
optional shallow-search bound, defaulting to eight.
-/
