import ACUIHE.Solver.Search.Optimized.E
import ACUIHE.Solver.Search.Optimized.Shortcut

/-!
Public import for the separate reachable-state ACUIhE solver.

The existing `ACUIHE.Solver.Search.solveACUIhE?` remains unchanged.  The new
entry point is `ACUIHE.Solver.Search.Optimized.solveACUIhE?` and accepts an
optional shallow-search bound, defaulting to eight.

The independent paper-inspired shortcut backend is available as
`ACUIHE.Solver.Search.Optimized.Shortcut.solveACUIhE?`; it carries witnesses
inside its saturation table and therefore needs no shallow-search bound.
-/
