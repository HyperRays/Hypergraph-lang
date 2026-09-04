import ACUIHE.Optimized.Shortcut.E

/-!
Public import for the separate shortcut-saturation ACUIhE solver.

The entry point is
`ACUIHE.Optimized.Shortcut.solveACUIhE?`.  Unlike the older
search entry points it takes no depth parameter: it constructs the reachable
closure and performs witness-carrying bottom-up saturation for the proved
finite cardinality bound.
-/
