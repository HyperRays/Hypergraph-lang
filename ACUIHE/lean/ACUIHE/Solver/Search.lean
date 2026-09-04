import ACUIHE.Solver.Search.Tree
import ACUIHE.Solver.Search.Automaton
import ACUIHE.Solver.Search.Saturation
import ACUIHE.Solver.Search.Words
import ACUIHE.Solver.Search.ColumnAutomaton
import ACUIHE.Solver.Search.Matrix
import ACUIHE.Solver.Search.E.Completeness

/-!
Exact exhaustive search for linear ACUIh matrix inequalities.

The public search functions take no caller-selected search cutoff.  Their
internal tree-height bound is the cardinality of the finite residual-state
space, and saturation proves that failure at that bound is equivalent to
unrestricted unsatisfiability.

`E.Body` discovers `E` bodies directly in intrinsic normal forms.
`E.Combination` purifies those bodies into finite alien constants and builds
the equality-class/rank certificate searched by backtracking. `E.Projection`
maps every genuine solution into such a certificate; `E.Reconstruction` maps
every accepted certificate back to an original solution. `E.Completeness` is
the compatibility import exposing both proof directions.
-/
