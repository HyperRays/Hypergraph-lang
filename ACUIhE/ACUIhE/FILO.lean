import ACUIhE.FILO.Solver
import ACUIhE.FILO.Coordinates

/-!
# Verified FILO algorithm for ACUIh unification

The algorithmic pipeline of arXiv:2502.14130 is proved against the existing
matrix semantics: preprocessing, propagated choice domains and lexicographic
choice search, the implicit solver, direct start reconstruction, and the
shortcut loop with stored resolvers, good variables, and early stopping.

`FILO.solve` returns a plain ground matrix or failure. `FILO.solve_sound` and
`FILO.solve_none_iff` cover both outcomes for the original problem.
`FILO.Coordinates.solve` uses the same column solver when entire prescribed
coordinates must be absent; its soundness and completeness are proved separately.
-/
