import ACUIhE.Solver.Decision

/-!
# Verified mixed ACUIhE solver

`Solver.solve` uses ACUIESolver's shared E conditions, ordered-group traversal,
and cached reconstruction, with FILO solving the coupled word-valued layers.
`solve_sound` proves success for the original full equations. `solve_none_iff`
proves failure equivalent to the absence of an ordinary unifier, and
`solve_complete_of_unifier` also accepts arbitrary target-variable types.

`Solver.isUnifiable` skips graph reconstruction. No public operation takes a
proof argument, a correctness assumption, a depth bound, or a fallback solver.
The executable path does not validate a candidate substitution afterward.
-/
