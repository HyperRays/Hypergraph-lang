import ACUIhE.ACUIESolver.Solver

/-!
# Complete verified ACUIE unifiability solver

`ACUIESolver.solve` returns an ordinary unifier or proved unsatisfiability,
with soundness, completeness, and termination. It searches canonical ordered
E-groups, prunes partial matchings by proved necessary Horn constraints, stops
propagation at its first fixed point, and reconstructs a substitution with
cached dependencies. There is no row enumeration, fallback, or runtime
validation of a returned substitution. The
ordered-group completeness is derived from arbitrary unifiers using canonical
graphs. Numeric ranks are determined by groups, not enumerated.

`Problem.Unifiable` retains its original semantic definition and now has a
computable `Decidable` instance. The original `prototype`, `step`, and `search`
APIs remain available; `preview` names the former residual-returning solver.
-/
