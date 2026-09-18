import ACUIhE.Equation.Decision

/-!
# Central equation interface

For ACUIhE, ACUIh, and ACUIE, this entry point provides:

* `Term.Equal` and `Term.Below`, their relation laws and certified decisions;
* `Equation` and `Inequality` objects containing unrestricted `left` and `right` terms;
* `Holds` under a particular interpretation, and universally quantified `Valid`;
* `Inequality.toEquation`, preserving both satisfaction and validity.

Raw equality of terms or objects remains Lean's `=`. It is not algebraic
validity. Import `ACUIhE.Solution` additionally for groundness and solvedness.

Foundational definitions live in `Equation.Definition`, below the proof
systems and normalizers, avoiding circular dependencies.
-/
