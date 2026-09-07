# Optimized FILO backend

This directory contains a separate exact solver for the finite-language
(`ACUIh`) part of the project. It does not call the original pending-state
solver or either optimized solver.

The kernel uses a finite flat presentation. An atom `(X, p)` denotes the
language `p · X`, and a constant atom `p` denotes the singleton language
`{p}`. The atom universe contains every variable paired with every word up to
the largest input coefficient, plus the corresponding constant atoms. It is
therefore finite and closed under taking coefficient tails.

A shortcut is a set of atoms satisfying all flattened anti-Horn clauses. If
`S₂` resolves `S₁` with respect to a homomorphism `r`, then membership is
exact:

```text
(X, r :: p) ∈ S₂  ↔  (X, p) ∈ S₁
```

and likewise for constant atoms. Bare variables in `S₂` are free membership
choices for the newly reached word. Root compatibility fixes constants and
rules out nonempty prefixes at the empty word; terminal shortcuts are exactly
those whose omitted children can all be empty.

`Saturation.lean` is the production search. It constructs height-zero
shortcuts and then grows bottom-up layers, resolving new shortcuts only from
the preceding table. Stored derivation trees make dependencies acyclic. The
implementation stops at the first closed fixed point instead of blindly
executing the entire cardinality bound, caches the candidate universe, and
constructs the complete `2 ^ |Variable|` family of resolving children
directly rather than scanning every known shortcut. These optimizations are
proved extensionally equivalent to the simple bounded saturation.

`Completeness.lean` proves that the number of explicit shortcuts is a complete
internal height bound via a finite productive-state argument; it is not
caller-selected fuel. `Soundness.lean` proves an exact path invariant and
reconstructs finite languages from bare-variable membership. Together they
establish:

```lean
solveFiniteLanguage?_sound
solveFiniteLanguage?_complete
solveFiniteLanguage?_eq_none_iff
```

No `sorry`, `admit`, extra axiom, or unchecked witness generator is used.

The column adapter compares finite-language systems extensionally and caches
both positive and negative exact results across basis columns and across `E`
configurations. Cache lookup and the cached ACUIhE search are proved equal to
fresh solving and to the uncached complete solver respectively. The `E`
wrapper still uses the existing exhaustive `EConfiguration` enumeration and
checked reconstruction; the cache removes repeated ACUIh work without
changing that search space.
