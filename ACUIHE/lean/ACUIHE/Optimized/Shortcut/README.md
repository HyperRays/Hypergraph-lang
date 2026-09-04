# Witness-carrying shortcut backend

This directory is a separate, exact solver backend inspired by the shortcut
and resolving relation in *FILO — automated unification in FL0*.

The adaptation deliberately reuses the repository's proved finite-language
tree-automaton encoding.  A `Shortcut.Entry` records:

- the canonical numeric identifier of a pending automaton state;
- the state itself, for the proof invariant; and
- an accepted subtree witnessing that the state is productive.

One `grow` round resolves an entry only from entries in the preceding table.
Consequently its witness dependencies are acyclic.  Terminal transitions
make leaf entries; nonterminal transitions make an entry only when every
successor already has a witness.  `TableValid`, `resolve?_sound`, and
`productiveSteps_lookup` connect this executable construction to the existing
automaton semantics.

There are three performance safeguards:

1. candidates are taken only from the reachable closure and sorted by their
   numeric identifiers; the full function-valued state universe is never
   enumerated by the shortcut pass;
2. a shallow prepass handles common small witnesses, but failure always falls
   through to exact saturation; and
3. the productive fixed point rejects impossible problems before witness
   construction, while successful witness construction stops as soon as the
   initial state is resolved.

The outer `E` certificate enumeration and independently checked
reconstruction are retained, because FILO's FL0 procedure does not itself
cover the `E` operator.  Column results remain memoized within each
configuration.

Public entry point:

```lean
ACUIHE.Optimized.Shortcut.solveACUIhE? left right
```

It has no caller-selected depth/fuel argument.  The finite cardinality bounds
inside the implementation are termination bounds used in the completeness
proofs, not weakening cutoffs.
