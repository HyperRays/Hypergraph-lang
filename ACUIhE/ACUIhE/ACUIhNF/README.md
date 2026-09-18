# ACUIh normal forms

Import `ACUIhE.ACUIhNF` (also exported by `ACUIhE`). All declarations live
in `ACUIhE.ACUIh`.

```lean
NF Const Var Hom = Finset (List Hom × Particle Const Var)
```

`Particle.const c` and `Particle.var v` are distinct constructors, even if
the two label types coincide. A word `[h₁, h₂, h₃]` records the term
`h₁(h₂(h₃(p)))`. Words retain both order and repeated labels. The empty set
represents zero; the empty word represents a bare particle.

`Term.normalize` distributes homomorphisms by prefixing their names to every
summand and combines sums by finite-set union. It is executable given
`DecidableEq` instances for `Const`, `Var`, and `Hom`.

`NF.reify` nests each summand's homomorphisms and adds the reconstructed
terms. It is **noncomputable**, because it chooses an enumeration of a
finite set without requiring an ordering on the label types. `NF.reifyList`
is executable when an enumeration is already supplied; its normalization
is exactly the finite set of list members, including when the list contains
duplicates.

`NF.reifyWith normal summands enumerates` is the certified, executable
interface. Its inputs are a normal form, a list of summands, and a proof
`enumerates : summands.toFinset = normal`. Its result has type:

```lean
{term : Term Const Var Hom // term.normalize = normal}
```

The result's `.val` is `NF.reifyList summands`; its `.property` proves that
normalizing that term returns the requested normal form. Any list order
and any multiplicity are accepted, provided the enumeration proof holds.
The interface requires decidable label equality and does not use choice to
obtain the enumeration. The proof is erased during execution.

## Proven guarantees

- `NF.normalize_reifyList`: `(NF.reifyList xs).normalize = xs.toFinset`.
- `NF.reifyList_derives_iff`:
  `Derives (NF.reifyList xs) t ↔ xs.toFinset = t.normalize`.
- `NF.reifyList_semanticallyEquivalent_iff`: the same characterization for
  equality in all ACUIh algebras.
- `NF.reifyList_congr_iff`: two lists reify to derivably equal terms exactly
  when their finite sets of members agree.
- `NF.reifyWith_derives_iff`: the certified output represents exactly the
  terms with the requested normal form.
- `NF.eval_reifyList` and `NF.eval_reifyWith`: list-based and certified
  reification preserve interpretation in every ACUIh algebra.
- `NF.normalize_reify`: `normal.reify.normalize = normal`.
- `NF.reify_normalize`: `Derives term.normalize.reify term`.
- `NF.normalize_eq_iff_derives`: normal-form equality is equivalent to
  derivability from the ACUIh axioms.
- `NF.normalize_eq_iff_semanticallyEquivalent`: normal-form equality is
  equivalent to equality in every ACUIh algebra.
- `Term.eval_normalize` and `NF.eval_reify`: both operations preserve
  interpretation in ACUIh algebras of any carrier universe.
- `NF.separates`: different normal forms give different evaluations in the
  concrete normal-form model.
- `decidableDerives`: computing and comparing normal forms decides
  fragment derivability.

`NF.algebra` supplies the concrete model with union, the empty set, and
word prefixing. It is an explicit instance value to install locally, so
importing this module does not change the arithmetic instances for finsets.
`Term.eval_normalForm` identifies evaluation in this model with normalization.

## Linear structure

The [linear development](linear/README.md) supplies a semiring of finite
homomorphism-word sets and a semimodule structure on normal forms. It proves
that scalar action agrees with homomorphism prefixing, normalization, and
evaluation in every ACUIh algebra. It is exported by the same import.

## Files

- `Theory.lean`: fragment derivations, their soundness, and the quotient
  term model proving semantic completeness.
- `Definition.lean`: particles, summands, normal forms, normalization,
  reification (including the certified enumeration interface), the concrete
  model, and the exact normal-form round trip.
- `Soundness.lean`: interpretation of normal forms and soundness of equality
  decided by normalization.
- `Completeness.lean`: the converse, correctness of arbitrary and certified
  enumerations, the term round trip, semantic characterization, and the
  decision procedure.

Build the library with:

```sh
lake build ACUIhE
```
