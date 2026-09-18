# Linear structure of ACUIh normal forms

Import `ACUIhE.ACUIhNF.linear`, also exported by `ACUIhE.ACUIhNF` and
`ACUIhE`. Declarations live in `ACUIhE.ACUIh.Linear`.

## Coefficient semiring

`WordPolynomial Hom` wraps a `Finset (List Hom)` in its `.words` field.
It has a standard `Semiring` instance whenever homomorphism names have
decidable equality.

| Operation | Word-set interpretation |
| --- | --- |
| `0` | The empty set |
| `1` | `{[]}`, containing the empty word |
| `p + q` | `p.words ∪ q.words` |
| `p * q` | All `u ++ v` with `u ∈ p.words` and `v ∈ q.words` |
| `WordPolynomial.monomial w` | `{w}` |
| `WordPolynomial.generator h` | `{[h]}` |

All semiring laws are proved in `Semiring.lean`. Addition is idempotent
(`WordPolynomial.add_self`). Multiplication preserves the order and
multiplicity of homomorphism names within each word. The general theorem
`WordPolynomial.generators_not_commute` proves that distinct names give
noncommuting generators.

## Semimodule of normal forms

The explicit function `act p n` is the finite set

```text
{ (u ++ v, particle) | u ∈ p.words, (v, particle) ∈ n }.
```

Its properties are proved as `act_one`, `act_zero`, `act_empty`, `act_add`,
`act_union`, and `act_mul`. Addition of normal forms is union and zero is
the empty set. These proofs supply the standard mathlib `Module` structure
over `WordPolynomial Hom`; over a semiring this means a semimodule.

Because `NF` is an abbreviation for a finset, its arithmetic structures are
explicit values rather than global instances. Within a section with
`Const`, `Var`, and `Hom` and their `DecidableEq` instances, enable them with:

```lean
open ACUIhE.ACUIh ACUIhE.ACUIh.Linear

local instance : AddCommMonoid (NF Const Var Hom) :=
  normalFormAddCommMonoid

local instance : Module (WordPolynomial Hom) (NF Const Var Hom) :=
  normalFormModule
```

Then `p • n` is `act p n`, and standard laws such as `one_smul`,
`mul_smul`, `add_smul`, and `smul_add` are available. Without installing
these instances, `act` and its explicit laws remain directly usable.

## Connection to the fragment

- `act_generator`: the action of `{[h]}` is exactly `NF.prepend h`.
- `normalize_reifyWord`: applying a word to a raw term and normalizing
  agrees with the action of that word's monomial on the term's normal form.
- `evalWord_append`: word concatenation is interpreted as composition,
  with the left word outermost.
- `eval_act`: interpreting `act p n` equals applying the interpreted
  coefficient to the interpretation of `n`, in every ACUIh algebra.
- `eval_act_normalize`: the same compatibility starting from a raw term.
- `WordPolynomial.eval_mul` and `WordPolynomial.eval_add`: multiplication
  and addition of coefficients are interpreted as composition and pointwise
  ACUI addition, respectively.

The definitions and instances are computable with decidable equality of
the relevant labels. They do not choose any enumeration of a finite set.
They add no multiplication of particles or of arbitrary normal forms:
coefficients multiply each other and act on normal forms.

## Constant-coordinate matrices

`Matrix.lean` represents ground substitutions using:

```text
Row Const Hom := Const →₀ WordPolynomial Hom
GroundMatrix Const Var Hom := Var → Row Const Hom
```

Constants index columns, variables index rows, and entries are word-set
coefficients. An unknown matrix describes the ground values to be assigned
to variables; variables do not introduce extra columns. Each row has finite
support, but neither the constant type nor the variable type needs to be
finite. Constants appearing in substitutions need not appear in the original
expression, as long as they belong to `Const`.

`Row.basis a` is the row with `1` in column `a` and `0` elsewhere.
`Row.ofNF` and `Row.toNF` convert between rows and ground normal forms
`NF Const Empty Hom`. Both round trips are proved, and `Row.groundEquiv`
packages the lossless equivalence. `Row.ofNF_union` and `Row.ofNF_act`
prove that it preserves addition and the left coefficient action.

For a term `t` and matrix `M`:

- `variableRow t` contains the coefficients of its variables.
- `constantRow t` contains its constant offset.
- `matrixCoordinates M t` computes `variableRow t · M + constantRow t`.
- `instantiateNF M t` substitutes the matrix rows directly in normal forms.
- `ofNF_instantiateNF` proves that these two descriptions agree exactly.
- `toNF_matrixCoordinates` reconstructs the entire instantiated normal form
  from the matrix result.

For example, for `h₁(X) + h₂(Y) + a + b`, with distinct row names `X, Y`
and distinct columns `a, b`, the displayed matrix expression is

```text
(h₁ h₂) · [[X_a, X_b], [Y_a, Y_b]] + (1 0) + (0 1)
```

Its `a` coordinate is `h₁ * X_a + h₂ * Y_a + 1`, and its `b`
coordinate is `h₁ * X_b + h₂ * Y_b + 1`. These are all the columns
when the allowed constant type contains only `a, b`; otherwise this is
the projection onto those columns. Multiplication order is preserved:
the expression's coefficient acts on the left, as the outer homomorphism.

`rowVecMul` sums only over the coefficient row's finite support.
`rowVecMul_eq_vecMul` and `matrixCoordinates_eq_vecMul` connect it to
mathlib's standard `Matrix.vecMul` when the variable type is finite.
`rowVecMul_eq_support_vecMul` and `matrixCoordinates_eq_support_vecMul`
give an ordinary finite-row matrix product over just the support without
that assumption. `GroundMatrix.asMatrix`
exposes the ordinary matrix view without dropping any entries.

The computational definitions use explicit finite supports, including
computable `Row.add` and `Row.scale`. Their agreement with standard Finsupp
addition and scalar multiplication is proved by `Row.add_eq` and
`Row.scale_eq`. No new noncomputable definitions or label orders are needed.

### Equality, inequalities, and solvedness

`GroundMatrix.ofSubstitution` builds a matrix from a raw ground substitution
`Var → Term Const Empty Hom`. The main correctness results are:

- `normalize_substituteGround`: matrix instantiation agrees with normalization
  after raw-term substitution.
- `derives_substituteGround_iff`: equality after substitution is equivalent
  to equality of the resulting coordinate rows.
- `derives_add_substituteGround_iff`: additive inequality after substitution
  is equivalent to word-set inclusion at every constant coordinate.
- `solved_substituteGround_iff` and `solvedBelow_substituteGround_iff`: the
  same criteria characterize the ACUIh predicates from `Solution.lean`,
  including their requirement that both sides be ground.

These results certify the matrix representation for ACUIh. They do not
introduce an algorithm for finding an unknown substitution, and do not
extend the representation to expressions containing `E`.

## Files

- `Semiring.lean`: the coefficient type, semiring instance, and word laws.
- `Semimodule.lean`: scalar action, semimodule instance, and compatibility
  with homomorphism prefixing and normalization.
- `Semantics.lean`: interpretation of words and coefficients, and
  compatibility with evaluation in arbitrary ACUIh algebras.
- `Matrix.lean`: constant-coordinate rows, substitution matrices, and their
  equivalence with ground normal forms, equality, and inequalities.

Verify the development with `lake build ACUIhE`.
