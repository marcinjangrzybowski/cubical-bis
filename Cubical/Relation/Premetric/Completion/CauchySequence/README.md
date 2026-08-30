# Cauchy-sequence completion

This directory implements a completion of a premetric space by a higher
inductive-inductive type whose limit constructor accepts natural-numbered
Cauchy sequences.

The defining Cauchy condition is

```agda
IsCauchySequence x =
  ∀ ε → ∥ Σ[ N ∈ ℕ ]
    (∀ m n → N ≤ m → N ≤ n → x m ≈ᶜ[ ε ] x n) ∥₁
```

The tail index and its proof are propositionally truncated separately for
each positive rational radius.  In particular, the datum contains no chosen
simultaneous modulus `ℚ₊ → ℕ`.  This radiuswise placement of truncation is
the construction's characteristic feature; the names and module boundaries
below are organized around it rather than around earlier completion
experiments.

## Core modules

- `Base` defines `Completion`, the injection `ι`, sequential limits `lim`,
  completed approximation `_≈ᶜ[_]_`, and the primitive elimination rule for
  proposition-valued predicates.  It also proves that the carrier is a set
  and that completed approximation is proposition-valued, reflexive,
  symmetric, and monotone in its radius.
- `Elimination` collects the dependent and non-dependent recursors needed
  when a definition must follow both the completion and approximation
  constructors.  `ElimIsCauchySequence` is the decorated form of the same
  radiuswise Cauchy datum.
- `Approximation` derives roundedness, density of the base injection, the
  triangle law, reflection of approximation along `ι`, and injectivity of
  `ι`.  Its decorated upper-cut relation `_≈ᴰ[_]_` is an internal semantic
  presentation proved equivalent to `_≈ᶜ[_]_`; it is used to derive the
  triangle law rather than added as a constructor.
- `Premetric` packages these results as `CompletionPremetricSpace`.  The
  constructor `lim` is a limit of its input sequence,
  `hasCauchySequenceLimitsCompletion` packages its radiuswise sequential
  completeness, and dyadic sampling proves completeness in the library's
  ordinary `PremetricTheory` sense.
- `Limits` states the construction's natural codomain interface for an
  arbitrary premetric space, `HasCauchySequenceLimits`, and proves that this
  structure is proposition-valued.

The root module `Cubical.Relation.Premetric.Completion.CauchySequence`
exports `Base` and `Premetric`, with the technical interfaces available as
the submodules `Approximation`, `Elimination`, and `SequenceLimits`.

## Extension principles

`Extension` groups five complementary ways to extend maps:

- `NonExpanding` extends a nonexpanding base map into another
  Cauchy-sequence completion and proves uniqueness from density.
- `Lipschitz` does the same for a specified positive rational Lipschitz
  constant.
- `UniversalProperty` extends a nonexpanding base map into any separated,
  rounded premetric space equipped with `HasCauchySequenceLimits`.  It proves
  uniqueness and packages extension/restriction as the equivalence
  `NE[ M , N ] ≃ NE[ Completion M , N ]`.
- `CauchyGraph` extends a base function whose approximate graph preserves
  Cauchy sequences.  The binary module treats two domains directly, without
  routing through a product completion, and exposes computation rules for
  `ι`/`ι`, `ι`/`lim`, `lim`/`ι`, and synchronized `lim`/`lim`.
- `CompletionCentered` asks, separately and merely for every completed
  center and output radius, for a source radius on which values of the base
  map are close.  This condition directly implies the `CauchyGraph`
  hypothesis and therefore has a canonical continuous extension.  For every
  base map it is equivalent to the proposition of admitting a continuous
  extension, and globally completion-centered restrictions are equivalent
  to continuous maps between the completions.

The construction-independent formulations live in
`Completion.UniversalProperty`.  The `UniversalProperties` submodule of
`Extension` supplies the `CauchySequence` presentation.  Its `NonExpanding`
module initializes the ordinary universal property for a radiuswise-complete
target; its `CompletionCenteredProperty` and
`CompletionCenteredMappingSpace` modules initialize the separate continuous
extension classification.

The `HasCauchySequenceLimits` hypothesis is deliberately stronger than the
ordinary completeness interface.  A radiuswise-truncated tail witness does
not constructively supply the single global modulus expected by the usual
`ℚ₊`-indexed completion machinery.

## Rational specialization

`Reals` specializes the construction to the rational premetric and defines
`ℝ`.  It proves rational density and injectivity of `ιℚ`, and supplies both
ordinary completeness and Cauchy-sequence limits.

`Reals.Algebra` is split by mathematical structure:

- `Additive`, `Scalar`, and `Multiplicative` construct the ring operations
  and their laws;
- `Lattice` constructs min, max, and absolute value;
- `Order` develops non-strict order, the positive-gap strict order,
  locatedness, rational density, apartness, order compatibility, and
  Archimedean bounds;
- `Metric` relates order, absolute difference, completed approximation, and
  equality;
- `Inverse` constructs bounded reciprocals by the native Lipschitz lift,
  glues them over positive gaps, and supplies positive and signed reciprocal
  laws (with signed division defined on apart-from-zero inputs);
- `Powers` and `Polynomial` supply natural powers, their order and absolute
  value laws, rational compatibility, and finite Horner evaluation;
- `Structure` packages the additive group, rational module, commutative
  ring, and ordered commutative ring instances.

`Reals.Extensionality` proves that pointwise-continuous maps out of these
reals are determined by their rational values.  The bounded reciprocal uses
that principle only for lower-bound independence and nonnegativity.  Its
inverse law itself is proved directly by the completion eliminator and the
synchronized `lim` computation rules for clamp, reciprocal, and
multiplication.

`Reals.Analysis` begins the analysis API with sequences.  It proves that the
native radiuswise Cauchy condition is equivalent to possessing a unique
sequential limit, develops preservation of Cauchy sequences and limits by
continuous maps, the basic real operations, powers, and polynomials, and
proves that eventual order is closed under limits.  Its series layer includes
finite sums, native Cauchy-series completeness, finite modifications,
absolute-series bounds, and geometric series, including convergence for
rational ratios of absolute value below one.  Its initial power-series layer
covers linear operations, the unit geometric series, polynomial coefficient
sequences, and finite coefficient modifications.  Eventual equality,
eventual order, and unknown finite-tail cutoffs remain propositionally
truncated when their consumers only need a proposition; exact
cutoff-dependent sum formulas retain the witness under truncation instead of
silently choosing it.  See `Reals/Analysis/README.md` for the design boundary
and roadmap.

`Reals.Comparison.Regular` gives the canonical map from the regular Cauchy
reals (`CauchyRealsP`) into this real type.  The accompanying comparison
modules prove preservation of the developed algebraic, lattice, order, and
distance structure.  No unconditional reverse map or equivalence is claimed.
`Reals.Comparison.Regular.StructuredInverse` proves that equipping this
canonical map with an inverse that sends radiuswise Cauchy sequences to
bundled sequential witnesses is equivalent to `SequentialTailChoice`.

The generic relationship with `Completion.Base` is isolated in the sibling
module `Cubical.Relation.Premetric.Completion.Comparison`.  It factors the
comparison through the chosen-modulus sequential completion, identifies the
exact missing Π/truncation commute as `SequentialTailChoice`, and proves that
this hypothesis yields an isometric equivalence.  It also shows formally that
the library's propositional axiom of choice over positive rationals supplies
the hypothesis; the axiom is parameterized, never assumed.

## Deliberate scope

This implementation retains results that describe the construction itself
or are used by its rational algebra.  The recovered completion-centered
condition is the radiuswise formulation intrinsic to this completion; the
older formulation that placed an entire modulus under one truncation remains
historical.  Speculative reverse comparisons, duplicate strict orders, and
separator encodings are not part of the standalone API.
