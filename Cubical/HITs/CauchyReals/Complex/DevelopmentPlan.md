# Further development of constructive complex analysis

This is the living plan for extending
`Cubical.HITs.CauchyReals.Complex.*`.  The existing implementation provides
the pointwise algebraic and metric foundations; the next goal is reusable
closure machinery for limits, series, derivatives, and integration.

The stable full entry point remains:

```agda
open import Cubical.HITs.CauchyReals.Complex
```

All development remains constructive.  In particular:

- division and inversion retain explicit apartness witnesses;
- no classical field structure is inferred from mere inequality;
- arguments and logarithms are defined only with branch data;
- no postulates, unsafe pragmas, or weakened options are introduced;
- existing public names remain available through their current entry points.

## Baseline

At commit `1313467ce8a159cd5786676e432415e936c46e88`, the complex development
contains 58 Agda modules and about 3,953 lines.  All modules typecheck without
holes or postulates.

The current layers provide:

- a commutative ring, conjugation, squared norm, modulus, and apartness-aware
  inversion;
- the canonical modulus premetric and coordinatewise completeness;
- unit-circle and polar equivalences;
- Cauchy complex sequences, limits, finite sums, and power-series syntax;
- a punctured-neighbourhood derivative with affine and square examples;
- complex exponential, sine, cosine, and explicit roots of unity.

The main missing layer at the baseline was closure theory: complex operations
were not systematically known to preserve convergence, general derivative
rules were absent, and the series API had no absolute- or
geometric-convergence theorem.  The current slice supplies the first metric,
sequence, and series closure results together with domain-aware additive,
fixed-scalar, product, conditional chain, inverse, and quotient rules.
Extending composition beyond apart-increment-preserving inner maps and
deriving continuity/local boundedness systematically remain the next broad
calculus gaps.

## Phase 0: architecture and performance

Status: planned.

- [ ] Add a lightweight `Complex.Core` entry point while retaining the full
      `Complex` umbrella.
- [ ] Split `Transcendental.Trigonometric` into definitions, ring identities,
      elementary laws, and real-axis compatibility, leaving the current module
      as a public aggregator.
- [ ] Split `Polar` into scaling, unit direction, reconstruction, and
      equivalence modules, leaving the current module as a public aggregator.
- [ ] Prefer restricted imports and semantic leaf modules for subsequent work.

The coherent benchmark from 2026-07-23 gives a median of about 39 seconds and
2.6 GiB peak RSS for `Transcendental.Trigonometric`, and about 22 seconds and
1.8 GiB for `Polar`.  These are the first candidates for performance-neutral
semantic splitting.

## Phase 1: algebra, metric operations, and domains

Status: in progress.

### Algebraic packaging

- [ ] Add `Complex.Algebra.Coordinates` with coordinate laws, Cartesian
      decomposition, and injectivity of the real embedding.
- [ ] Add `Complex.Units`, re-exporting `ℂˣ` and packaging its abelian-group
      structure.
- [ ] Complete the structural apartness API: irreflexivity, cotransitivity,
      compatibility with addition and multiplication, and cancellation.
- [x] Prove that the modulus of a witnessed complex inverse is the witnessed
      real inverse of the modulus.
- [ ] Add the remaining inverse laws for conjugation, products, and division.

### Metric operations

- [x] Prove that `modulus` is nonexpanding.
- [x] Prove closeness preservation for translation and binary addition.
- [ ] Package the complex constructor as a uniformly continuous map from the
      real-plane product premetric.
- [ ] Prove continuity/Lipschitz estimates for addition and fixed-scalar
      multiplication.
- [ ] Prove binary multiplication continuous at every point.
- [ ] Prove inversion continuous on subspaces whose modulus has a positive
      lower bound.
- [x] Add reusable predicate-relative local-bound certificates with
      restriction, congruence, radius shrinking, center extraction, and
      constant, identity, negation, addition, multiplication, and
      fixed-scalar constructors.

### Domains

- [x] Introduce complex predicates/subspaces and open-ball witnesses.
- [x] Define `HasComplexDerivativeWithinAt` and `HolomorphicOn`.
- [x] Recover the existing total derivative notions as special cases.

Domain-aware calculus is required for inverse, rational functions, logarithm
branches, and contour integration.

## Phase 2: limits and series

Status: in progress.

### Sequence laws

- [x] Prove convergence and Cauchy properties for constant sequences.
- [ ] Prove convergence of shifted sequences and subsequences.
- [ ] Characterize complex convergence coordinatewise.
- [x] Prove preservation of limits by addition, negation, subtraction, and
      conjugation.
- [x] Add the generic nonexpanding-map convergence and Cauchy constructors,
      applicable in particular to `modulus`.
- [ ] Prove preservation of limits by scalar multiplication, multiplication,
      and powers.
- [ ] Prove preservation by inversion under a positive lower-modulus bound.
- [x] Package the corresponding Cauchy-sequence constructors for the completed
      operation laws.

### Series laws

- [ ] Add linearity and conjugation laws for convergent series.
- [x] Prove the finite-sum modulus bound.
- [x] Prove that convergence of `Σ modulus (a n)` makes the complex partial
      sums Cauchy.
- [x] Add a nonnegative real-series comparison theorem and a rational
      geometric-series convergence theorem based on the existing ratio test.
- [x] Prove absolute and Cauchy convergence of the geometric series from an
      explicit rational contraction bound.
- [x] From `modulus z < 1`, construct propositionally truncated witnesses of
      absolute convergence, Cauchy convergence, and existence of a complex
      limit.
- [x] Prove that every convergent real series has eventually small terms.
- [x] Derive apartness of `1ℂ -ℂ z` from `modulus z < 1`, and prove the finite
      geometric inverse-correction and inverse-error identities.
- [x] Identify its sum as the witnessed inverse of `1ℂ -ℂ z`.

The geometric-series formula is exposed as the pair:

```agda
geometricSeriesConvergesToSum :
  (bound : RationalContractionBound z) →
  SeriesConvergesToℂ (geometricTerms z)
    (geometricSeriesSum z bound)

geometricSeriesSum≡inverse :
  (bound : RationalContractionBound z) →
  geometricSeriesSum z bound ≡
  invℂ (1ℂ -ℂ z) ...
```

The untruncated computational interface deliberately uses
`RationalContractionBound z`, which contains a positive rational `q`, a proof
`modulus z <ᵣ rat q`, and `q < 1`.  Since strict order on the Cauchy reals
supplies an intermediate rational only under propositional truncation, the
weaker hypothesis `modulus z <ᵣ 1` cannot construct a convergence modulus
without returning a truncated witness.  In that case,
`geometricSeriesInverseFormulaTruncated` returns a truncated sum together with
both its convergence proof and its equality to the witnessed inverse.

## Phase 3: differential calculus

Status: in progress.

- [ ] Prove uniqueness of the complex derivative.
- [ ] Prove that complex differentiability implies continuity.
- [ ] Add congruence under pointwise equality.
- [x] Add sum, negation, subtraction, constant-scalar, and product rules.
- [x] Add a chain rule for inner maps that preserve apart increments.
- [ ] Extend the chain rule to arbitrary inner maps through a remainder-form
      derivative or an equivalent constructive interface.
- [x] Add natural-power derivative theorems.
- [x] Add polynomial derivative theorems.
- [x] Add inverse and quotient rules on apart domains.
- [x] Extract the inverse rule's neighborhood-bound hypothesis into a shared
      local-boundedness layer with algebraic constructors.
- [ ] Package closure laws for `Holomorphic` and `HolomorphicOn`.
- [ ] Connect real two-coordinate differentiability and the Cauchy--Riemann
      equations to the complex derivative.

A representative acceptance example is differentiation of a nonconstant
rational function with the denominator's apartness witness explicit.

## Phase 4: power series and elementary functions

Status: planned.

- [ ] Define convergence disks and majorants for complex power series.
- [ ] Prove uniform convergence on strictly smaller closed disks.
- [ ] Justify termwise addition, multiplication, and differentiation.
- [ ] Construct the complex exponential power series and prove agreement with
      the current polar definition.
- [ ] Prove
      `expℂ′ = expℂ`, `sinℂ′ = cosℂ`, and `cosℂ′ = -sinℂ`.
- [ ] Add Taylor expansions and useful remainder estimates.
- [ ] Give roots of unity their group structure and prove periodicity of
      powers of the principal root.
- [ ] Prove distinctness and the finite root-sum identity wherever the
      constructive angle theory supplies the required separation.

## Phase 5: complex integration

Status: planned.

- [ ] Define complex integration coordinatewise from real integration.
- [ ] Define interval paths, path derivatives, and line integrals.
- [ ] Prove linearity, reversal, concatenation, and affine
      reparameterization.
- [ ] Prove the fundamental theorem for line integrals:

```agda
∫γ F′ dz ≡ F (endpoint γ) -ℂ F (startpoint γ)
```

- [ ] Evaluate integrals of polynomials and `expℂ`.
- [ ] Prove vanishing of closed-path integrals for functions with a global
      primitive.
- [ ] Compute the unit-circle integral of `1/z` directly.

A general Cauchy theorem and integral formula are deferred until the required
two-dimensional or homotopy-invariance infrastructure is available.

## Phase 6: argument and logarithm branches

Status: planned.

- [ ] Define a `LogBranch` record carrying an argument on a specified domain.
- [ ] Construct branches using the existing circle chart and unwinding theory,
      beginning with one half-plane or slit domain.
- [ ] Prove `expℂ (logℂ z) ≡ z` on a branch.
- [ ] Prove the derivative of a branch is `1/z`.
- [ ] Define branch-dependent complex powers.
- [ ] Develop winding numbers and argument-principle infrastructure.

There is deliberately no branch-free global argument or logarithm in the core
API.

## Implementation order

The first bounded implementation slice is:

1. [x] modulus nonexpansiveness and basic metric-operation packaging;
2. [x] initial algebraic laws for convergent complex sequences;
3. [x] absolute convergence of complex series;
4. [x] the convergent geometric-series formula, including explicit convergence
   to a packaged sum and identification of that sum with the witnessed inverse;
5. [x] a representative checked rational contraction bound at `1/2`.

After that slice, implement domain-aware derivative rules before adding more
isolated transcendental identities.

The domain-aware follow-up now has its predicate/open-ball foundation,
additive derivative closure laws, fixed-complex-scalar closure, a quantitative
product rule, a conditional chain rule, natural-power derivatives in the
standard `(n + 1) · z ^ n` form, and Horner-form finite-polynomial
derivatives, together with inverse and quotient rules for total extensions
that agree with witnessed inversion on the selected predicate.  The inverse
rule's neighborhood certificate now lives in a shared local-bound layer with
the first structural and algebraic constructors.  General continuity,
additional higher-level boundedness automation, and remainder-form packaging
are the next calculus layer; they can further reduce explicit bound arguments
and remove the chain rule's apart-increment restriction.

## Implemented modules

The current development slice is organized into semantic leaves:

- `Complex.Metric.Modulus` and `Complex.Metric.Operations` contain the new
  metric estimates.
- `Complex.Analysis.Sequence.Laws` exports constant, addition, negation,
  subtraction, conjugation, nonexpanding-map, and convergence-to-Cauchy laws.
- `Complex.Analysis.Series.Absolute` contains finite-sum bounds and the
  absolute-convergence criterion.
- `Complex.Analysis.Series.Geometric` exports modulus preservation for powers,
  nonnegative comparison, positive-rational geometric convergence, explicit
  rational contraction bounds, and the resulting complex convergence
  theorems.  Its `Terms`, `Inverse`, and `Sum` leaves provide eventual term
  decay, apartness of `1ℂ -ℂ z`, the finite inverse-correction/error
  identities, and the geometric sum formula.
- `Complex.Inverse.Modulus` identifies the modulus of a witnessed complex
  inverse with the corresponding witnessed real inverse.
- `Complex.Modulus.Bounds` packages explicit positive-rational upper bounds
  for a complex modulus, proves their propositionally truncated existence,
  and supplies the quantitative multiplication estimate used by calculus.
  `Complex.Modulus.BoundAlgebra` constructs bounds for zero, one, negation,
  addition, multiplication, and natural powers.  The general
  modulus-of-power theorem now lives in the lower `Complex.Modulus.Power`
  layer; its previous geometric-series entry point remains a compatibility
  re-export.
- `Complex.Domain` packages complex predicates, their canonical premetric
  subspaces, the whole complex plane, rational open balls, and constructive
  open-domain witnesses.
- `Complex.Calculus.Derivative.Within` restricts the existing
  punctured-neighbourhood derivative to a complex predicate, provides
  `ComplexDifferentiableWithinAt` and `HolomorphicOn`, restriction laws,
  whole-space conversions in both directions, and domain-aware affine,
  identity, constant, and square examples.
- `Complex.Calculus.Derivative.Algebra` exports addition, negation,
  subtraction, fixed-scalar, product, conditional composition, and
  natural-power and finite-polynomial rules at the
  `HasComplexDerivativeWithinAt`,
  `ComplexDifferentiableWithinAt`, and `HolomorphicOn` levels, together with
  corresponding rules for the existing total derivative API.  Positive
  powers have the standard derivative
  `positiveNaturalComplex n ·ℂ z ^ℂ n`; the zero power has derivative zero.
  The scalar rule accepts an explicit
  `ComplexScalarBound c`, consisting of a positive rational upper bound for
  `modulus c`; `complexScalarHasRationalBound` proves that such data always
  exists propositionally truncated.  This distinction preserves the explicit
  convergence radius required by the derivative definition.  The product
  rule similarly accepts separate bounds for both function values and both
  derivatives.  Its error is split into two quarter-sized linear terms and a
  half-sized quotient cross term; quotient bounds follow from unit derivative
  error estimates.  Keeping these four bounds as separate arguments also
  avoids a pathological normalization observed when pairing dependent
  `ComplexScalarBound` values in an otherwise redundant wrapper.
  `HasComplexDerivativeWithinAt-compose` additionally requires the inner map
  to map the source predicate into the outer predicate and to satisfy
  `LocallyPreservesApartIncrementsWithinAt`, including an explicit rational
  radius.  This second hypothesis is necessary for the current
  punctured-quotient definition: an outer difference quotient cannot be
  formed when the inner increment is not known apart from zero.  Identity and
  affine maps with an apart coefficient have constructors for this condition.

The natural-power implementation keeps positive powers separate at the
`HasComplexDerivative...` level and unifies them with the zero case at the
differentiability level.  This avoids forcing Agda to normalize a recursive
dependent `ComplexScalarBound`.  Small opaque paths separately expose power
unfolding, coefficient succession, and the product-rule derivative
recurrence; directly applying generic ring identity proofs to reducible
powered terms was observed to cause multi-gigabyte elaboration stalls.

Finite polynomials use coefficient lists in increasing degree order and
Horner evaluation.  Their derivative evaluator follows the matching Horner
recurrence.  The quantitative theorem accepts a
`PolynomialTailBoundsAt z coefficients` certificate containing explicit
value and derivative bounds for every recursive tail; empty and singleton
certificates and a linear-polynomial constructor are provided.  The public
  evaluators are opaque with separate empty/cons computation paths.  A
  transparent recursive derivative evaluator, or a single definition combining
  the product rule, addition rule, and both transports, was observed to force
  multi-gigabyte normalization.  Splitting these stages into opaque typed
  lemmas keeps the polynomial leaf checking in a few seconds.

`Complex.Calculus.Derivative.Algebra.Inverse` represents a constructive
reciprocal on a predicate by `ReciprocalOn P f g`; the stronger
`WitnessedInverseExtensionOn P f g` records explicit apartness witnesses and
agreement with `invℂ`, and implies the reciprocal relation.  Because the
derivative API takes total functions, `g` is a total extension, while all
inverse equations are required only on `P`.  The derivative is
`(-g z) ·ℂ f′ z ·ℂ g z`.  Its quantitative proof takes a bound for `g z` and
a `ComplexLocalBoundWithinAt P g z` controlling nearby reciprocal values.
The error separates into a linear derivative-error term and a quadratic
cross term.  Their estimates multiply by the two center reciprocals, two
difference quotients, and the nearby reciprocal in separate opaque stages;
packaging the five-factor bound as one dependent value reproduced the known
multi-gigabyte elaboration pathology.

`Complex.Calculus.Derivative.Algebra.Quotient` combines that inverse rule with
the product rule.  It exports domain-aware and total derivative,
differentiability, and holomorphic closure APIs for a numerator and a chosen
reciprocal extension of the denominator.  Apartness remains explicit through
`WitnessedInverseExtensionOn`, and all quantitative derivative/value bounds
remain caller-visible rather than being extracted from truncated
Archimedean existence.

`Complex.Calculus.LocalBound` owns `ComplexLocalBoundWithinAt`, retaining its
availability through the inverse module for compatibility.  It adds
predicate restriction and congruence, radius shrinking, extraction of the
center's scalar bound, and explicit constructors for constants, the identity,
negation, addition, multiplication, and fixed-scalar multiplication.  Binary
constructors use the minimum input radius and the corresponding sum or
product of rational bounds.  The quotient example now obtains its constant
reciprocal neighborhood certificate from this common interface.

The local-bound proofs state their modulus estimates directly.  Returning a
dependent `ComplexScalarBound` from a transparent helper and immediately
projecting its inequality caused conversion checking to remain active around
3 GiB; the equivalent direct inequalities check in a few seconds.  Likewise,
feeding the center-bound extractor back into the large reciprocal theorem
currently reproduces that elaboration pathology, so the theorem retains its
separate explicit center and neighborhood arguments even though the former is
mathematically derivable from the latter.

The geometric implementation avoids whole-function rewriting through
`seqΣ`.  Indexed computation paths and explicit transports are used instead;
this prevents pathological lossy unification around reducible recursive
sequence aliases.  The geometric sum is deliberately an opaque typed value
with a separate inverse-identification path: putting the fully reducible
witnessed inverse directly in the convergence target causes pathological
unification, while the paired API is equivalent and checks predictably.
For the same reason, dependent derivative adapters pass their hidden function,
point, and derivative arguments explicitly; inferring these parameters from a
fully unfolded quotient-limit proof causes pathological unification.
Difference-quotient algebra is also normalized in small generic lemmas before
being instantiated with reducible quotient terms.  Derived subtraction is
transported through an opaque path from addition-with-negation rather than
asking conversion checking to unfold both derivative proofs.

## Validation

After every Agda edit, check the changed leaf with:

```bash
agda-codex <changed-file>
```

At the end of each slice, also check affected public aggregators and
`Complex.Examples`.  Performance is remeasured at phase boundaries with the
same coherent cold-interface methodology used by the 2026-07-23 report.
Unexpected regressions in the public aggregators or a new proof-heavy leaf
approaching the current `Trigonometric` cost trigger a dependency/import
review before further development.
