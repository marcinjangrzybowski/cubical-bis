# Scope roadmap for `Cubical.Analysis`

Date: 2026-08-30

Status: living implementation plan.  This document compares the sequential
Analysis development with `Cubical.HITs.CauchyReals`,
`Cubical.HITs.CauchyRealsP`, and the newer
`Cubical.Relation.Premetric.Completion.CauchySequence.Reals` development.  It
does not propose making any of those real carriers a dependency of Analysis.

## Goal and interpretation of coverage

The long-term goal is a coherent real-analysis stack over
`Alternative.Sequential`, with the stable, reusable mathematical coverage of
the two Cauchy-real developments.  "Roughly the same scope" should mean the
common progression

1. ordered field-like algebra;
2. sequences, finite sums, and series;
3. continuity and local quantitative estimates;
4. differentiation and integration;
5. power series and elementary functions;

rather than a file-for-file port.  The very large experimental tails of
`CauchyReals` (specialized transcendental approximations, complex analysis,
and function-specific proof pipelines) should follow only after the generic
real-analysis interfaces have stabilized.

## Capability matrix

| Area | Analysis status | Reference coverage | Next gap |
| --- | --- | --- | --- |
| Completion and density | Strong | Both | Keep generic; add helpers only when demanded by clients |
| Quantitative maps | Non-expanding and fixed-Lipschitz lifts | Both | Bounded-domain/local-Lipschitz combinators |
| Additive/ring/lattice algebra | Complete baseline | Both | Rational scalar and affine APIs |
| Non-strict and strict order | Complete baseline | Both | Interval/subspace packaging |
| Apartness | Additive and multiplicative laws | Both | Decide whether a standard field/apartness bundle fits without API churn |
| Reciprocal and division | Implemented away from zero | Both | Quotient continuity on domains; derivative rules |
| Naturals and powers | Implemented baseline | Both | Integer/rational scalar compatibility |
| Polynomials | Horner evaluation, rational computation, continuity, limits | Both | Bounds, local Lipschitz estimates, derivatives |
| Ordinary sequences | Limits, constants, shifts, unary/binary preservation | Both | Eventually-equal/order API; witness hierarchy |
| Finite sums | Preserve native witnesses and limits | `CauchyRealsP` | Ordered and absolute-value bounds |
| Series | Partial sums, linear operations, term test | Both | Tails, absolute convergence, comparison, geometric series |
| Power series | Missing | `CauchyRealsP` | Start only after robust series bounds |
| Continuity on domains | Missing | Mostly `CauchyReals` and newer completion reals | Open/closed intervals, subspaces, composition library |
| Derivatives | Missing | Both | Definition, uniqueness, algebra, chain rule, polynomials |
| Integration | Missing | Newer completion reals and parts of `CauchyReals` | Uniform-limit and partition infrastructure first |
| Elementary functions | Missing | Mostly `CauchyReals` | Exponential/logarithm before trigonometry |
| Complex analysis | Out of current core scope | `CauchyReals` | Revisit after real elementary analysis |

## Techniques already transferred successfully

### Dense extensionality

The most successful shared technique is to define operations quantitatively
and prove laws on rational points.  Continuity plus rational density then
proves the real law.  Analysis uses this for ring, lattice, order, absolute
value, and reciprocal laws.  This avoids constructor recursion and keeps
proofs independent of the completion presentation.

### Bounded reciprocal followed by witness elimination

The reciprocal implementation follows the constructive architecture of
`CauchyRealsP`:

1. clamp rational inputs at a positive rational lower bound;
2. prove an exact Lipschitz estimate for the clamped reciprocal;
3. lift that globally Lipschitz map to reals;
4. prove compatibility when two bounds both apply;
5. eliminate the truncated positive-gap witness into the set of reals; and
6. split signed apartness into positive and negative cases.

The result retains computational lemmas at rational points and does not choose
a denominator bound globally.  Natural Archimedean bounds prove positivity of
the reciprocal, enabling involution, sign laws, and reflection of product
apartness.

### Horner recursion and finite recursion

Horner evaluation is the right polynomial representation here: evaluation,
rational computation, and continuity follow from constants, addition, and
multiplication without materializing powers.  Similarly, finite sums combine
only finitely many truncated witnesses.  Neither construction introduces a
choice principle.

### Quantitative interfaces before qualitative interfaces

`Completion.Lipschitz` extends a map with one fixed positive rational
Lipschitz constant and preserves the exact constant.  Bounded reciprocal uses
this instead of falling back to ordinary continuity.  Future local estimates
should follow the same rule: retain the numerical modulus until the last API
layer, then derive continuity.

## Techniques that should be adapted, not copied

### Treat the other real developments as specifications

The carriers are not definitionally equal.  In particular, the newer
`CauchySequence.Reals` uses a different completion implementation.  Thin
re-exports would therefore create conversion costs and brittle dependencies.
Reference the theorem shape and proof architecture, then implement it using
the Analysis lift, order, and sequence interfaces.

### Do not copy constructor-specific eliminators

Uniform maps belong in generic non-expanding or Lipschitz lifts.  Non-uniform
maps belong in bounded transforms followed by compatibility, or in the
completion-centred lift.  Constructor recursion should be reserved for the
generic completion layer itself.

### Keep the sequence witness distinction explicit

Analysis currently has:

- `ChosenIsCauchySequence`, a chosen global modulus;
- `SeqWitness`, the propositional truncation of such a global modulus; and
- `isLimitSequence`, whose tail exists separately at each radius.

The newer `CauchySequence.Reals` deliberately uses a radiuswise Cauchy witness
and can prove Cauchy iff convergent without selecting a global modulus.
Analysis cannot silently import that converse.  For now, series should use
`Summable` (existence of a limit) as their primary interface and use
`IsCauchySeries` only in the sound direction from native witness to sum.  A
future witness-hierarchy module should document conversions and isolate any
additional principle that a converse would require.

## Phased implementation plan

### Phase 1: ordered field-like core — complete

- Fixed-constant Lipschitz extension.
- Bounded and positive reciprocal.
- Signed reciprocal from apartness, division, cancellation, involution, and
  sign/order laws.
- Multiplicative apartness and reflection laws.

Exit condition: checked rational computation and two-sided inverse laws, with
no postulates and no carrier conversion.  This condition is met.

### Phase 2: finite algebraic analysis — baseline complete

- Natural embedding and monotonicity.
- Horner polynomials with rational computation and continuity.
- Ordinary sequence limit-preservation combinators.
- Finite sums preserving native Cauchy witnesses and limits.

Next additions: rational scalar multiplication, affine maps, polynomial
majorants, finite triangle inequalities, and polynomial local Lipschitz
bounds.

### Phase 3: series core — started

The base now has partial sums, additive and scalar operations, unique sums, and
the term test.  Continue in this dependency order:

1. tail/drop and finite-modification invariance;
2. partial-sum order and absolute-value bounds;
3. absolute convergence and comparison;
4. geometric series, first for rational ratios and then real ratios;
5. Cauchy products and convolution under absolute hypotheses; and
6. power-series definitions and interior convergence.

Do not begin convolution before finite-sum reindexing and absolute bounds are
available as separate checked modules.

### Phase 4: domains and local continuity

- Metric balls, radii, closed/open intervals, and subspace premetrics.
- Continuous and uniformly continuous functions on a domain.
- Restriction, composition, products, pasting, and uniform-limit closure.
- Bounded-domain Lipschitz lemmas for powers, polynomials, and reciprocal.

This phase should reuse the generic premetric subspace and mapping instances;
it should not create real-specific copies of generic structures.

### Phase 5: differential calculus

Implement a small derivative kernel before specialized functions:

1. derivative at a point and on a domain;
2. uniqueness from punctured/local control;
3. constants, identity, addition, negation, and scalar rules;
4. product and chain rules;
5. powers and polynomials; and
6. reciprocal, quotient, and rational functions on apart domains.

The signed reciprocal derivative should consume an explicit domain proof that
the denominator stays apart from zero; it should not repeatedly eliminate
pointwise apartness inside the difference quotient.

### Phase 6: integration

First build finite partitions, mesh, and Riemann sums over intervals.  Then
prove preservation under constant, addition, negation, and scaling, followed
by a Cauchy criterion and uniform-limit theorem.  The dyadic integration
architecture in the newer completion reals is a useful specification, but its
sealed implementation modules should not be copied wholesale.

### Phase 7: power series and elementary functions

- Power-series algebra and termwise differentiation on strict interiors.
- Exponential from a power series, then its algebraic and derivative laws.
- Logarithm on positive reals using inverse/integration or a controlled local
  series.
- Trigonometric functions after the power-series and differentiation APIs are
  stable.

### Phase 8: optional extended scope

Complex numbers, complex series, and specialized inverse trigonometric
functions are valuable but should remain outside the core milestone.  They
depend on a mature real modulus, series, and calculus stack.

## Performance gates

Every phase must preserve the following constraints:

- A lifted operation has one implementation path.  Do not instantiate a
  sequential lift and a regular lift in the same client merely to compare
  them.
- Quantitative proofs are separated from large algebraic law modules.
- Aggregate facades expose curated names and should remain comfortably below
  ten seconds in a warm focused check on the current development machine.
- New focused modules should normally check in a few seconds.  A minute-scale
  check is an architectural warning, not an acceptable steady state.
- Rational computation lemmas are required before an operation is exported.
- No postulates, unsafe pragmas, weakened options, or hidden carrier
  equivalences are introduced.

A concrete failed experiment reinforces the first two rules: deriving a
canonical multiplication `SeqWitness` directly through the full product-
completion comparison ran for more than two minutes.  The experiment was
removed.  The right follow-up is a lightweight generic binary
Cauchy-continuous witness combinator, not embedding the comparison proof in
`Real.Algebra.Multiplication.Base`.

## Near-term work queue

1. Rational scalar and affine maps, with exact Lipschitz constants.
2. Eventually-equal/eventual-order sequence operations without global choice.
3. Series tails and finite modifications.
4. Finite triangle inequality and absolute convergence comparison.
5. Geometric series and its reciprocal identity.
6. Polynomial majorants and derivative-ready local estimates.
7. Domain/subspace continuity layer.

This queue deliberately alternates user-facing theorems with generic support
work so that no large specialized branch grows on a weak foundation.
