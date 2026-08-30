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
| Quantitative maps | Non-expanding, fixed-Lipschitz, affine, local polynomial estimates, and non-expanding closed-domain clamps | Both | General bounded-domain/local-Lipschitz combinators |
| Additive/ring/lattice algebra | Complete baseline plus rational module | Both | Integer embedding and derivative-facing linear API |
| Non-strict and strict order | Complete baseline plus closed interval/radius subspaces | Both | Open domains and domain-restricted mapping API |
| Apartness | Additive and multiplicative laws | Both | Decide whether a standard field/apartness bundle fits without API churn |
| Reciprocal and division | Implemented away from zero | Both | Quotient continuity on domains; derivative rules |
| Naturals and powers | Naturals and rational scalars implemented | Both | Integer embedding and scalar/power compatibility |
| Polynomials | Horner evaluation, majorants, absolute bounds, local Lipschitz estimates | Both | Derivatives and reusable closed-ball packaging |
| Ordinary sequences | Limits, eventual equality/order, two asymptotic witness levels, and squeeze theorems | Both | Monotone convergence once supremum infrastructure exists |
| Finite sums | Witness/limit preservation, algebra, exchange, telescoping, monotonicity, and absolute bound | `CauchyRealsP` | Convolution-specific reindexing |
| Series | Linear operations, comparisons, tails, finite modifications, absolute-Cauchy comparison, signed rational half-contractions, and uniform family Cauchy/sum interfaces | Both | General strict contractions, Cauchy products, and uniform-limit closure |
| Power series | Terms, linear algebra, geometric majorants, bounded-coefficient convergence, and one-modulus uniform convergence on closed radii at most one half | `CauchyRealsP` | General strict interiors, products, and termwise differentiation |
| Continuity on domains | Closed intervals and absolute-radius balls as complete retract subspaces; open half-lines and intervals as open premetric subspaces | Mostly `CauchyReals` and newer completion reals | Open balls, domain maps, products, and pasting |
| Derivatives | Division-free local-error definition, reparameterization, factor criterion, constants/identity, and uniqueness | Both | Algebra, chain rule, continuity, and polynomials |
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

### Radiuswise truncated asymptotic data

Eventual equality/order uses one merely existing cutoff, while asymptotic
closeness uses a merely existing cutoff separately at each positive radius.
This is enough to transport ordinary limits and is closed under symmetry and
transitivity.  It transfers the useful theorem shape from `CauchyRealsP`
without choosing a global modulus and therefore fits the Analysis witness
hierarchy exactly.

The stronger `SelectedAsymptoticallyCloseSequence` merely selects one complete
radius-indexed cutoff function.  It maps to the radiuswise relation, is an
equivalence relation, and preserves and reflects the native `SeqWitness`.
This makes the exact constructive strength required by witness-producing
clients explicit instead of hiding a choice step.

The uniform-series layer follows the same discipline.  A
`ChosenUniformlyCauchySeries` contains one modulus shared by every point of a
family; its public proposition-valued form merely truncates that datum.  A
single native Cauchy majorant therefore supplies uniform convergence without
selecting separate pointwise moduli.  This is the constructive ingredient
used by bounded-coefficient power series on a closed rational radius.

### Central ordered-ring bounds

The absolute-value triangle inequality and two-variable monotonicity now live
in the real order layer.  Polynomial majorants, finite sums, and series tail
bounds consume those common results.  This avoids the earlier pattern where
each quantitative client rebuilt the same max-based proof and is the intended
shape for future norm and integration estimates.

### Complete subspaces as quantitative retracts

Closed intervals and absolute-radius balls inherit the ambient premetric.
Their clamp maps are non-expanding retractions, so completeness follows from
the generic theorem that a non-expanding retract of a complete space is
complete.  This is preferable to rebuilding Cauchy-sequence limit proofs for
each real domain and will scale to later uniformly continuous domain maps.

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

### Phase 2: finite algebraic analysis — complete

- Natural embedding and monotonicity.
- Rational scalar and affine maps with exact global Lipschitz constants.
- Horner polynomials with rational computation, majorants, absolute bounds,
  and closed-ball local Lipschitz estimates.
- Ordinary sequence limit-preservation combinators.
- Finite sums preserving native Cauchy witnesses and limits, with monotonicity
  and a finite triangle inequality.

Further finite-sum reindexing laws should be added only as required by series
products and integration partitions.

### Phase 3: series core — substantial baseline complete

The base now has partial sums, additive and scalar operations, unique sums, the
term test, tail/drop equivalences, finite-modification correction laws,
partial-sum distance bounds, sum comparison and domination, and native-witness
absolute comparison.  The geometric layer proves the division-free
partial-sum identity and gives an explicit global modulus, summability, and
the reciprocal value for every rational `|q| ≤ 1/2`.  A uniform layer lets one
selected majorant modulus control a whole family.  The remaining dependency
order is:

1. extend geometric convergence to arbitrary rational `|q| < 1`, then to real
   ratios equipped with rational contraction bounds;
2. uniform-limit closure for continuous families;
3. comparison tests driven by explicit Cauchy moduli;
4. finite-sum reindexing needed by convolution;
5. Cauchy products and convolution under absolute hypotheses; and
6. general strict-interior power-series convergence.

Do not begin convolution before finite-sum reindexing and absolute bounds are
available as separate checked modules.

### Phase 4: domains and local continuity

- Closed intervals, absolute-radius balls, their subspace premetrics,
  non-expanding clamps, and completeness are implemented.
- Open half-lines and intervals, including their openness witnesses, are
  implemented; add open balls.
- Continuous and uniformly continuous functions on a domain.
- Restriction, composition, products, pasting, and uniform-limit closure.
- Bounded-domain Lipschitz lemmas for powers, polynomials, and reciprocal.

This phase should reuse the generic premetric subspace and mapping instances;
it should not create real-specific copies of generic structures.

### Phase 5: differential calculus

The kernel now defines a division-free first-order error on a general
premetric parameter space, provides ambient and pointwise derivatives,
supports continuous reparameterization and continuous difference factors,
and proves uniqueness.  Constants and the coordinate/identity function are
checked.  Continue in this order:

1. addition, negation, subtraction, and scalar rules;
2. continuity as a consequence of differentiability;
3. product and chain rules;
4. powers and polynomials; and
5. reciprocal, quotient, and rational functions on apart domains.

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

- Power-series terms, additive/scalar algebra, geometric majorants, and
  bounded-coefficient absolute and uniform convergence on closed radii at most
  one half are implemented.
- Extend convergence and termwise differentiation to general strict interiors.
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

The rational geometric proof exposed a second normalization trap: expanding a
proof-dependent positive denominator and its reciprocal directly inside the
`HasSum` type made a focused check run for more than two minutes.  Naming the
denominator proof and sum value reduced the completed module to about four
seconds.  Proof-dependent analytic values should therefore be factored before
they appear in large dependent statements.

Open-interval openness exposed the same issue at hidden arguments: using the
abstract `width gap` projection left its implicit real endpoints to inference,
which unfolded lifted order and addition until the checker occupied roughly
13.4 GB.  Using `fst gap` and explicitly instantiated generic order transports
made the finished module check in about 2.8 seconds.  Local witness
projections and transport endpoints should remain syntactically explicit.

## Near-term work queue

1. Generalize geometric convergence from `|q| ≤ 1/2` to rational `|q| < 1`
   without regressing checker time.
2. Prove derivative addition, negation, subtraction, and scalar rules on top
   of the checked kernel.
3. Add open balls and domain-restricted continuity interfaces.
4. Prove uniform-limit closure for continuous families, then general
   strict-interior power-series convergence.
5. Prove product/chain rules followed by power and polynomial derivatives.
6. Add convolution after its remaining finite reindexing laws are isolated.
7. Add power-series products and termwise differentiation only after
   convolution and uniform-tail bounds are separately checked.

This queue deliberately alternates user-facing theorems with generic support
work so that no large specialized branch grows on a weak foundation.
