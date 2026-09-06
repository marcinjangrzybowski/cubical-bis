# Scope roadmap for `Cubical.Analysis`

Updated: 2026-09-06

Status: living implementation plan.  This document compares the sequential
Analysis development with `Cubical.HITs.CauchyReals`,
`Cubical.HITs.CauchyRealsP`, and the newer
`Cubical.Relation.Premetric.Completion.CauchySequence.Reals` development.  It
does not propose making any of those real carriers a dependency of Analysis.

The latest [logarithm development](LOGARITHM_2026-09-06.md) adds exponential
algebra, order, continuity and self-differentiation, a choice-free local
logarithm series, finite-partition approximate IVT, and a global exponential
equivalence and logarithm constructed by geometrically convergent arithmetic
iteration. Local-series compatibility remains open; inverse existence does not.
The positive-real multiplicative abelian group and its exp/log isomorphism
with the additive real group are now bundled in the standard algebra APIs.
The [choice-free policy](AGENTS.md) prohibits countable-choice assumptions,
even as explicit parameters; the former conditional adapters were removed.

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
| Additive/ring/lattice algebra | Complete baseline plus rational module and positive-real multiplicative abelian group, isomorphic to the additive group via exp/log | Both | Integer embedding and derivative-facing linear API |
| Non-strict and strict order | Complete baseline plus closed interval/radius subspaces | Both | Open domains and domain-restricted mapping API |
| Apartness | Additive and multiplicative laws | Both | Decide whether a standard field/apartness bundle fits without API churn |
| Reciprocal and division | Implemented away from zero; arbitrary numerator/denominator quotient derivatives are checked on explicit uniform positive and negative rationally bounded domains | Both | Performant full-apart derivative adapter and rational-function packaging |
| Naturals and powers | Naturals and rational scalars implemented | Both | Integer embedding and scalar/power compatibility |
| Polynomials | Horner evaluation, majorants, absolute bounds, local Lipschitz estimates, and structural derivative/composition rules | Both | Reusable closed-ball packaging and rational-function closure |
| Ordinary sequences | Limits, eventual equality/order, two asymptotic witness levels, and squeeze theorems | Both | Monotone convergence once supremum infrastructure exists |
| Finite sums | Witness/limit preservation, algebra, exchange, telescoping, monotonicity, absolute bounds, and convolution-oriented diagonal/triangular reindexing | `CauchyRealsP` | Partition reindexing as demanded by integration |
| Series | Linear operations, comparisons, tails, finite modifications, absolute-Cauchy comparison, rational/real contraction results, uniform family convergence, constructive native-Cauchy bounds, selected absolute-product closure, and bound-free Mertens products | Both | Radiuswise/weaker uniform witness variants and modulus-driven tests |
| Power series | Terms, finite-polynomial/rescaling/geometric laws, zero/finite-modification laws, coefficient growth, exact products, repeated formal derivatives, radiuswise entire values, uniform closed-radius convergence/continuity, closed-radius/strict-interior termwise differentiation, the entire exponential family with global algebra/order laws, entire sine/cosine coefficient families with exact Pythagorean and addition product identities, and the choice-free local logarithm series with reciprocal derivative | `CauchyRealsP` | Local exponential/logarithm compatibility and composition |
| Continuity on domains | Complete closed interval/radius retracts plus open half-lines, intervals, and absolute-radius balls | Mostly `CauchyReals` and newer completion reals | Domain maps, products, and pasting |
| Derivatives | Division-free kernel, uniqueness, algebra, ordinary and indexed chain rules, power/Horner/finite-sum rules, controlled reciprocal and arbitrary-denominator quotient rules, continuity, open-subspace adapters, and exact global/interval-local mean-value inequalities under radiuswise-uniform differentiability | Both | Full apart-domain reciprocal and rational-function packaging |
| Integration | Finite/tagged partitions, mesh and resampling bounds, equal/dyadic vanishing meshes, recursive dyadic sums with refinement bounds, a unique mesh-limit integral on ordered endpoints, an ordered-domain wrapper with reversed-interval regressions, and constant/additive/negative/subtractive/scaling laws | Newer completion reals and parts of `CauchyReals` | Common-refinement/Cauchy criterion for uniformly continuous integrands, then uniform limits |
| Elementary functions | Global exponential, sine, and cosine power-series values; sine/cosine values at zero, odd/even, Pythagorean, addition, and double-angle laws, sharp absolute bounds by one, exponential majorant bounds, derivatives, continuity, all finite higher-derivative convergence, second-derivative equations, four-step formal-derivative cycles, partial tangent/secant values with parity, Pythagorean, addition, and tangent double-angle identities on their exact cosine-apart domains, plus first-positive-cosine-zero characterization, historical and damped conditional Bishop limits, the `[0,1]` cosine lower bound, conditional quarter/half/full-turn laws, and strict monotonicity/embedding of sine on the complete closed quarter interval, finite approximate image density, and generic restricted sine/cosine inverse laws for supplied equivalences or intermediate-value witnesses | Mostly `CauchyReals` | Choice-free exact IVT; damped Bishop convergence and positivity; then unconditional π |
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

Anti-diagonal reversal and triangular reindexing are now available for series
products.  Further finite-sum reindexing laws should be added only as required
by convolution estimates and integration partitions.

### Phase 3: series core — substantial baseline complete

The base now has partial sums, additive and scalar operations, unique sums, the
term test, tail/drop equivalences, finite-modification correction laws,
partial-sum distance bounds, sum comparison and domination, and native-witness
absolute comparison.  The geometric layer proves the division-free
partial-sum identity and gives an explicit block/binary modulus, summability,
and the reciprocal value for every rational `|q| < 1`.  Real ratios inherit
these results when supplied with an explicit rational contraction bound.  A
uniform layer lets one selected majorant modulus control a whole family, and
the finite-sum layer now supplies the anti-diagonal/triangular reindexing used
by convolution.  The Cauchy-product layer proves its finite algebra,
rectangular decomposition, explicit remainder bounds, and the quantitative
Mertens theorem from native Cauchy hypotheses plus explicit uniform
  partial-sum bounds.  A native `SeqWitness` now yields the mere existence of
  one positive rational absolute bound.  Eliminating those bounds only into
  propositions gives Mertens remainder convergence, product summability, and
  the exact product value directly from native absolute/Cauchy hypotheses,
  without adding a choice principle.  The remaining dependency order is:

1. uniform-limit closure for continuous partial sums is implemented; extend it
   to reusable radiuswise/weaker uniform witness variants;
2. comparison tests driven by explicit Cauchy moduli.

Explicit exponential coefficient growth is now handled separately: a bound
`|a n| ≤ B G^n` reduces evaluation on `|x| ≤ R` to the geometric ratio
`G R`.  It supplies absolute convergence, a sum bound, uniform convergence,
and continuity whenever `G R < 1`.  Addition, subtraction, negation, and
bounded real scaling preserve the packaged growth hypotheses.

Do not begin convolution before finite-sum reindexing and absolute bounds are
available as separate checked modules.

### Phase 4: domains and local continuity

- Closed intervals, absolute-radius balls, their subspace premetrics,
  non-expanding clamps, and completeness are implemented.
- Open half-lines, intervals, and absolute-radius balls, including their
  openness witnesses, are implemented.
- Continuous and uniformly continuous functions on a domain.
- Restriction, composition, products, pasting, and uniform-limit closure.
- Bounded-domain Lipschitz lemmas for powers, polynomials, and reciprocal.

This phase should reuse the generic premetric subspace and mapping instances;
it should not create real-specific copies of generic structures.

### Phase 5: differential calculus

The kernel now defines a division-free first-order error on a general
premetric parameter space, provides ambient and pointwise derivatives,
supports continuous reparameterization and continuous difference factors,
and proves uniqueness.  Constants and the coordinate/identity function,
addition, negation, subtraction, real/rational scaling, multiplication,
composition, natural powers, Horner polynomials, and finite sums are checked.
Differentiability implies continuity, and open-predicate subspaces have
restriction and pointwise ambient adapters.  An indexed chain rule now lets
both derivatives live on the same parameter space, which is the missing
composition shape for subtype-valued denominators.  Reciprocal
differentiation is checked on explicit positive and negative rationally
bounded domains, including proof-independent positive and signed inverse
values.  Arbitrary differentiable numerators and denominators now have the
product-form quotient derivative whenever one fixed positive rational bound
separates the whole denominator family from zero on either side.  Continue in
this order:

1. isolate a performant full-apart reciprocal adapter; and
2. package rational functions over composable bounded denominator domains.

The signed reciprocal derivative should consume an explicit domain proof that
the denominator stays apart from zero; it should not repeatedly eliminate
pointwise apartness inside the difference quotient.

### Phase 6: integration

Finite and tagged partitions, widths, mesh predicates, sampling and
resampling estimates, and Riemann-sum algebra are now checked.  Equal and
dyadic partitions provide explicit vanishing-mesh families.  The semantic
integral is the unique value approached by every sufficiently fine tagged
partition; constants, addition, negation, subtraction, and arbitrary real
scaling preserve it.  A binary recursive dyadic sum has exact midpoint-width,
constant, additive, negative, and scaling laws together with a refinement
estimate controlled by the oscillation on each dyadic half.

The next layer is the actual existence theorem: turn the recursive refinement
estimate into a Cauchy bound for a radiuswise uniformly continuous integrand,
relate the recursive sums to tagged partitions, and remove dependence on the
canonical tags using the checked resampling estimate.  After that, add
uniform-limit preservation.  The dyadic integration architecture in the
newer completion reals remains a useful specification, but its sealed
implementation modules should not be copied wholesale.

### Phase 7: power series and elementary functions

`CauchyRealsP` contains generic power-series, majorant, uniform-convergence,
and differentiation infrastructure but no sine, cosine, tangent, or π
definitions.  The trigonometric result scope below is therefore compared with
`CauchyReals` and the newer completion-real power-series development, while
reusing the `CauchyRealsP` proof architecture where it transfers.

- Power-series terms, additive/scalar algebra, geometric majorants, and
  bounded-coefficient absolute and uniform convergence on every closed
  positive rational radius below one are implemented.  The canonical value is
  continuous there because its term functions are continuous and the partial
  sums converge uniformly.
- Explicit exponential coefficient growth now gives the more general radius
  criterion `G R < 1`, with absolute evaluation bounds and a continuous
  closed-radius value.  Growth certificates have additive, subtractive,
  negative, and bounded-scaling closure laws.
- Evaluation at zero is unconditionally summable with value `a 0`.  Eventual
  equality of coefficient sequences transports native Cauchy witnesses and
  summability, while an explicit cutoff gives the exact finite correction to
  the value; cutoff-dependent data remains truncated when the equality is
  merely eventual.
- Zero-padded finite coefficient lists are native Cauchy with the explicit
  modulus `length coefficients`, and their power-series value agrees exactly
  with Horner evaluation.  That length is also a uniform closed-radius modulus;
  weighted derivative coefficients make the canonical formal derivative equal
  the Horner derivative and give a direct closed-radius derivative theorem.
  Coefficient rescaling by `c^n` transports Cauchy,
  absolute-Cauchy, `HasSum`, summability, and values along the substitution
  `x ↦ c x`.  The constant-one coefficient series is explicitly the geometric
  series and inherits its quantitative rational-contraction convergence and
  positive-reciprocal value.  Its self-convolution has coefficients `n + 1`
  and evaluates to the square of that reciprocal through native Mertens.
- The formal derivative shifts and weights coefficients, respects the linear
  operations, and identifies each derivative-series term with the derivative
  of the corresponding successor power-series term.  It also satisfies the
  exact coefficient-level Leibniz rule for Cauchy products without requiring
  convergence data.  Its finite iterates compose, preserve addition/scaling,
  and satisfy the explicit coefficient formula
  `D^k a n = ((n+1)⋯(n+k)) · a (n+k)`.
- Cauchy multiplication of coefficient sequences evaluates termwise to the
  Cauchy product of the two evaluated series.  Explicit-bound and native-Cauchy
  wrappers give summability and an exact `HasSum` product value.  Negation and
  subtraction now have native summability and proof-independent value laws,
  while the elementary coefficient operations preserve explicit absolute
  bounds.  A quantitative rectangular-product/remainder construction also
  closes selected absolute-Cauchy witnesses under Cauchy products, with a
  sealed native entry point for iterative clients.
- The finite divided-difference factor, its power factorization, its diagonal
  formal-derivative identity, continuity, closed-radius bound, and domination
  by a derivative majorant are checked.  Derivative-majorant Cauchy convergence
  now makes the whole factor family uniformly Cauchy on a closed radius, also
  when obtained by restriction from a larger radius.  Its canonical sum now
  factors the difference of two power-series values and agrees with the
  formal-derivative value on the diagonal.  Continuity of that uniform factor
  therefore gives a checked derivative of the canonical uniform sum along the
  closed-radius coordinate.  A generic open-interior adapter now gives the
  ordinary ambient derivative for any explicit extension agreeing on the
  closed radius.  The power-series wrapper can derive and return the reusable
  inner-radius derivative witness from an outer derivative-majorant series.
  A radiuswise entire-series package now selects the closed radius `|x| + 1`,
  constructs a global canonical value, proves its agreement with every local
  uniform value, and exposes the local derivative plus its proof-independent
  equality to the global formal-derivative value.  Radiuswise families for all
  iterated formal derivatives and divided-difference factors give the same
  paired equality/derivative interface at every higher order.
- Repeated geometric convolution has a structural coefficient family with
  simplex/binomial closed forms, nonnegative polynomial majorants, and the
  formal law `D I_k = (k + 1) I_(k+1)`.  Native Mertens gives its successor sum
  recurrence, while selected absolute-product closure constructs the
  all-order absolute-Cauchy family directly from a rational contraction bound.
  Thus every finite order has unconditional absolute/Cauchy convergence and a
  proof-independent reciprocal-power value on that domain.  Exponential
  coefficients are exact embedded rational factorial reciprocals and satisfy
  `D a = a` as well as the corresponding repeated-derivative fixed point.  The concrete coefficient
  bound `1/n! ≤ 2·(1/2)^n` supplies absolute and uniform convergence on every
  closed positive rational radius below two.  The parameterized estimate
  `1/n! ≤ B^B·(1/B)^n` now supplies the same APIs on every explicit rational
  radius below a supplied positive natural `B`.  The Archimedean bridge now
  restricts those estimates to arbitrary real radii, packages all repeated
  derivatives and divided differences, and exposes the global exponential
  value with its fixed-point derivative evidence.
- Sine and cosine now use exact rational sign masks times the exponential
  factorial coefficients.  Exponential majorization supplies uniform Cauchy
  convergence on every real closed radius for their terms, formal
  derivatives, and divided-difference factors.  Their formal derivatives
  cycle as `D sin = cos`, `D cos = -sin`, and `D^4 = id`.  The resulting
  global values `sinℝ` and `cosℝ` satisfy their values at zero, have the
  expected global derivatives, are continuous, and satisfy the second-order
  equations `sinℝ'' = -sinℝ` and `cosℝ'' = -cosℝ`.  Rescaling coefficients by
  `-1` proves the odd/even identities first for term sequences and then for
  the canonical values.  Coefficient majorization also bounds both absolute
  values by the global exponential evaluated at `|x|`, and supplies entire
  uniform term and divided-difference convergence at every finite derivative
  order.  The formal Leibniz law reduces the sum of the sine-square and
  cosine-square coefficient products to the unit series; native Mertens
  convergence then gives `sinℝ² + cosℝ² = 1` for the global values.  Located
  order reflects the resulting component square bounds to the sharp global
  laws `|sinℝ x| ≤ 1` and `|cosℝ x| ≤ 1`.  The same product API, combined
  with exact factorial/binomial summands and finite anti-diagonal identities,
  proves the total addition formulas for both functions.  Their diagonal
  specializations and Pythagorean rewrites give the standard sine/cosine
  double-angle laws.  On the constructive subspace where cosine is apart from
  zero, tangent and secant are defined without arbitrary pole values.  Their
  cancellation laws give proof irrelevance, zero and parity formulas,
  `tanℝ = sinℝ · secℝ`, `1 + tanℝ² = secℝ²`, and the equivalent subtractive
  Pythagorean identity.  If the sum also lies in that subspace, cosine
  factorization constructively derives the gap for
  `1 - tanℝ x · tanℝ y` and gives both cleared and quotient addition
  laws for tangent and secant.  The converse denominator-gap constructor
  supplies the tangent double-angle law on its exact local domain.
  Differentiating these partial functions awaits the
  performant full-apart quotient adapter already identified in Phase 4.

The construction of π now has an explicit constructive boundary.
`IsFirstPositiveCosineZero` records the intended characterization, implies the
least nonnegative cosine-zero property, and is unique; the type of
characterized values is a proposition.  Bishop's historical iteration
`a(n+1) = a(n) + cos(a(n))` is defined and identified with the partial sums of
its increments.  Its Cauchy witness is an explicit existence target; any
limit candidate is already proved unique and a cosine zero.  An unconditional
`piℝ` is intentionally deferred until convergence and positivity before the
limit are checked.

For convergence, the preferred damped Bishop iteration
`a(n+1) = a(n) + (1/2) cos(a(n))` is now defined, has its own explicit Cauchy
boundary, and has the same conditional cosine-zero theorem.  Four-term
alternating power-series blocks prove `1 - x²/2 ≤ cos x`, `1/2 ≤ cos x`, and
strict cosine positivity on `[0,1]`.  Signed endpoint inequalities from the
uniform-derivative partition core, together with exact one-Lipschitz bounds for
sine and cosine, should give the rational contraction `7/8` and direct
domination by the existing geometric-series API.  The historical HIT proof
remains the specification, but its integration/FToC/strict-comparison stack is
too large for a direct port.  Leibniz/Machin, IVT/bisection, and integral
definitions remain secondary candidates because their required
inverse-trigonometric, IVT, or integration characterizations are not yet
available.

Algebraically, a cosine-zero candidate has sine-square one, and sine
positivity selects the value one.  A generic positive-quarter-turn API now
derives phase shifts, half-turn signs, and full-turn periodicity; it specializes
to a characterized half-pi. The sine-orientation fact is now proved from the
first-positive-cosine-zero characterization; it is no longer an extra input.
The corresponding restricted sine is now a continuous map from the complete
closed symmetric quarter interval to the complete unit interval, with checked
endpoint values.  The product-to-sum difference identity and positivity of its
midpoint-cosine and half-difference-sine factors prove strict increase, hence
injectivity and embedding.  Surjectivity is equivalent to the explicit
truncated `SineQuarterIntermediateValue` statement; for a positive
first-cosine-zero quarter, that statement is now the sole interval-level input
to an equivalence, including the characterized-half-pi specialization.
Quantitative sine separation and closeness reflection are available on the
quarter interval.  The exact IVT is now equivalent to a
completion-compatible approximate IVT: a sequence of interval points with a
single native Cauchy witness whose sine images converge to the target.
Completeness and continuity turn this data into an exact preimage, and the
approximate formulation feeds the equivalence theorem directly.  There is now
also a rational-target completion route aligned with Bishop-style inverse
constructions.  A `RationalSineInverseConstruction` consists only of a
rational-to-real candidate, its clamped sine equation, and quarter-interval
bounds.  Given a chosen (or merely bundled chosen) closeness-reflection
modulus, its graph is Cauchy-continuous, extends through sequential completion,
remains in the quarter interval, and satisfies `sin (G y) = clamp y`; this
already implies the desired equivalence when the specified data are supplied.
Finite slack-bisection proves approximate image density directly, but does not
select an infinite coherent sequence or inverse modulus. Exact IVT remains
open, and the former countable-choice bridge was removed. Generic restricted
inverse endpoint, zero, parity, continuity, and order laws remain available
for supplied equivalences or intermediate-value witnesses.
Adapters also accept explicit rational Cauchy witnesses, but the existing HIT
bisection inverse theorem is not directly reusable: it requires rational
endpoints and values plus a uniform positive lower slope, whereas sine has
real characterized endpoints and zero endpoint derivative.
The local logarithm series and global exponential equivalence are checked.
The global logarithm now has inverse, algebra, order, continuity, and derivative
laws without an equivalence hypothesis. Identifying it with the separate
series construction remains a compatibility target.

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

The signed reciprocal derivative exposed a fourth performance boundary.  Two
mathematically direct full-apart adapters—one transporting local positive and
negative derivative witnesses, one using a common inverse factorization—both
forced completion-level subtype/negation/inverse normalization for more than
60--90 seconds.  They were removed.  The checked positive and negative
quantitative-domain modules each remain near four seconds; a future full-apart
facade should eliminate into a small named local witness instead of unfolding
those transports in the derivative proposition.

The negative arbitrary-denominator quotient exposed the same issue one layer
later.  Composing through a proof-indexed signed inverse ran for more than
forty seconds.  Pulling back the already checked uniformly upper-bounded
negative reciprocal, which is extensionally the same inverse on the domain,
made the complete module check in about four seconds.  Quotient clients should
therefore compose bounded reciprocal maps first and only erase the bound at a
small public convenience layer.

A proof-indexed `powerSeriesValue` convenience theorem for the coefficient
Cauchy product crossed fifty-eight seconds even though the underlying exact
`HasSum` theorem checks in about five seconds.  The slow wrapper was removed.
Analytic value APIs should prefer proof-independent `HasSum` equations and use
summability proof irrelevance only in a small client theorem when necessary.

The entire-series derivative experiment found the same boundary twice.  A
single theorem transporting the local derivative proof across canonical-sum
equality ran beyond fifty seconds; returning the local derivative and the
equality as separate components checks in about six seconds.  Adding a
nonnegativity proof argument to every radiuswise convergence witness also ran
beyond fifty-five seconds because that proof entered canonical values.  The
checked interface therefore keeps radius evidence proof-free and leaves these
transports at the client boundary.

The finite-polynomial bridge found the analogous source-function boundary:
transporting the Horner derivative proof to the extensionally equal canonical
power-series source exceeded sixty seconds both as a whole-function `subst`
and as a pointwise rewrite.  The fast modules instead export the canonical
source-value equality, the canonical formal-derivative value equality, and the
direct Horner derivative theorem separately; together they preserve all bridge
data while keeping focused checks near six seconds.

## Near-term work queue

1. Instantiate the checked exact mean-value inequality with interval-uniform
   sine/cosine remainder estimates and derive the one-Lipschitz bounds needed
   for damped Bishop contraction, then construct its Cauchy and positivity
   witnesses. The inequality itself is now complete.
2. Construct coherent native-Cauchy inverse data for exact IVT. Finite
   approximate image density is complete, but choice-based exact inverse
   adapters are forbidden and have been removed.
3. Prove local exponential/logarithm compatibility and identify the total
   series candidate with the global logarithm. The choice-free global inverse
   and uniform local logarithm derivative estimates are now constructed.
4. Design a performant full-apart reciprocal derivative adapter and package
   bounded-domain rational functions.
5. Add the generic domain-map and pasting combinators demanded by calculus.
6. Turn recursive dyadic refinement into integrability for radiuswise
   uniformly continuous functions, then prove uniform-limit preservation.

This queue deliberately alternates user-facing theorems with generic support
work so that no large specialized branch grows on a weak foundation.
