# Scope roadmap for `Cubical.Analysis`

Updated: 2026-10-10

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

The latest [integration and limit results](LIMITS_2026-09-15.md) add
boundedness from radiuswise uniform continuity, substitution with bounds
obtained automatically, uniform convergence of indefinite integrals, uniform
derivative stability under limits, construction from convergence at one
endpoint, and differentiation of series. The preservation theorems use
radiuswise convergence; constructions of new integrals use supplied native
moduli. General pointwise differentiability remains weaker than the uniform
derivative hypotheses used here.

## Goal and interpretation of coverage

The [circle development](Circle/README.md) now constructs the quotient
`ℝ/ℤ` directly from the sequential reals. Its turn premetric supports a
choice-free winding integer, subdivision and lift formulas, and the standard
integer-traversal computations. The construction does not depend on π or an
inverse trigonometric function. A bridge to the Cartesian circle and the
larger homotopy-classification results remain open.

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
`CauchyReals` (specialized transcendental approximations and function-specific
proof pipelines) should follow only after the generic real-analysis interfaces
have stabilized. The user expanded the scope to native complex analysis on
2026-10-08; its constructive FTA milestone is tracked below.

## Capability matrix

| Area | Analysis status | Reference coverage | Next gap |
| --- | --- | --- | --- |
| Completion and density | Strong | Both | Keep generic; add helpers only when demanded by clients |
| Quantitative maps | Non-expanding, fixed-Lipschitz, affine, local polynomial estimates, and non-expanding closed-domain clamps | Both | General bounded-domain/local-Lipschitz combinators |
| Additive/ring/lattice algebra | Complete baseline plus rational module, injective integer embedding with additive laws and metric separation, and positive-real multiplicative abelian group, isomorphic to the additive group via exp/log | Both | Integer multiplicative compatibility and derivative-facing linear API |
| Non-strict and strict order | Complete baseline plus closed interval/radius subspaces | Both | Open domains and domain-restricted mapping API |
| Apartness | Additive and multiplicative laws | Both | Decide whether a standard field/apartness bundle fits without API churn |
| Reciprocal and division | Implemented away from zero; arbitrary numerator/denominator quotient derivatives are checked on explicit uniform positive and negative rationally bounded domains | Both | Performant full-apart derivative adapter and rational-function packaging |
| Naturals and powers | Naturals, integers, and rational scalars implemented | Both | Integer scalar/power compatibility |
| Polynomials | Horner evaluation, majorants, absolute bounds, local Lipschitz estimates, and structural derivative/composition rules | Both | Reusable closed-ball packaging and rational-function closure |
| Ordinary sequences | Limits, eventual equality/order, two asymptotic witness levels, and squeeze theorems | Both | Monotone convergence once supremum infrastructure exists |
| Finite sums | Witness/limit preservation, algebra, exchange, telescoping, monotonicity, absolute bounds, and convolution-oriented diagonal/triangular reindexing | `CauchyRealsP` | Partition reindexing as demanded by integration |
| Series | Linear operations, comparisons, tails, finite modifications, absolute-Cauchy comparison, rational/real contraction results, uniform family convergence, constructive native-Cauchy bounds, selected absolute-product closure, and bound-free Mertens products | Both | Radiuswise/weaker uniform witness variants and modulus-driven tests |
| Power series | Terms, finite-polynomial/rescaling/geometric laws, zero/finite-modification laws, coefficient growth, exact products, repeated formal derivatives, radiuswise entire values, uniform closed-radius convergence/continuity, closed-radius/strict-interior termwise differentiation, the entire exponential family with global algebra/order laws, entire sine/cosine coefficient families with exact Pythagorean and addition product identities, and the choice-free local logarithm series with reciprocal derivative | `CauchyRealsP` | Local exponential/logarithm compatibility and composition |
| Continuity on domains | Closed interval/radius retracts, open half-lines/intervals/balls, and boundedness from radiuswise uniform continuity on a closed interval | Mostly `CauchyReals` and newer completion reals | Domain maps, products, and pasting |
| Derivatives | Division-free kernel, uniqueness, algebra, ordinary and indexed chain rules, power/Horner/finite-sum rules, controlled reciprocal and arbitrary-denominator quotient rules, continuity, open-subspace adapters, and exact global/interval-local mean-value inequalities under radiuswise-uniform differentiability | Both | Full apart-domain reciprocal and rational-function packaging |
| Integration | Tagged sums and comparison bounds, integrability from standard uniform continuity, order and algebra laws, uniform limits with supplied moduli, termwise series integration, oriented interval integrals, both uniform FTC directions, integration by parts, substitution with automatically obtained bounds, uniform derivative limits, and series differentiation | Newer completion reals and parts of `CauchyReals` | Integral existence from weaker radiuswise hypotheses; further closure laws and weaker FTC hypotheses |
| Elementary functions | Global exponential, sine, and cosine power-series values; sine/cosine values at zero, odd/even, Pythagorean, addition, and double-angle laws, sharp absolute bounds by one, exponential majorant bounds, derivatives, continuity, all finite higher-derivative convergence, second-derivative equations, four-step formal-derivative cycles, partial tangent/secant values with parity, Pythagorean, addition, and tangent double-angle identities on their exact cosine-apart domains, plus first-positive-cosine-zero characterization, historical conditional Bishop limits, convergent damped Bishop iteration, the `[0,1]` cosine lower bound, unconditional π with first-zero characterizations and quarter/half/full-turn laws, and strict monotonicity/embedding of sine on the complete closed quarter interval, finite approximate image density, and exact closed-interval sine/cosine equivalences and inverses with explicit uniform moduli | Mostly `CauchyReals` | Inverse calculus and further elementary functions |
| Complex analysis | Native ring, product premetric, l1 estimates and multiplicative Euclidean modulus, continuity and sequential completeness; complex exponential/sine/cosine with algebraic laws, periods, continuity and derivatives, and a continuous right-half-plane logarithm with reciprocal derivative; general complex derivatives with uniqueness, continuity, algebra/product/chain rules and polynomial holomorphicity; native series, Cauchy products, elementary-function series identities, repeated power-series differentiation and Taylor representation for convergent series; bounded uniform line-integral FTC with polynomial and constructed power-series primitives, including finite contours; contraction roots; polar form and nth roots; polynomial translation, division, coefficient estimates, approximate FTA in every degree, exact FTA under positive Bézout separability, quantitative root matching, the completed-multiset coefficient equivalence, finite near-zero nets, and spectral/block estimates | `CauchyReals` for baseline algebra/analysis | Separated clusters and further FTA formulations; primitive compatibility under Taylor reexpansion, holomorphic Taylor representation and Cauchy integral theory |
| Circle winding | Native quotient circle with abelian group and turn premetric; winding for uniformly continuous loops and self-maps, subdivision independence, supplied-lift formula, constants/identity/integer traversals | `CauchyReals.Circle.Winding` | Cartesian-circle equivalence and homotopy classification |

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

The [FTC development](FTC_2026-09-15.md) now proves that a radiuswise uniform
derivative on `[a,b]` is Riemann integrable with value `F b - F a`.
The proof expands at each tag toward both cell endpoints and telescopes the
increments; it does not assume integrability or continuity of the derivative.
Interval-local bounds prove the converse for integral increments, using
pointwise or radiuswise uniform continuity on the interval. Concatenated
dyadic partitions establish interval additivity for three existing integrals.
The actual accumulation function has derivative `f` when its ordered
subinterval integrals exist. Those integrals are now constructed from the
standard uniform continuity predicate on the closed interval, so
`UniformlyContinuousAccumulation` needs no separate integrability hypothesis.
These results use the Analysis reals directly and introduce no choice assumptions.

The existence proof uses cell overlap lengths to compare arbitrary tagged
partitions. Row and column sums of these weights are the original cell widths.
Continuity bounds the weighted differences wherever the cells overlap;
disjoint cells contribute zero. A supplied continuity modulus and an explicit
dyadic mesh index construct a native Cauchy witness, whose limit is the semantic
integral. Standard uniform continuity merely asserts the existence of such a
modulus; truncation is eliminated into the proposition of having a unique integral.

Radiuswise uniform continuity already gives the Riemann Cauchy condition,
but its separately truncated radii are not assembled into a global modulus.
Integrability under that weaker hypothesis remains future work.

The [integration expansion](INTEGRATION_2026-09-15.md) adds order and error
bounds, local extensionality, zero-length integrals, and oriented endpoint
differences within a fixed interval. Bounded integrands have Lipschitz
accumulation functions; continuous integrands have the expected signed
endpoint derivatives. Radiuswise uniform limits preserve convergence of
existing integrals, and a supplied convergence modulus constructs the limit
integral. Uniformly Cauchy series can be integrated term by term.

FTC now yields monotonicity, increment bounds, constancy for a zero uniform
derivative, and uniqueness of antiderivatives with an initial value. Bounded
uniform product and chain rules support integration by parts and substitution.
For substitution, standard uniform continuity of the target integrand can
construct the needed primitive. The new `ContinuousSubstitution` derives
the two bounds when the inner derivative is radiuswise uniformly continuous.
No monotonicity of the substitution is required for the oriented endpoint
formula. Radiuswise uniform continuity now also gives boundedness on every
ordered closed interval and therefore Lipschitz integral functions.

The [limit expansion](LIMITS_2026-09-15.md) proves uniform convergence of
indefinite integrals, stability of uniform derivatives under pointwise
function limits and uniform derivative limits, and construction of a uniform
function limit from convergence at one endpoint. Series can be differentiated
termwise from supplied pointwise sums and uniform derivative sums; a native
uniform Cauchy witness for the derivative series also constructs the original
sum from convergence at one endpoint. The limiting derivative need not have
a separate continuity proof. These are results for uniform derivatives;
weakening that hypothesis to ordinary pointwise derivatives remains open.

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

The native construction of π is now complete. `IsFirstPositiveCosineZero`
records positivity, cosine zero, and positive cosine at every preceding
nonnegative point. It implies the least nonnegative cosine-zero property;
the type of characterized values is a proposition.

The damped Bishop recurrence `d(n+1) = d(n) + (1/2) cos(d(n))`, starting at
zero, supplies an inhabitant. Addition formulas and sharp trigonometric
bounds translate the derivatives at zero into global radiuswise-uniform
derivative estimates. Analysis's signed uniform-FTC bounds preserve positive
cosine on `[0,d(n)]`. Since `d(1)=1/2` and `sin(1/2)>=1/4`, cosine residuals
contract by `7/8` after the first step. All increments are bounded by
`(7/8)^n`, yielding a native sequential Cauchy witness without choice. The
limit's first-zero characterization follows from positivity on the prefixes
and convergence at the single radius supplied by a strict gap.

`Pi.Value` exports `halfPiℝ`, `piℝ`, and `twoPiℝ`, their unique first-cosine-
zero / first-sine-zero characterizations, least-zero properties, special
values, phase shifts, and `2π` periodicity. The historical undamped Bishop
iteration remains available as a separate conditional API. It is not a
prerequisite for π. No HIT-real comparison or exact IVT is used.

The identity comparison with HIT `Trigonometry/{Base,Pi,Identities}` is
documented in `Real/Series/PowerSeries/Trigonometric/README.md`. The native
API now includes all four product-to-sum formulas, the remaining sum and
difference factorizations, complementary squares, coefficient/power
double-angle forms, power reduction, squared half-angle formulas, negative
phase shifts, reflections, and every integer period. The turn-coordinate
periodicities match those used in HIT `Circle.Core`. Existing identities are
reused, including the unrestricted sine-difference factorization. Sharp
derivative bounds yield global non-expanding sine and cosine and
`|sin x| ≤ |x|`; native FTC constructs the definite sine/cosine integrals.
These results are public through `Trigonometric` and introduce no carrier
comparison, exact inverse, or choice hypothesis.

Algebraically, a cosine-zero candidate has sine-square one, and sine
positivity selects the value one.  A generic positive-quarter-turn API now
derives phase shifts, half-turn signs, and full-turn periodicity; it specializes
to a characterized half-pi. The sine-orientation fact is now proved from the
first-positive-cosine-zero characterization; it is no longer an extra input.
The restricted sine is a continuous embedding from the complete closed
symmetric quarter interval to `[-1,1]`, with checked endpoint values and
strict increase. Exact surjectivity is now constructed by deterministic
arithmetic iteration `x(n+1)=x(n)+y-sin(x(n))`, starting at the left endpoint.
Sine's non-expanding estimate preserves the bracket and bounds the residual
by the interval width divided by the step number. The small-angle bound
`sin t >= t/2` produces an explicit rational closeness-reflection modulus.
Together these give native Cauchy data and an exact preimage by completeness.
`Pi/InverseValue.agda` exports `sinℝ-restrictedEquiv`,
`cosℝ-restrictedEquiv`, `arcSinℝ`, and `arcCosℝ` without supplied existence
data. Their inverse, endpoint, zero, parity, continuity, and weak/strict order
laws specialize the existing generic proofs. `inverseTrigRadius` is an
explicit uniform modulus, valid at the endpoints as well.

Finite slack-bisection remains an independent approximate density result;
it does not choose an infinite sequence. The rational-target completion and
conditional inverse APIs remain compatible, and
`characterizedHalfPi-sineIntermediateValue` supplies their formerly missing
interval witness. The HIT rational inverse-bisection theorem requires rational
endpoints and values and a positive lower slope; the native iteration avoids
these restrictions and uses no comparison between real carriers. General
exact IVT remains open, and the former countable-choice adapters remain
removed. See `Trigonometric/QuarterTurn/Restriction/README.md` for the proof.

The local logarithm series and global exponential equivalence are checked.
The global logarithm now has inverse, algebra, order, continuity, and derivative
laws without an equivalence hypothesis. Identifying it with the separate
series construction remains a compatibility target.

### Phase 8: native complex analysis and constructive FTA

The user explicitly added this scope on 2026-10-08. See
[Complex/README.md](Complex/README.md) for the precise statement, implementation,
and next proof obligations.

The [missing-layer plan](Complex/DEVELOPMENT_GAPS_2026-10-09.md) now adds a
native elementary-function layer: complex exponential, sine and cosine with
addition/Euler/parity/periodicity laws, real-axis agreement, positive exponential
modulus and continuity. Generic continuity also preserves supplied complex
sequence limits. Logarithms exist merely at each positively nonzero point,
and are constructed from supplied polar witnesses. The
[differential-calculus layer](Complex/Calculus/README.md) now proves general
complex derivative uniqueness, continuity, algebra/product/chain rules and
analytic correctness of the existing polynomial derivatives, with
holomorphic/entire interfaces. The exponential, sine and cosine now have
their expected complex derivatives and are proved entire, using the native
real derivative estimates and complex chain rules. The
[series layer](Complex/Series/README.md) now proves general sum laws, absolute
and uniform comparison, continuous power-series values from supplied radius
majorants, and the geometric-series theorem on the Euclidean unit disk.
Cauchy products now have finite algebra, native Mertens with one absolute
factor, absolute native Cauchy closure and a bound on the sum of norms.
Coefficient convolution multiplies power-series values and preserves a
supplied nonnegative radius majorant. Complex power-series differentiation
now follows from a supplied native derivative-majorant witness, with
continuous derivative values, uniform derivative estimates and endpoint
line integrals. Strict-interior convergence and holomorphicity now follow
from an original outer-radius norm-majorant witness, with constructed
derivative-series sums. Open norm-radius domains and a generic open-subspace
adapter give ambient derivative statements; interior paths have endpoint
integrals from the original witness alone. The existing exponential, sine
and cosine now agree with their standard complex series, with absolute native
convergence everywhere and uniform convergence on bounded families. The sine
and cosine endpoint integral formulas follow from the interior series FTC
for every certified uniform path. One original outer-radius witness now
constructs all finite derivatives, their uniform series sums and their
coherent derivative tower on smaller bounded families. Taylor coefficients
recover the original sequence; intrinsic open-ball Taylor representation is
uniform and has a majorant-tail remainder estimate. The elementary functions
have explicit derivative towers and Taylor series at every complex center.
Intrinsic open-subspace tower uniqueness proves local coefficient uniqueness.
One canonical derivative tower is now defined on the whole open convergence
ball; its Taylor coefficients at each interior center are independent of the
outer radius and agree with any supplied convergent reexpansion.
[General reexpansion](Complex/Series/PowerSeries/Translation.agda) now
constructs native convergence for `norm(center) + r < R`, represents the
original sum, and supplies uniform convergence and tail-remainder bounds.
The proof uses finite binomial translation and a common geometric majorant
before interchanging limits. Reexpansion preserves every derivative by
intrinsic tower uniqueness. The
[centered FTC](Complex/Integration/LineIntegral/PowerSeries/Centered.agda), its
[canonical Taylor application](Complex/Integration/LineIntegral/PowerSeries/Reexpansion.agda),
and [piecewise local-series FTC](Complex/Integration/Piecewise/PowerSeries.agda)
now give endpoint integrals and closed-path zero. Different pieces may use
different centers but must represent a common primitive.
[Constructed primitives](Complex/Series/PowerSeries/Primitive.agda) now
reuse the real formal-primitive coefficients and converge at the original
nonnegative majorant radius. Intrinsic uniform differentiation gives their
[path FTC](Complex/Integration/LineIntegral/PowerSeries/Primitive.agda) and
[finite-contour endpoint theorem](Complex/Integration/Piecewise/PowerSeries/Primitive.agda)
without a supplied ambient primitive. Next prove compatibility under Taylor
reexpansion and apply it to coherent differently centered local descriptions;
holomorphic Taylor representation without a supplied series remains separate. The [complex integration layer](Complex/Integration/README.md) now
proves an endpoint theorem for line integrals along bounded uniformly
differentiable paths, using a uniform primitive estimate along the curve.
It constructs the integral, proves path independence and closed-path
vanishing, and supplies polynomial-derivative applications from existing
Newton estimates. Finite piecewise contours now have concatenation,
reversal, and the telescoping endpoint theorem; actual smooth parameter
changes satisfy substitution under supplied standard uniform continuity.
Exponential primitives apply to every certified path. A supplied continuous
logarithmic lift yields its reciprocal integral as the lift's endpoint change,
and the explicit positive unit circle has value `2πi`. The
[right-half-plane logarithm](Complex/Transcendental/Logarithm/README.md) is
now constructed as an intrinsic continuous function with derivative `1/z`
and positive-real normalization. A positive rational lower bound on a
certified path's real part suffices for its reciprocal endpoint formula and
closed-path zero. Pointwise inverse differentiation and supporting modulus,
reciprocal and logarithm continuity reuse the native library. A general
compact C¹ upgrade, additional branch domains and Cauchy integral theory
remain future work.

The selected FTA target approximates any monic polynomial, at each requested
positive rational tolerance, by a finite product of linear factors. The
witness remains truncated separately at each tolerance. The target is proved
for every degree by `approximateFundamentalTheorem` in
[Complex/FundamentalTheorem/Approximate.agda](Complex/FundamentalTheorem/Approximate.agda).
The same module proves `approximatePolynomialRoots` for every positive degree.
There are no coefficient-apartness or root-separation hypotheses.

The native complex plane uses pairs of sequential reals and the product
premetric. The l1 norm supplies submultiplicative bounds and geometric
contraction proofs. Exact local roots and a unique small quadratic branch are
constructed with native sequence witnesses. Positive real higher roots use
the global exp/log equivalence. Nonnegative square roots use an explicit
geometrically Cauchy sequence and define the multiplicative Euclidean
modulus. Restricted arcsine and a finite rotated cover provide local polar
forms and truncated arguments away from zero; De Moivre's formula and
positive real roots then give higher complex roots. Approximate nth roots
exist at each requested tolerance for every input. Unit roots give optimal
two-term cancellation for positive-modulus coefficients. Monic vectors
retain degree without coefficient zero tests, translation recenters them,
and synthetic division keeps the remainder explicit.

Finite quantitative Kneser descent now has a checked coefficient-selection
construction: balanced weighted-power roots, a bounded finite near-maximum
chain, three adjacent equal indices, and a degree-dependent lower bound on
the selected term. With `q = 4^(-N)`, the bound `N*q ≤ 1/4` controls the
finite remainder by one quarter of the selected term plus an explicit
rational-slack allowance. Polynomial monomial expansion and selected-term
modulus bounds provide the algebraic interface.

The one-step theorem now combines that scale with angular cancellation and
one sufficiently small rational error. It gives the contraction factor
`1-L/8`, strictly between zero and one and depending only on degree.
Located order handles the small-constant case without a zero test.
`uniformPolynomialDescent`, finite translated iteration, geometric decay,
and the synthetic-deflation reduction complete the arbitrary-degree
approximate theorem. No infinite root or coefficient-index sequence is
selected. See the Complex README for the proof and exact choice boundary.

The finite-accuracy milestone and the completed-multiset extension below
are complete. General native exact FTA, the remaining power-series calculus
and Cauchy integral theory remain further layers. Winding remains an alternative proof route after a
Cartesian-circle bridge and homotopy-invariance proof. No Cartesian-circle
equivalence or argument principle is inferred from quotient-circle winding.

The [constructive FTA survey](Complex/FTA_SURVEY_2026-10-08.md) records
the preferred proof order: polynomial differential algebra and quantitative
local Newton roots; exact factorization for strongly separable polynomials
with positive Bézout certificates; quantitative matching; completed root
multisets. Presentation-sensitive exact FTA and projective formulations are
separate later targets. None of these extensions is claimed from the
radiuswise truncated approximate theorem alone.

The statement-first pass requested afterward is complete; the
[catalogue](Complex/FundamentalTheorem/Formulations/README.md) gives checked
types for the surveyed formulations and distinguishes proposed native
adaptations. Proofs have resumed: formal Bézout certificates now give
evaluation identities and derivative inverses at supplied roots, and
`localNewtonRoot` constructs an actual unique native root in a ball from the
specified Newton bounds. These bounds are now derived uniformly, using
Horner coercivity, two-point divided-difference estimates, and the Bézout
identity. Finite rational tolerance selection supplies one approximate center;
deterministic iteration constructs an exact native root.

`stronglySeparableRootExistence` and
`stronglySeparableFundamentalTheorem` now inhabit the catalogue's original
types. Formal coefficient certificates propagate through exact deflation by
`separableDeflation`; finite induction gives exact factorization into pairwise
apart roots. The polynomial-ring interpretation reflects equality back to
zero-extended coefficients, preserving the formal certificate.

Stage 4 is now also proved: `quantitativeRootMatching` and
`quantitativeFactorContinuity` give explicit rational moduli for the two
finite stability directions. Matching retains multiplicities and makes no
separability assumption. The native proof uses finite located search,
coefficient-level permutation identities, and uniform synthetic-division
estimates. The direct reverse reduction also completes
`approximateFormulationsInterderivable`. No infinite family of roots is
selected. Stage 5 now also supplies `completedMultisetFundamentalTheorem`:
the Gaussian-rational matching completion is constructed, and its factor map
is equivalent to all native monic coefficient vectors with whole local
moduli in both directions. Rational-coefficient existence uses explicit
enumeration and decidable least-witness search. Native coefficient induction
and reflection of entire Cauchy witnesses establish general existence;
radiuswise density is not turned into a chosen sequence. See the
[completion notes](Complex/FundamentalTheorem/Completion/README.md).
Stages 1–5 are complete. Stage 6 now proves `nearZeroNet` with the catalogue's
original finite Gaussian net and universal small-residual coverage fields.
The [cluster layer](Complex/FundamentalTheorem/Clusters/README.md) supplies
robust spectral certificates, openness and nonvacuity, separation of actual
roots, finite block matching, and a whole coefficient modulus for separated
blocks. The empty, single-cluster, and strongly separable exact cases are
proved. General separated factorization still needs persistent finite
partitions and exact factor construction in the native completion.
Weak FTA, presentation-sensitive exact roots, and projective roots remain
later clients. Unrestricted native exact FTA remains open.

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

1. Extend the new restricted sine/cosine inverses with inverse calculus and
   the Cartesian-circle bridge. General exact IVT remains separate;
   choice-based exact-inverse adapters are forbidden and remain removed.
2. Prove local exponential/logarithm compatibility and identify the total
   series candidate with the global logarithm. The choice-free global inverse
   and uniform local logarithm derivative estimates are now constructed.
3. Design a performant full-apart reciprocal derivative adapter and package
   bounded-domain rational functions.
4. Add the generic domain-map and pasting combinators demanded by calculus.
5. Extend integral existence to weaker radiuswise continuity/convergence
   hypotheses without choice; develop further closure laws and weaker FTC
   hypotheses beyond the checked bounded uniform calculus.

This queue deliberately alternates user-facing theorems with generic support
work so that no large specialized branch grows on a weak foundation.
