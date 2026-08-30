# Analysis on radiuswise Cauchy-sequence reals

This directory starts an analysis API for the reals constructed by
`Completion.CauchySequence`.  Its first layer recovers the foundational
sequence results of `HITs.CauchyReals` and `HITs.CauchyRealsP`, but states
them using the weaker, native Cauchy datum

```agda
∀ ε → ∥ Σ[ N ∈ ℕ ] CauchyTailAt ε N ∥₁.
```

Thus a caller never has to choose all tail indices simultaneously.

## Verification status

As of 2026-08-11, all 344 Agda modules below
`Completion.CauchySequence.Reals/` typecheck with `agda-codex`.  The final
sweep was dependency ordered, checked every module in a separate compiler
process, and imposed a 60-second cap per module.  It completed with no holes,
unsolved metas, unsolved constraints, failures, or timeouts.

## What is available

`Sequence.Base` provides the native Cauchy predicate, sequential limits,
constant and shifted sequences, preservation by continuous maps, and two
relations useful for changing a sequence without changing its limit:
eventual equality and radiuswise eventual closeness.

`Sequence.Operations` proves preservation of native Cauchyness and limits
by negation, absolute value, rational scalar multiplication, addition,
subtraction, multiplication, minimum, maximum, and every fixed natural
power.  `Polynomial` extends this by a finite Horner induction to polynomial
evaluation with real coefficients.

`Sequence.Order` defines propositionally truncated eventual non-strict and
strict order.  It proves that eventual non-strict order passes to limits and
derives the corresponding results for pointwise order and eventual bounds.
Eventual strict order yields only non-strict order between limits, since its
positive gaps can tend to zero.

`FiniteSum` proves that finite sums preserve native Cauchyness and limits.
It combines only finitely many radiuswise witnesses and therefore never
needs a simultaneous modulus.

`Series` develops partial sums, sums, native Cauchy series, scaling, dropped
prefixes, finite modification, finite-sum distance bounds, order bounds, and
absolute convergence.  It now also develops finite convolution, Cauchy
products, Mertens remainders, and their rectangular partial-sum
approximation.  In particular,

```agda
IsCauchySeries terms ≃ Summable terms
```

holds without choice.  Scaling preserves Cauchy and absolutely Cauchy
series for every real scalar, strengthening the rational-scalar statement
in the regular-real analysis API.  More generally, a pointwise majorant of
the termwise absolute values transfers Cauchyness and summability from the
majorant series to the original series.  The proof maps each already
truncated Cauchy tail independently; it never selects a modulus function.
The bounds layer proves that an absolutely Cauchy series merely has some
rational bound on all of its absolute partial sums.  The Mertens proof opens
such finite bounds only inside proposition-valued remainder estimates.  Thus
two absolutely Cauchy series have an absolutely Cauchy product and its sum is
the product of their sums, with no bounds or moduli exposed in the theorem.

`Series.Geometric` now contains the finite geometric identity, its reciprocal
form, conditional convergence and exact sum formulas, rational convergence,
rational-majorant comparison for arbitrary completed ratios, and scaled and
shifted geometric tails.  The core theorem exposes the exact condition

```agda
GeometricPowersTendToZero x
```

and, when `x < 1`, proves that it is equivalent both to summability and to
native Cauchyness of the geometric series.  For rational `q`, the arithmetic
development proves this condition from `abs q < 1`.  Its concrete modulus is
used only inside one requested-radius proof and is hidden again by the
native truncation boundary.  For arbitrary `x`, an exhibited positive
rational `q < 1` above `abs x` yields absolute Cauchyness, summability, and
the reciprocal sum formula.  More sharply, the public proposition-valued
theorems require only `abs x < 1`: rational density produces a merely
existing intermediate rational, and that truncation is eliminated directly
into Cauchyness, summability, or the uniquely determined sum statement.

`Series.PowerSeries` adds coefficient sequences, evaluation at a point,
addition and arbitrary-real scaling of summable power series, the
unit-coefficient geometric series, finite-support polynomial series, finite
modification of coefficients, coefficient majorants, and bounded-coefficient
convergence inside an exhibited rational contraction.  Bounded coefficients
also give absolute and ordinary convergence under the sharp hypothesis
`abs x < 1`, without exposing or selecting a rational contraction.  Polynomial power
series are proved summable directly from eventual stability of their partial
sums and their value is identified with the Horner evaluator.  The native
majorant API is slightly stronger than the older `CauchyRealsP` version:
`CoefficientMajorizedBy coefficients majorant` already implies that the
majorant coefficients are nonnegative, so callers do not supply that
redundant premise separately.

The power-series product layer identifies evaluation of the coefficient
convolution with the Cauchy product of the evaluated term series.  Its
low-level theorem takes the precise rectangular-approximation condition,
while the Mertens layer discharges it from absolute convergence.  For bounded
coefficients the resulting product is summable and has the expected product
value under the sharp hypotheses `abs x < 1`, without choosing intermediate
rational contraction bounds.

The eventually-geometric layer treats a finite polynomial prefix followed
by a scaled geometric coefficient tail.  With an explicit cutoff it gives
the exact prefix-plus-tail sum, and the polynomial specialization identifies
that prefix with Horner evaluation.  Its sharp variants assume only
`abs (ratio * x) < 1`; no rational contraction is exposed.  The corresponding
rational-function module proves that this power-series value is the partial
quotient with denominator `1 - ratio * x`, constructing denominator
apartness directly from the same open inequality.

Repeated Cauchy products of the unit coefficient sequence give the
iterated-geometric family.  The native absolute Mertens theorem makes this
construction stronger and simpler than its bound-indexed counterpart:
neither the induction nor its public value formula carries selected rational
sum bounds.  The coefficients are identified with simplex numbers and then
with binomial coefficients, with polynomial growth and nonnegativity proofs.
Their formal derivative is exactly `(order + 1)` times the next family, and
both the original and formal-derivative series converge uniformly on a
closed radius satisfying the sharp condition `abs radius < 1`.  Opaque
aliases seal the recursive Mertens witnesses at module boundaries so later
proofs do not repeatedly normalize them.

`Series.Uniform` uses the same truncation discipline for parameterized
families.  Its native definition is

```agda
∀ ε → ∥ Σ[ N ∈ ℕ ]
  (∀ x m n → N ≤ m → N ≤ n →
    partialSum (terms x) m ≈ᶜ[ ε ] partialSum (terms x) n) ∥₁.
```

The module also exposes the traditional chosen-modulus structure and the
map from it to the native predicate, but deliberately no converse.  Uniform
domination and uniform absolute convergence preserve the same common cutoff.
A native uniformly Cauchy family converges uniformly to its canonical
pointwise sum: one truncated cutoff is shared by all parameters, while each
pointwise limit witness is eliminated only into a closeness proposition.
Continuous terms therefore have a continuous uniform sum, again without
choosing a uniform modulus.

`Analysis.Metric.Radius` supplies closed absolute-value balls as premetric
subspaces, as well as open absolute-value balls and the inclusion of an open
ball into its closed counterpart.  `Series.PowerSeries.Uniform` proves uniform absolute convergence
on such a ball from a coefficient majorant, and in particular for bounded
coefficients on every embedded rational radius `q < 1`.  It gives the uniform
partial-sum theorem and continuity of the resulting power-series value.  As
in the pointwise majorant API, nonnegativity of a coefficient majorant is
derived rather than requested redundantly.

`Analysis.Derivative` provides a division-free derivative along any
real-valued coordinate on an arbitrary premetric parameter space.  It is
stable under continuous reparameterization, and a continuous divided
difference with the expected diagonal value supplies a derivative.  The
local radius at each requested error scale remains propositionally
truncated; no global derivative modulus is selected.  Constants, the
coordinate map, and every natural power have derivatives in this sense.
The algebra layer includes sums, differences, scalar multiples, the chain
rule, and the product rule, both ordinarily and along an arbitrary continuous
coordinate.  The chain proof consumes the merely existing rational bound
native to completed reals directly instead of converting it to a chosen
natural bound.  The product rule is derived by polarization from squaring;
this replaces the older direct three-error calculation and reuses the chain
and additive rules.  An indexed chain rule additionally handles an outer
function defined only on the same constrained parameter space.  This is the
right interface for reciprocal and quotient rules because it does not demand
an artificial ambient extension of a partial function.

Reciprocal differentiation is layered by constructive strength.  A fixed
positive rational lower bound first gives a globally Lipschitz reciprocal
and an untruncated quantitative derivative theorem.  On the full positive
subspace, a point's truncated gap is opened only to establish local
continuity; the derivative then follows from the global algebraic
difference-factor identity.  Negation transports this theorem to the
negative subspace, and local sign evidence glues continuity on apart reals.
The signed derivative again follows from one continuous difference factor,
rather than repeating positive and negative derivative-error estimates.

The quotient layer accepts a denominator valued in apart reals, or an
ordinary denominator equipped pointwise with apartness.  It derives both the
expanded product-rule derivative and a normalization-friendly form
`(f′g - fg′) * (g⁻¹ * g⁻¹)`.  This form carries exactly the usual
`(f′g - fg′) / g²` algebra while remaining the preferred computational
normal form.  Multiplicativity of signed inversion now proves that it equals
the conventional division-by-`g²` presentation.  Thus both derivative forms
and both derivative theorems are exposed without asking the checker to
renormalize the quotient-rule algebra from scratch.

`Derivative.RationalFunction` builds the corresponding partial-function
calculus on canonical apart-denominator domains.  A differentiable
denominator has an open natural domain, because the nonzero real predicate is
open and differentiability implies continuity.  Quotient values and their
normalized derivatives are explicitly proof-irrelevant in the apartness
witness.  Besides the relative derivative along the subspace coordinate, the
API therefore gives an ordinary derivative at every domain point for any
total extension agreeing with the partial quotient.

Binary sums and products live on the exact intersection of their denominator
domains.  Their pointwise definitions agree with the usual single-quotient
combined-denominator normal forms.  Composition uses a nested domain: the
inner denominator is apart at the input and the outer denominator is apart at
the inner quotient.  The outer condition is open relative to the inner
domain.  A flattened, proposition-valued version of the dependent domain is
also proved open in the base real line, yielding the same ambient-extension
derivative theorem for composed rational functions.  In these openness
proofs, the inner and outer radii are combined only inside propositional
truncation; neither a sign nor a uniform denominator gap becomes part of the
function data.

The algebraic support for this layer adds multiplicative apartness,
apartness of natural powers, and multiplicativity of signed inverse.  The
two-pole and double-reciprocal examples exercise domain transport,
composition, and the expected involutive value computation.

`Derivative.Polynomial` connects the finite Horner evaluator to calculus.  It
defines the weighted formal coefficient derivative, proves its evaluation
formula, constructs a division-free two-point difference factor, and obtains
the derivative and chain rules for polynomials.  Uniqueness identifies every
other proposed derivative value with that formal derivative.

`Derivative.OpenSubspace` turns a derivative along an open premetric
subspace into an ambient derivative at an interior point.  It offers both a
local extension theorem and the stronger direct theorem when an ambient
function is already available.  `Derivative.Interior` specializes this to
strictly interior points of closed absolute-radius balls.  The strict gap is
opened only while proving the proposition-valued local-neighbourhood claim.

The formal-derivative layer sends coefficients `a (suc n)` to
`(n + 1) * a (suc n)` and proves that coefficient majorization is preserved.
For bounded coefficients, its linear-growth majorant `(n + 1)q^n` is
identified with a scalar multiple of the Cauchy product of two geometric
series.  The absolute Mertens theorem therefore gives uniform absolute
convergence of the formal-derivative series on every positive rational
closed radius `q < 1`, without exposing a chosen modulus or requiring a
separate nonnegativity hypothesis.

The divided-difference layer now supplies that missing differentiation
theorem.  It proves the finite power identity without division, bounds the
two-variable factor series by the formal-derivative majorant, sums the finite
factorization, and obtains a continuous factor on the closed-radius product.
Thus the canonical uniform power-series value has the canonical uniform
formal-derivative value as derivative along the closed-radius coordinate.
For bounded coefficients, this conclusion is automatic on every positive
rational closed radius `q < 1`: the geometric/Mertens argument discharges
the original, derivative, and difference-factor convergence hypotheses.
`Series.PowerSeries.Interior` transports this result to an ordinary ambient
derivative at every strict interior point.  Its strongest majorant theorem
returns the derivative series' uniform-convergence witness together with the
derivative proof.  Keeping that computational witness in a dependent pair is
both stronger for later constructions and avoids hiding a reusable choice
behind truncation; the internally chosen tail cutoffs remain truncated.

`Series.PowerSeries.LocallyUniform` is the whole-line interface.  Its datum
asks for uniform Cauchyness on every positive rational closed ball.  Mere
Archimedean boundedness then proves pointwise summability, but the canonical
value does not choose or expose a ball.  Opaque agreement with each local
uniform sum makes downstream elaboration stable.  The derivative companion
eliminates a merely existing strict natural bound directly into the
proposition `IsDerivativeAt`, giving a global termwise differentiation
theorem.  Separate modules prove global continuity, additive and arbitrary
real-scalar closure, closure of the divided-difference hypotheses, and a
proposition-valued smooth derivative tower.  The smooth tower deliberately
requires an explicit proof family at all orders; it does not turn a family of
merely existing witnesses into countable chosen data.

The locally uniform radiuswise-continuity layer is stronger than pointwise
continuity on bounded domains.  Uniform-series limits preserve the interface

```agda
∀ ε → ∥ Σ[ δ ∈ ℚ₊ ]
  (∀ x y → x ≈ᶜ[ δ ] y → f x ≈ᶜ[ ε ] f y) ∥₁
```

without assembling a modulus function.  Powers are handled by bounded
multiplication on rational balls, and arbitrary real coefficients by opening
one scalar bound per error radius.  Consequently every locally uniform power
series is radiuswise uniformly continuous on every real closed interval: a
joint rational endpoint bound is opened only into that proposition.  This is
the regularity interface consumed by native Riemann integration.

`Analysis.Integration` builds sequential Riemann integration on the native
completion.  Radiuswise uniform continuity is the input interface, so a
function supplies an adequate input radius separately at each requested
output radius, under propositional truncation.  Equal partitions, mesh
estimates, Riemann-sum bounds, the sequential integral, and uniqueness and
linearity properties are all available without assembling a global modulus.

`RiemannIntegral.DyadicContinuous` specializes this construction to recursive
dyadic sums.  Radiuswise uniformly continuous functions give Cauchy dyadic
sum sequences and hence canonical completed integrals.  The result is
independent of the interval-order and continuity witnesses and is unique
among limits of the same dyadic sums.  Exact constant, addition, negation,
and arbitrary-real scaling laws are proved by first establishing identities
of the finite recursive sums and then using uniqueness in the completion.

`RiemannIntegral.DyadicUniformLimit` strengthens the construction with an
operator-norm estimate.  A pointwise absolute error on `[a,b]` increases a
dyadic sum by at most the interval width times that error, uniformly in the
subdivision depth.  Consequently the completed integral has a corresponding
metric stability theorem.  Interval-local uniform convergence is sufficient
for convergence of integrals when continuity of the limit is supplied;
global uniform convergence constructs that continuity witness automatically.
The integral sequence is then Cauchy in the native completion, and
`completedUniformIntegral-agrees` identifies its independently completed
value with the integral of the uniform limit.

`PowerSeries.Exponential` constructs the embedded reciprocal-factorial
series, proves absolute and locally uniform convergence on the whole line,
and defines the canonical `expℝ`.  The formal derivative is the original
coefficient sequence, so the locally uniform calculus gives
`expℝHasDerivativeSelf`.  The Cauchy-product/Mertens development and exact
factorial-binomial identities prove `expℝ (x + y) = expℝ x * expℝ y`
without selecting convergence bounds.  The order layer goes further: it
proves global positivity, reciprocal behavior under negation, quantitative
lower bounds, non-strict and strict monotonicity, reflection of order,
injectivity, and preservation of apartness.

`PowerSeries.Trigonometric` defines total `sinℝ` and `cosℝ` by even/odd
alternating transforms of the same factorial majorant.  Their series converge
locally uniformly and satisfy `sin′ = cos` and `cos′ = -sin`; the laws modules
supply values at zero, parity, addition formulas, the Pythagorean identity,
and the second-order equations `sin″ = -sin` and `cos″ = -cos`.  Tangent and
secant are defined on the open domain where cosine is apart from zero.  Their
derivatives, parity, value at zero, and tangent addition formula are expressed
on exact proof-irrelevant domains rather than through a totalized inverse.

`PowerSeries.Hyperbolic` defines total `sinhℝ` and `coshℝ` from `expℝ x`
and `expℝ (-x)`.  It proves parity, addition and subtraction formulas,
`sinh′ = cosh`, `cosh′ = sinh`, the self second-derivative equations, the
fundamental difference-of-squares identity, double-angle and product-to-sum
identities, and the canonical solution with arbitrary initial value and
slope.  The polynomial parts of these proofs are bundled as reusable generic
commutative-ring identity shapes and specialized to the completed reals only
once.

`PowerSeries.Logarithm` develops the negative-log-one-minus series and
identifies its formal derivative with the reciprocal geometric series on
closed radii strictly inside the unit ball.  `PowerSeries.Arctangent` develops
the alternating odd series, proves uniform convergence of its derivative
series on such radii, identifies that derivative with the reciprocal of
`1 + x²`, and exposes the resulting derivative theorem.  These constructions
reuse the generic power-series and completion interfaces rather than proving
each analytic estimate directly from expanded partial sums.

The principal strengthening is

```agda
IsCauchySequence x ≃ SequenceLimit x
```

for real-valued sequences.  The forward direction uses the native limit
constructor; the reverse direction uses the triangle law.  This equivalence
does not select a modulus: both sides are propositions and all radiuswise
tail witnesses remain truncated.

At the algebraic boundary, arbitrary real translation has now been packaged
as a nonexpanding map in either addition argument.  This yields the exact
metric/order equivalence

```agda
(x ≈ᶜ[ ε ] y) ≃ (absℝ (x - y) <ℝ ιℚ (fst ε))
```

for the sequence-completion reals.  Its converse is what makes order
majorants usable as primitive Cauchy estimates.  The proof first handles a
closed absolute bound at a strictly smaller rational radius and eliminates
rational density only into a proposition.

## Truncation discipline

The API follows three rules.

1. A cutoff is truncated when later code only uses its existence to prove a
   proposition.  This applies to eventual equality and eventual order.
2. A uniquely determined mathematical output is not needlessly truncated.
   A sequence limit is an actual real together with its convergence proof,
   because separatedness makes that entire type a proposition.
3. The implementation never silently exchanges `∀ ε → ∥ A ε ∥₁` with
   `∥ ∀ ε → A ε ∥₁`.  The latter supplies one globally chosen modulus;
   obtaining it from the former is precisely the tail-choice principle
   isolated by the comparison modules.

Uniform convergence adds one important refinement: the common cutoff over
the parameter space lies inside the truncation, but outside the universal
quantifier over parameters.  Moving it inside that quantifier would weaken
uniform convergence to pointwise convergence; moving truncation outside the
radius quantifier would choose a global modulus.

Consequently, continuity preserves native Cauchy sequences of these reals:
first take their real limit, use sequential continuity, and then observe
that every convergent sequence is native Cauchy.  This argument depends on
completeness of the domain and is not a theorem about continuous maps from
arbitrary incomplete premetric spaces.

The low-level Cauchy-graph proofs used to define real operations remain
necessary.  Deriving their continuity from those operations and then using
continuity to justify the defining lift would be circular.  Once an
operation and its computation rules exist, however, the public unary
sequence theorems are obtained through continuity.  Multiplication and
maximum retain their synchronized constructor-level construction proofs;
maximum still lacks a separate continuous binary-map package.  Addition has
its separate nonexpanding package: the one-sided limit rule is recovered by
uniqueness of the binary Cauchy graph, and proposition-valued induction lifts
rational translation invariance to arbitrary reals.

Multiplication now has a separate continuity package as well.  Multiplication
by a real with an exhibited rational absolute bound is Lipschitz; joint
continuity obtains a merely existing local rational bound and eliminates it
inside the proposition-valued continuity statement.  This supports generic
closure of continuous functions under products and proves continuity of all
fixed natural powers.  These results justify public sequence and
power-series continuity theorems after multiplication has been constructed;
they do not replace its non-circular constructor-level Cauchy-graph proof.

Several expensive downstream identities cross an explicit normalization
boundary.  Small `Sealed` modules expose opaque agreements for completed-real
addition, multiplication, negation, inverse, order, and derivatives.  Generic
polynomial identity records are proved over an abstract commutative ring and
transported through those agreements once.  This is not an additional axiom
or a weakened transparency option: it is a proof architecture that prevents
the checker from repeatedly unfolding Cauchy-sequence lifts while retaining
the public real operations and theorems.

Finite modification illustrates a further distinction.  Mere eventual
equality is sufficient to preserve Cauchyness and summability, so its cutoff
is hidden.  The numerical correction formula mentions a particular cutoff;
the API therefore offers an untruncated formula when a cutoff is supplied,
and otherwise returns the cutoff together with the formula under one
propositional truncation.  It never projects an index out of mere existence.

The affine geometric and power-series finite-modification APIs make the same
distinction.  An explicit starting index gives an untruncated formula
consisting of the finite prefix plus the modified tail.  If only the mere
existence of such an index is available, summability is still returned
directly because it is a proposition, while the cutoff-dependent sum formula
remains under one propositional truncation.

The geometric-tail bridge illustrates a complementary strengthening.  A
rational contraction witness is useful quantitative data, but the exact
series value and the denominator's positivity need only the proof-irrelevant
condition `abs (ratio * x) < 1`.  The strongest theorem therefore avoids
eliminating a truncation altogether: it derives `ratio * x < 1` directly and
uses the already proposition-valued sharp convergence theorem.  This keeps
the public rational function point untruncated without selecting a modulus.

## Choice boundary and next steps

The native condition is sufficient for forming limits and for all results
in this directory.  It does not yield even the mere existence of a single
chosen modulus without a countable tail-choice principle.  Similarly, a
construction that must return countably many untruncated witnesses cannot
generally eliminate the radiuswise truncations.  The exploratory module
`Reals.Dirty.MapsBaseCauchySequences` records this obstruction for lifting
base maps.

Natural next layers are to connect the primitive power-series theorems with
the completed dyadic integral through a fundamental theorem of calculus, to
extend logarithm and arctangent from their initial power-series domains by
functional equations and exact open-domain transport, and to develop the
period and inverse-function interfaces needed for global trigonometry.
Completeness results for closed-radius subspaces and further interval/pasting
theorems would make those transports more reusable.  Quantitative sum and
integral bounds can be layered on the present qualitative results without
changing their truncation strength.  New definitions should continue to
consume radiuswise or otherwise local truncated evidence unless their output
is proposition-valued or uniquely determined, and should isolate completed
operation normalization behind small reusable agreements when a generic
algebraic construction is available.
