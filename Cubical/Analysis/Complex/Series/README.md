# Native complex series

The public `Cubical.Analysis.Complex.Series` facade extends the native complex
sequence and differential-calculus layers. Its carrier remains a pair of
Analysis's sequential reals. All sums and convergence data use the existing
real series and sequence APIs.

## Constructive boundary

`partialSumℂ terms n` is the pair of the existing real partial sums of the
first `n` coordinates. `HasComplexSum terms value` is their existing complex
limit predicate. `ComplexSummable terms` packages the value and this proof;
uniqueness makes the package a proposition, and `seriesSumℂ` projects the
value independently of the supplied proof.

`IsComplexCauchySeries` supplies two global native Cauchy witnesses, each
under a single truncation. It constructs an actual sum. Ordinary summability
is kept separate: no theorem manufactures a global modulus from independently
truncated tail bounds.

`ComplexAbsolutelySummable` is ordinary real summability of `normℂ ∘ terms`.
`IsComplexAbsolutelyCauchySeries` supplies the stronger native Cauchy witness
for that real norm series. The latter constructs a complex sum. Bounds on an
already supplied complex sum need only a supplied sum of the majorant.

## Implemented interfaces

| Module | Results |
| --- | --- |
| [Base](Base.agda) | Coordinate partial sums; sums, uniqueness and proposition proofs; native Cauchy completeness; coordinate summability bridges; summable terms tend to zero |
| [Operations](Operations.agda) | Finite and infinite addition, subtraction, negation, complex scaling and conjugation; proof-independent sum equations |
| [Tails](Tails.agda) | Tail partial-sum identities, preservation of native Cauchy data, forward and reverse summability, reconstruction from a finite prefix and its tail |
| [Bounds](Bounds.agda) | Finite l1 norm majorants and bounds on supplied sums |
| [Absolute](Absolute.agda) | Dominated and absolute native Cauchy convergence; equivalence with absolute convergence of both coordinates; absolute summability; norm and tail-remainder bounds |
| [Uniform](Uniform.agda) | Uniform coordinate Cauchy data, uniform sums, parameter restriction, uniform comparison, agreement with pointwise sums and continuity of sums of continuous terms |
| [PointwiseLimit](PointwiseLimit.agda) | Pointwise limits preserve a common native series modulus; uniform summation commutes with pointwise sequence limits, through the real theorems |
| [FiniteSupport](FiniteSupport.agda), [Double/Finite](Double/Finite.agda) | Sums of explicitly finite-support sequences; triangular and anti-diagonal finite reindexing |
| [PowerSeries/Translation](PowerSeries/Translation.agda) | General reexpansion at interior centers: binomial coefficients, exact finite translation, native convergence, canonical representation, uniform sums, tail bounds and compatibility of every derivative |
| [PowerSeries/Base](PowerSeries/Base.agda), [Bounds](PowerSeries/Bounds.agda), [Convergence](PowerSeries/Convergence.agda) | Complex coefficient series, finite term laws and continuity; l1 power bounds; absolute and uniform convergence from a supplied real radius-majorant witness; continuous values along bounded continuous coordinates |
| [Product](Product.agda) | Finite convolution laws, coordinate formulas, singleton/unit laws; native Mertens with one absolutely convergent factor; absolute native Cauchy closure and a bound on the sum of norms |
| [PowerSeries/Product](PowerSeries/Product.agda), [Product/Bounds](PowerSeries/Product/Bounds.agda) | Coefficient convolution evaluates as series multiplication; convergence and sum equations; preservation of a supplied nonnegative radius majorant without shrinking the radius |
| [PowerSeries/Difference](PowerSeries/Difference.agda), [Bounds](PowerSeries/Difference/Bounds.agda), [Sum](PowerSeries/Difference/Sum.agda) | Division-free monomial factors; formal derivative coefficients; shared real majorant; exact factorization of supplied sums and diagonal identification |
| [PowerSeries/Derivative](PowerSeries/Derivative.agda), [Uniform](PowerSeries/Derivative/Uniform.agda) | Complex differentiation of supplied or canonical power-series sums along bounded continuous coordinates; uniform derivative estimates along radiuswise uniformly continuous coordinates |
| [Uniform/Continuity](Uniform/Continuity.agda) | Radiuswise uniform continuity of sums of uniformly continuous terms, reusing the real uniform-tail theorem |
| [Geometric](Geometric.agda) | Finite geometric identity, absolute native Cauchy convergence on the full Euclidean unit disk, and the exact equation `(1-z) * sum = 1` |

Uniform Cauchy data supplies one modulus per coordinate valid across the
whole parameter space, with each modulus under truncation. It is not derived
from separate pointwise moduli. Uniform sums use the native real uniform-limit
theorem; continuity follows coordinatewise. Parameter spaces and continuous
coordinate maps remain explicit, so no new ball or open-subspace machinery is
needed.

For a power series `a[n] z^n`, the comparison series is
`normℂ(a[n]) * R^n`. A native Cauchy witness for this real series gives absolute
convergence at every point satisfying `normℂ z ≤ R`, uniform convergence on
any supplied family with that bound, and continuity along continuous
coordinates. These are l1 radius bounds. The geometric-series theorem uses
the existing multiplicative Euclidean modulus and therefore covers the whole
usual unit disk `modulusℂ z < 1`. It now supplies absolute native Cauchy
data on that whole disk as well, using the coordinate characterization above,
so it is directly available as the absolute factor in Mertens.

## Products and their hypotheses

`cauchyProductℂ a b n` sums `a[k] * b[n-k]` for `0 ≤ k ≤ n`. Its
coordinate formulas use the existing four real convolutions. The finite API
proves commutativity, distributivity, scalar and conjugation compatibility,
and multiplication by a singleton or the degree-zero unit sequence. It also
reuses real finite-interval reversal and bounded pointwise equality.

`mertensCauchyProductℂHasSum` takes absolute native Cauchy data for `a`,
native Cauchy data for `b`, and supplied sums `x,y`; the product has sum
`x*y`. The right-absolute variant exchanges the factors. This is stronger
than requiring both factors to converge absolutely. Its proof is four
applications of `Real.Series.Product.Native` followed by the real sum
algebra. It does not obtain a native witness from ordinary summability.

When both factors supply absolute native Cauchy data,
`cauchyProductℂIsAbsolutelyCauchy` preserves that stronger data. The bound
`normℂ(product[n]) ≤ cauchyProduct(normℂ ∘ a)(normℂ ∘ b)[n]` transfers the
sealed real absolute-product theorem. `cauchyProductℂAbsoluteSumBound`
then bounds the sum of product norms by the product of the two norm sums.

For power series, `powerSeriesTermsℂ-cauchyProduct` is a finite identity
valid at every complex argument. It combines the generic ring power and
interchange laws with finite reindexing; it needs no convergence hypothesis.
`powerSeriesCauchyProductℂHasSum` and `powerSeriesValueℂ-cauchyProduct`
transfer Mertens to coefficient multiplication, with explicit supplied sums.
Absolute native convergence is also preserved at each argument.

`complexPowerSeriesProductMajorantIsCauchy` preserves the full radius
hypothesis: at any supplied nonnegative radius `R`, native Cauchy witnesses
for `normℂ(a[n])*R^n` and `normℂ(b[n])*R^n` yield one for the product
coefficients at the same `R`. Thus the existing uniform-convergence and
continuity theorems apply to coefficient products directly. Its proof uses
the existing real power-series product identity; no real estimate is copied.

## Reuse and next proofs

Finite coordinate algebra reuses `Real.Series.Base` and `Operations`; tails
reuse `Real.Series.Tails`; comparison reuses `Real.Series.Absolute`; uniform
convergence and continuity reuse `Real.Series.Uniform`. The geometric proof
reuses the existing `modulusℂ-power` theorem from the polynomial expansion
layer. Its finite identity is proved over an abstract commutative ring from
the supplied partial-sum zero/step equations; the existing ordered-ring
geometric theorem cannot be instantiated at the complex ring.

The power norm bound is proved with the ring and size map abstract, then
instantiated at `normℂ`. This avoids expanding completed coordinate arithmetic
during the natural-number induction.

## Differentiation and line integrals

`formalDerivativeℂ a n` is `(n+1) * a[n+1]`, using the native real
natural-number embedding. The shared derivative majorant is
`normℂ(a[n+1]) * ((n+1) * R^n)`. A supplied native Cauchy witness for this
real series constructs the uniformly convergent divided-difference series
and the derivative series on any family with `normℂ z ≤ R`.

`complexPowerSeriesHasFormalDerivativeAlong` accepts supplied sums `f,d` of
the original and derivative series and a continuous bounded coordinate. It
proves the existing complex-linear derivative predicate. The canonical
version `uniformComplexPowerSeriesHasFormalDerivative` additionally consumes
the original radius-majorant witness and constructs both values. The
constructed derivative is continuous. These are relative derivative theorems
on the supplied domain; no open-disk or full-plane extension is implicit.

`complexPowerSeriesHasUniformFormalDerivativeAlong` strengthens the conclusion
to the radiuswise uniform derivative when the coordinate is radiuswise
uniformly continuous. Joint uniform continuity of the factor follows from
bounded finite-term estimates and the existing real uniform-sum theorem.
No separately truncated radii are converted to a global modulus.

The [line-integral application](../Integration/LineIntegral/PowerSeries.agda)
proves `∫γ f dz = F(γ(b)) - F(γ(a))` when `F,f` have the respective sums
along a certified path inside the supplied l1 radius. The derivative
majorant also bounds `f` on the path, so integrability is a conclusion.
Closed paths give zero. The original sum need only be supplied along the
path; no global power-series definition or choice of extension is assumed.

The [interior convergence theorem](PowerSeries/InteriorConvergence.agda)
now derives the derivative-majorant witness at every specified `0 ≤ r < R`
from the native ORIGINAL norm-majorant witness at `R`. It reuses a
[real finite secant bound](../../Real/Series/PowerSeries/Difference/InteriorBound.agda),
`(R-r)(n+1)r^n ≤ R^(n+1)`, and the existing rational scaling, tail and
comparison theorems. One truncated positive gap suffices; there is no
countable selection of convergence moduli.

[Interior differentiation](PowerSeries/Interior.agda) gives both relative
and uniform derivative estimates on bounded coordinate families, and an
ambient derivative theorem on the open outer norm radius. The
[holomorphicity theorem](PowerSeries/Interior/Holomorphic.agda) needs only
original sums representing an ambient function there: it constructs the
unique derivative value together with its formal-derivative series sum.
No derivative function or derivative-series convergence hypothesis is needed.
The open domains use the l1 norm, not the Euclidean modulus. An ambient
extension of an intrinsic sum is not constructed.

The [interior FTC application](../Integration/LineIntegral/PowerSeries/Interior.agda)
now requires only the original majorant at `R` when the path image has a
supplied bound `normℂ γ(t) ≤ r < R`. Original and derivative sums are supplied
along the path; uniform differentiation, an integrand bound, integrability,
the endpoint formula and closed-path zero follow.

## Elementary complex power series

The [coefficient API](PowerSeries/Elementary/Coefficients.agda) embeds the
existing real factorial and trigonometric coefficient sequences. Its formal
derivative identities are `D exp = exp`, `D sin = cos`, and `D cos = -sin`.
The [convergence module](PowerSeries/Elementary/Convergence.agda) reuses the
real factorial comparison to supply native absolute Cauchy witnesses at every
complex argument and radius-majorant witnesses at every nonnegative radius.

[Exponential/HasSum](PowerSeries/Exponential/HasSum.agda) identifies the
existing polar exponential with this series. The real-axis sum is the native
real exponential; on the imaginary axis, each term is the pair of the native
cosine and sine terms. The finite binomial theorem and native Mertens theorem
combine the two axes. Factorial/binomial arithmetic is reused from the real
trigonometric addition development; finite rearrangements are checked over
an abstract commutative ring before instantiation at the completed carrier.

[Trigonometric/HasSum](PowerSeries/Trigonometric/HasSum.agda) identifies the
existing complex sine and cosine by applying their Euler formulas termwise.
The full real coefficient masks retain their zero entries, so no infinite
even/odd reindexing is required. Each function has a `HasComplexSum` theorem,
a summability package, and a value equation for any supplied sum witness.
[Uniform convergence](PowerSeries/Elementary/Uniform.agda) holds on any family
with a supplied nonnegative l1 radius bound, to these same existing functions.

The generic [real embedding](PowerSeries/RealEmbedding.agda) reuses the
existing embedded-power identity. [Rescaling](PowerSeries/Rescaling.agda)
transfers argument scaling into coefficient scaling. These do not introduce
a second completion or infer native moduli from radiuswise truncated tails.
The [trigonometric line-integral application](../Integration/LineIntegral/Trigonometric.agda)
uses these sum identities with the strict-interior FTC, deriving its radius
margin from the existing path-image bound.

## Repeated derivatives and Taylor representation

[RepeatedDerivative](PowerSeries/RepeatedDerivative.agda) reuses the existing
real repeated formal derivatives coordinatewise, including their natural
coefficient multipliers. Its successor equation identifies this with the
existing complex formal derivative. Iteration composition, negation and
commutation with one further derivative are proved.

[RepeatedDerivative/Convergence](PowerSeries/RepeatedDerivative/Convergence.agda)
constructs a native radius-majorant witness for **every finite derivative
order** at each specified `0 ≤ r < R` from the original witness at `R`.
Finite induction applies the one-derivative interior theorem across an
intermediate rational radius. Each truncation is eliminated into the
proposition of native Cauchy data; no family of selected tail moduli is made.

[RepeatedDerivative/Tower](PowerSeries/RepeatedDerivative/Tower.agda)
constructs all derivative values on a bounded coordinate family, together
with their uniform series sums. Differentiating order `n` gives order `n+1`;
each derivative is continuous when the coordinate is continuous. Radiuswise
uniform continuity of the coordinate gives uniform derivative estimates at
every order. Only the original outer-radius witness is an input.
The [calculus tower API](../Calculus/Derivative/Tower.agda) also proves
uniqueness of ambient derivative towers from their order-zero function.

[Taylor/Coefficients](PowerSeries/Taylor/Coefficients.agda) defines Taylor
coefficients as `1/n!` times the supplied derivative value. The inverse
factorial is the existing real exponential coefficient embedded in ℂ.
Repeated-derivative sums at zero recover the original coefficient sequence
exactly. This reuses the real exponential's coefficient fixed point rather
than duplicating factorial identities.

[Taylor/Interior](PowerSeries/Taylor/Interior.agda) packages an actual
intrinsic derivative tower on an open l1 ball `r`, for `0 < r < R`, and proves
that the Taylor series of its order-zero function converges uniformly there
to that function. Its Taylor remainder is bounded by the corresponding tail
of the original summable norm-majorant at `R`. The supplied power-series
representation is essential: this does **not** prove that every holomorphic
function has a Taylor representation.

[Elementary/HigherDerivative](PowerSeries/Elementary/HigherDerivative.agda)
identifies all repeated exponential/sine/cosine coefficient-series sums with
their explicit [ambient derivative towers](../Transcendental/HigherDerivative.agda).
The exponential is its own derivative at every order; sine and cosine have
their four-cycles. [Taylor/Elementary](PowerSeries/Taylor/Elementary.agda)
gives the Taylor representations at zero for all three functions and the
exponential representation at every complex center.

[Taylor/Elementary/Translation](PowerSeries/Taylor/Elementary/Translation.agda)
now gives sine and cosine Taylor representations at every complex center
and every complex increment. Their coefficients are identified using the
[addition laws for every derivative](../Transcendental/HigherDerivative/Addition.agda),
normalization at zero, and the existing series sum operations.
[PowerSeries/Operations](PowerSeries/Operations.agda) exposes coefficientwise
addition, subtraction and scaling of supplied power-series sums.

## Local uniqueness and arbitrary-center coefficients

[Open-subspace derivative uniqueness](../Calculus/Derivative/OpenSubspace/Uniqueness.agda)
and [tower uniqueness](../Calculus/Derivative/Tower/OpenSubspace.agda) apply
to intrinsic functions, without ambient extensions. Subtracting two
estimates reduces the proof to the ambient zero function and reuses existing
uniqueness. The general open-subspace adapter now also supports relative
coordinates and an estimate at just one point.

[Taylor/Uniqueness](PowerSeries/Taylor/Uniqueness.agda) identifies a convergent
series' coefficients with the normalized values of **any** derivative tower
representing its order-zero function. Consequently two series representing
the same function on a common positive open ball have equal coefficients.
Their outer convergence radii and native witnesses may differ. These are
local representation hypotheses; equality at a single point is insufficient.

[RepeatedDerivative/Interior](PowerSeries/RepeatedDerivative/Interior.agda)
constructs one coherent derivative tower on the **whole open outer ball**.
Each point uses its explicit norm as a convergence radius. Local estimates
use a single intermediate rational radius and the relative open-subspace
adapter. Every order is continuous and has its formal-derivative series sum.
This does not assert uniform convergence up to the outer boundary.

[Taylor/Center](PowerSeries/Taylor/Center.agda) constructs normalized
coefficients at every interior center and proves that each coefficient is
the sum of the normalized formal-derivative series there. The coefficients
are independent of the chosen outer radius and witness, and at zero they
recover the original sequence.

[Taylor/Reexpansion](PowerSeries/Taylor/Reexpansion.agda) identifies any
**supplied convergent reexpansion** with these canonical coefficients. A
translated inner ball fits whenever `norm(center) + inner ≤ outer`; its
derivative tower is obtained by continuous pullback and invariance under
coordinate translation. The representation premise is still required.

## General reexpansion

[Translation](PowerSeries/Translation.agda) completes these steps for an
arbitrary supplied native power series. Writing `b[n]` for its canonical
Taylor coefficient at `center`, the main results are:

- [Coefficient normalization](PowerSeries/Translation/Coefficients.agda)
  identifies the normalized repeated-derivative multiplier with
  `choose(k+n,n)`. The existing exponential fixed-point and divided-factorial
  identities supply the factorial arithmetic.
- [Finite translation](PowerSeries/Translation/Finite.agda) rewrites the
  first `N` original terms exactly as a polynomial in the increment. Its
  coefficient `n` uses the row cutoff `N-n`. For each fixed `n`, these
  coefficients [converge to `b[n]`](PowerSeries/Translation/Approximation.agda).
- [Native convergence](PowerSeries/Translation/Convergence.agda) constructs
  `IsCauchySeries (complexPowerSeriesMajorant b r)` whenever `0 ≤ r` and
  `norm(center) + r < R`, from the original witness at `R`.
- [Representation](PowerSeries/Translation/Representation.agda) proves
  `sum b[n] * increment^n = sum a[n] * (center + increment)^n` under the
  corresponding strict radius condition. The
  [canonical specialization](PowerSeries/Translation/Canonical.agda) uses
  the already constructed original sum and needs no extra representation
  premise.
- [Uniform representation and remainder bounds](PowerSeries/Translation/Uniform.agda)
  apply to every family of increments with `norm(increment) ≤ r` and
  `norm(center) + r < R`. The remainder is bounded by the tail sum of the
  constructed native majorant for `b` at `r`.

The convergence proof first bounds all finite translated coefficients at
one larger radius. The reusable real
[weighted-bound theorem](../../Real/Series/PowerSeries/WeightedBound.agda)
then supplies a geometric majorant at the target radius. A single radius
gap and a single rational bound from the original native witness are
eliminated under propositional truncation. The real
[pointwise-limit theorem](../../Real/Series/PointwiseLimit.agda) transfers the
common modulus to the limiting coefficients and justifies interchange of
the polynomial limit with the series sum. Bounded monotone convergence and
countable choice are not used.

[Derivative compatibility](PowerSeries/Translation/Derivatives.agda) now
identifies the whole reexpanded derivative tower with the translated original
tower, using intrinsic open-subspace uniqueness. Every differentiated Taylor
series therefore represents the corresponding original derivative.

The [centered FTC](../Integration/LineIntegral/PowerSeries/Centered.agda)
works with local expansions in `z-center` and bounds
`norm(γ(t)-center) ≤ r < R`. The
[reexpansion application](../Integration/LineIntegral/PowerSeries/Reexpansion.agda)
constructs those local series from one original outer majorant and
`norm(center)+r<R`. Finite piecewise paths may use different centers on each
piece, provided their sums represent the same primitive and derivative.

[Constructed primitives](PowerSeries/Primitive.agda) now reuse the real
formal-primitive coefficients in both coordinates. The formal derivative
recovers the original sequence; its derivative majorant equals the original
majorant. Native absolute convergence therefore gives both a convergent
primitive and its uniform derivative at the same nonnegative radius.
[Domain values](PowerSeries/Primitive/Domain.agda) construct the primitive
on the closed norm ball, normalized to the supplied constant at zero.
Differentiation here is intrinsic to chords within the domain.

The convergence proof uses exact norms for multiplication by real scalars,
coefficient division by positive naturals and the reusable real
[successor-series lemma](../../Real/Series/Successor.agda). The latter restores
an initial term by shifting an explicit native Cauchy modulus. Finite
truncated bounds are eliminated into propositions; no countable choices of
tails are assembled.

The [path FTC](../Integration/LineIntegral/PowerSeries/Primitive.agda) and
[finite-contour theorem](../Integration/Piecewise/PowerSeries/Primitive.agda)
now integrate any represented series in its centered closed convergence
ball without a supplied ambient primitive. Next establish compatibility
between these normalized primitives and Taylor reexpansion.

General Taylor representation from holomorphicity alone remains separate.
The pointwise C¹-to-uniform upgrade and Cauchy integral theory also remain
open.

## Reexpansion validation

Reexpansion validation: all 25 changed Agda files (19 new modules, five
facade updates and one comment update) and both Analysis entrypoints pass
`agda-codex` with exit code 0 after their final edits. All 418 audited
complex/support/root snapshots match current sources and report zero holes,
metas, constraints and warnings. All 902 Analysis modules are reachable
(1,303 transitive Cubical modules), with no missing imports, orphans,
cycles, choice dependencies, alternate real carriers or source flags.
All 315 audited local documentation links resolve; whitespace checks pass.

## Series-foundation checkpoint validation

- All 15 new or edited Agda files (14 new modules and the Complex facade)
  pass `agda-codex` with exit code 0 after the final edits.
- Both `Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` pass
  after integration of the series exports.
- All 268 audited complex/root source snapshots match current files and
  report zero holes, unsolved metas, constraints and warnings.
- The import audit reaches all 757 native Analysis modules and 1156 Cubical
  modules transitively. There are no missing imports, orphan Analysis
  modules, cycles or Cauchy-real/choice dependencies. Source assumption and
  whitespace checks are clean.
- All 133 local links in the six updated development/progress documents
  resolve, and `git diff --check` passes.


## Product checkpoint validation

- All ten new or edited Agda files (six new modules and four updates) pass
  `agda-codex` with exit code 0 after their final edits.
- The public Complex facade, `Cubical/Analysis/Everything.agda` and
  `Cubical/Analysis.agda` also pass with exit code 0.
- All 274 audited complex/root source snapshots match current files and
  contain zero holes, unsolved metas, constraints and warnings.
- The import audit reaches all 763 native Analysis modules and 1162 Cubical
  modules transitively, with no missing imports, orphan Analysis modules,
  cycles or Cauchy-real/choice dependencies. Source assumption and whitespace
  checks are clean.
- All 142 local links in the six updated documentation files resolve;
  `git diff --check` passes.

## Power-series differentiation checkpoint validation

All 16 changed Agda files (12 new modules and four facade updates) pass
direct `agda-codex` checks after their final source edits. Both
`Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` pass with exit
code 0. All 355 audited complex/supporting and entrypoint snapshots match
current sources and contain no holes, unsolved metas, constraints or warnings.

The import audit reaches all 841 native Analysis modules and 1,242 Cubical
modules transitively, with no missing imports, orphan modules, cycles,
choice imports or Cauchy-real imports. The source audit finds no postulates,
holes or new option pragmas. All 227 local links in the eight audited
progress/development documents resolve; `git diff --check` passes.
Validation completed on 2026-10-10.


## Strict-interior checkpoint validation

All 15 changed Agda files (nine new modules and six facade updates) pass
direct `agda-codex` checks after their final source edits. Both
`Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` pass with exit
code 0. All 365 audited complex/supporting and entrypoint snapshots match
current sources and contain no holes, unsolved metas, constraints or warnings.

The import audit reaches all 850 native Analysis modules and 1,251 Cubical
modules transitively, with no missing imports, orphan modules, cycles,
choice imports or Cauchy-real imports. Source checks find no postulates,
holes or new option pragmas. All 240 local links in the eight audited
progress/development documents resolve; `git diff --check` passes.
Validation completed on 2026-10-10.


## Elementary-series checkpoint validation

All 14 changed Agda files (12 new modules and two facade updates) pass direct
`agda-codex` checks after their final source edits. Both
`Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` pass with exit
code 0. All 377 audited complex/supporting and entrypoint snapshots match
current sources and contain no holes, unsolved metas, constraints or warnings.

The import audit reaches all 862 native Analysis modules and 1,263 Cubical
modules transitively, with no missing imports, orphan modules, cycles,
choice imports or Cauchy-real imports. Source checks find no postulates,
holes or new option pragmas. All 255 local links in the eight audited
progress/development documents resolve; `git diff --check` passes.
Validation completed on 2026-10-10.


## Higher-derivative and Taylor checkpoint validation

All 13 changed Agda files (ten new modules and three facade updates) pass
direct `agda-codex` checks after their final source edits. Both
`Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` pass with exit
code 0. All 387 audited complex/supporting and entrypoint snapshots match
current sources and contain no holes, unsolved metas, constraints or warnings.

The import audit reaches all 872 native Analysis modules and 1,273 Cubical
modules transitively, with no missing imports, orphan modules, cycles,
choice imports or Cauchy-real imports. Source checks find no postulates,
holes or new option pragmas. All 269 local links in the eight audited
progress/development documents resolve; `git diff --check` passes.
Validation completed on 2026-10-10.

## Local uniqueness and expansion-center validation (2026-10-11)

Validation: all 16 changed Agda files (11 new modules, the generalized
open-subspace proof and four facade updates) and both Analysis entrypoints
pass `agda-codex` with exit code 0 after their final source edits. All 398
audited complex/support/root snapshots are current with zero holes, metas,
constraints and warnings. All 883 Analysis modules are reachable
(1,284 transitive Cubical modules), with no missing imports, orphan
modules, cycles, choice dependencies, alternate real carriers or source flags.
All 291 audited local documentation links resolve; whitespace checks pass.
