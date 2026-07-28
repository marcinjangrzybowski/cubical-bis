# Mathematical overview of the Cauchy-real development

This document describes the mathematical scope of
`Cubical.HITs.CauchyReals` as of 2026-07-25.  It is an overview of the
constructions and theorems formalized in the directory, not an import guide or
an exhaustive list of helper lemmas.

The directory currently contains 307 Agda modules.  Four of these are
experimental files under `Dirty`; the remaining modules form the
foundational, real-analysis, transcendental, geometric, and complex-number
development described below.  Files named `Base`, `Core`, `Properties`,
`Bounds`, or similar often split one proof into manageable dependency and
elaboration units.  Such a split does not represent an additional
mathematical assumption.

## Constructive setting

The development is constructive and cubical throughout.

- Existence statements frequently use propositional truncation when a witness
  cannot be selected computationally.
- Strict positivity or apartness, rather than mere inequality, is used when
  constructing reciprocals or cancelling factors.
- Convergence and continuity carry explicit rational error bounds or moduli.
- The mean-value theorem has an approximate existential conclusion, which is
  the constructively valid form needed in subsequent proofs.
- Positive, non-negative, and apart-from-zero reals are represented as
  dependent types carrying the relevant proof.

No global excluded-middle or choice principle is introduced by this
development.

The source areas covered below are:

| Source area | Mathematical content |
| --- | --- |
| `Foundation`, `Algebra` | Sections 1--2 |
| `Analysis`, `Approximation` | Sections 3--5 |
| `Calculus` | Sections 6--7 |
| `Transcendental/Roots`, `Trigonometry` | Section 8 |
| `Exponentiation` | Section 9 |
| `ArcSin` | Section 10 |
| `Circle` | Section 11 |
| `Complex` | Section 12 |
| `Dirty` | Section 13 |

## 1. The Cauchy real numbers

### Higher inductive construction

The type `ℝ` is defined as a higher inductive-inductive Cauchy completion of
the rationals.  Its constructors provide:

- an embedding `rat : ℚ → ℝ`;
- limits of rationally indexed Cauchy approximations;
- a path constructor identifying points that are arbitrarily close;
- set truncation, so `ℝ` is a set.

The associated closeness relation is developed with reflexivity, symmetry,
triangle and rounding laws.  Being close at every positive rational radius is
equivalent to equality.  This supplies the main extensionality principle used
throughout the formalization.

The folder provides dependent and propositional eliminators, recursion
principles, and a universal-property formulation in terms of Cauchy
presentations.  The universal property constructs the map determined by a
rational embedding and compatible Cauchy-limit operation.

### Order and rational bounds

Strict and non-strict order, absolute value, minimum, maximum, and open and
closed intervals are defined on `ℝ`.  The formalization proves:

- the expected order laws and compatibility with equality;
- equivalences between symmetric interval membership and absolute-value
  bounds;
- rational witnesses inside strict real inequalities;
- density of the real order;
- the existence of a unit fraction below every positive real;
- weak linearity and the constructive finite dichotomy principles needed by
  later interval arguments.

Positive reals `ℝ₊`, non-negative reals `ℝ₀₊`, and apart nonzero reals
`ℝ₋₊` are used as proof-carrying subtypes.

## 2. Algebra and ordered algebra

Addition, negation, subtraction, and multiplication are constructed on the
Cauchy reals.  The resulting structure is proved to be a commutative ring.
The rational embedding preserves the ring operations, and natural-number
scalars agree with the ring's canonical natural-number embedding.

The order is compatible with the ring structure:

- addition is monotone and cancellable for both `<` and `≤`;
- multiplication is monotone with non-negative factors and strictly monotone
  with positive factors;
- positive and non-negative reals are closed under addition,
  multiplication, and natural powers;
- `ℝ` is packaged as an ordered commutative ring and as an Archimedean ring.

The absolute value satisfies the triangle inequality, detects zero, and
interacts with minimum, maximum, negation, multiplication, and powers in the
expected way.

Natural powers satisfy their algebraic laws, parity laws, continuity, and
order laws.  On non-negative reals, every positive natural power is monotone
and reflects order; on positive reals it is strictly monotone.  Rational
counterparts of these facts are also supplied.

Apartness `x ＃ y` is based on positive separation.  It is proposition-valued,
symmetric, agrees with rational apartness on embedded rationals, and supports
the cancellation arguments used below.

Reciprocals and division are constructive:

- a reciprocal requires an apartness or positive witness;
- multiplication by the reciprocal cancels;
- division equations can be moved back and forth across a nonzero
  denominator;
- the positive reciprocal reverses order and is involutive;
- the familiar comparisons `1 < x/y` and `x/y < 1` are derived under
  explicit positivity hypotheses.

A sign function is defined on apart nonzero reals, agrees with rational sign,
has square one, and is continuous on its apartness domain.

## 3. Metric, continuity, and extension theory

### Premetric structure

The Cauchy reals carry a canonical rational-radius premetric.  Its closeness
relation is equivalent to the original Cauchy-real closeness relation.
Premetric structures are also provided for:

- closed and unit intervals;
- the Cartesian real plane;
- products and predicate subspaces;
- a trivial/discrete source space;
- reversal of the unit interval.

There is compatibility in both directions between the older explicit
real-valued uniform-continuity predicates and the generic
`Cubical.Relation.Premetric` uniformly continuous maps.  Predicate-relative
versions are included.

The `PNorm` modules establish the root, monotonicity, positivity, and
two-coordinate inequalities used for one- and two-dimensional product-norm
arguments.  They are supporting results rather than a general
finite-dimensional normed-space theory.

### Continuous functions

Continuity is formulated directly using the Cauchy construction and rational
approximations.  The theory includes:

- identity and constant maps;
- composition and replacement by pointwise equal functions;
- negation, absolute value, minimum, maximum, addition, and subtraction;
- unary and binary continuity combinators;
- equality of continuous real functions from equality on rational inputs.

There is a predicate-relative theory of continuity on open domains, including
restriction and composition.  Open half-lines and open intervals are shown to
be open in the relevant constructive sense.

Inequalities between continuous functions can be extended from rational
points to all real points, with variants for the whole line, closed and open
half-lines, closed intervals, and arguments away from zero.

Clamp maps onto closed intervals are continuous, monotone, and
nonexpanding.  They support elimination from an interval by extending a
function to all reals.

Monotone uniformly continuous functions on an open half-line, with a
specified endpoint limit, can be extended to the corresponding closed
half-line.  Both left- and right-endpoint versions are formalized, preserving
the endpoint value, agreement on the open part, monotonicity bounds, and
uniform continuity.

### Uniform continuity and Lipschitz maps

Uniform continuity is developed both globally and on predicates.  It is
closed under the basic arithmetic operations, translation, rational scaling,
and powers on bounded intervals.  Explicit boundedness certificates are
provided for the identity on a rational interval and are closed under
addition, subtraction, negation, multiplication, and natural powers.

The Lipschitz theory constructs real functions from Lipschitz rational data:

- nonexpanding and general Lipschitz maps `ℚ → ℝ` extend to `ℝ → ℝ`;
- the extension agrees with the original function on rational points;
- binary nonexpanding rational operations lift to binary real operations;
- lower-Lipschitz estimates give injectivity and inverse-Lipschitz bounds;
- bounded local Lipschitz extensions are assembled coherently over expanding
  intervals.

Continuous additive automorphisms of the additive real group are classified
as multiplication by a scalar.  In particular, the formalization constructs
the scalar associated to such an automorphism and proves that the
automorphism acts by that scalar everywhere.

### Pasting

Continuous functions can be pasted across a cut point.  Variants cover:

- two functions defined on the closed lower and upper sides;
- a function defined above a closed lower bound;
- a function defined above a strict lower bound.

The resulting function agrees with each branch on its intended region.

## 4. Sequences, series, and uniform limits

Real sequences use explicit Cauchy moduli.  The development constructs the
limit of a Cauchy sequence and proves the expected approximation,
proof-irrelevance, shift, speedup, mapping, and constant-sequence laws.

Finite sums and partial-sum sequences are developed with:

- order comparison of termwise bounded sums;
- absolute-value bounds for sums;
- non-negative truncation and shifted-tail identities;
- the finite geometric-progression formula;
- the finite geometric-sum formula with an explicit nonzero denominator.

Convergence of a real series is related to the Cauchy property of its
partial-sum sequence.  The formalization includes:

- a ratio test with an explicit positive rational contraction;
- convergence of the real exponential series;
- Cauchy convergence of alternating series with decreasing positive
  magnitudes tending to zero.

For families of functions on a predicate, the theory defines uniform Cauchy
sequences, uniform convergence, and uniformly convergent series.  A uniformly
Cauchy family has a pointwise Cauchy-real limit, and uniform limits of
uniformly continuous functions remain uniformly continuous.  Addition,
negation, shifts, restrictions, and subsequences are supported.

## 5. Recovering approximations and inverse functions

Every Cauchy real has propositionally truncated rational approximations at
arbitrary positive rational precision.  Using the homogeneous-discrete
recovery construction, the development also obtains computationally
recoverable approximation data and decimal digit pairs.

A general rational bisection construction produces a Cauchy-real inverse
candidate for a strictly increasing rational function on a bounded interval.
Under an explicit lower slope bound:

- the inverse sequence is Cauchy;
- its values remain in the source interval;
- the inverse is Lipschitz on the target interval;
- it extends to a continuous real function;
- it agrees with rational bisection and satisfies the proved rational-side
  inverse law.

This infrastructure is subsequently used in root and inverse-function
constructions.

## 6. Differential calculus

### Derivatives and limits

Limits are defined using punctured neighbourhoods and apartness.  Total and
predicate-relative versions are supplied, together with inclusive-limit and
continuity equivalences.

A derivative on a predicate is expressed by a linear remainder estimate.
Both pointwise and uniform-on-a-predicate derivative notions are present.
The formalized rules include:

- identity, constants, addition, negation, and rational or real scalar
  multiplication;
- restriction to a smaller predicate;
- product and square rules on bounded intervals;
- a chain rule with the domain and boundedness data needed by the
  constructive estimates;
- translation of the input;
- natural-power differentiation;
- an inverse-function derivative theorem under explicit injectivity,
  continuity, apartness, and quantitative bounds.

Derivative values are unique.  Scaling the input transforms the derivative by
the expected factor.

### Rolle and mean-value results

For a uniformly differentiable function whose derivative is uniformly
continuous on a closed interval:

- the constructive Rolle theorem finds, for every positive tolerance, a point
  where the derivative has absolute value below that tolerance;
- the constructive mean-value theorem finds, for every tolerance, a point
  where `f(b) - f(a)` is within that tolerance of
  `f'(x) · (b - a)`;
- a function with identically zero derivative is constant on the interval.

The approximate conclusions are intentional and avoid selecting an exact
zero of the derivative.

## 7. Riemann integration and the fundamental theorem

Partitions, tagged partitions, mesh, samples, and Riemann sums are developed
over Cauchy-real intervals.  The supporting theory includes:

- equal partitions with arbitrarily small mesh;
- translation and positive scaling of partitions;
- clamping and resampling partitions;
- concatenation of adjacent tagged partitions;
- splitting of Riemann sums under concatenation;
- the finite-sum algebra and inequalities needed by the estimates.

Integrability is defined by convergence of Riemann sums as the mesh tends to
zero.  Integrals are unique and respect pointwise equality.  Uniformly
continuous functions on a closed interval are integrable via a canonical
refining sequence.

The integral satisfies:

- addition, subtraction, and scalar multiplication;
- monotonicity;
- an absolute-value estimate;
- the zero-width interval law;
- additivity over adjacent intervals;
- translation and positive input-scaling laws.

Both directions of the fundamental theorem of calculus are proved in the
uniform setting:

- the indefinite integral of a uniformly continuous function has that
  function as its derivative;
- integrating a uniformly continuous derivative gives the endpoint
  difference of its primitive.

There are also results commuting integration with uniformly Cauchy limits and
passing derivative relations to suitable uniform limits.

## 8. Roots, exponential series, trigonometry, and π

### Natural roots

For every positive natural degree, raising to that power is an equivalence on
positive reals.  Its inverse is the positive root.  The construction is
extended to non-negative reals, including zero.  The formalization proves:

- power/root cancellation in both directions;
- uniqueness of positive and non-negative roots;
- monotonicity and strict monotonicity;
- multiplicativity;
- compatibility with reciprocal and integer powers;
- continuity and uniform-continuity estimates on the relevant positive
  domains.

### The Taylor exponential

The real exponential series is shown to converge uniformly on bounded
intervals.  Its sum `expℝ` equals one at zero and, on non-negative arguments,
is positive, monotone, and explicitly bounded.  Termwise differentiation is
justified, giving

```text
(expℝ)' = expℝ.
```

### Sine, cosine, and π

Sine and cosine are constructed from their power series.  The series converge
uniformly on bounded intervals, allowing termwise differentiation:

```text
sin' = cos
cos' = -sin.
```

The development proves continuity, global Lipschitz bounds with constant one,
the parity and zero-value laws, and

```text
sin² x + cos² x = 1.
```

The number `π/2` is constructed as the limit of an explicit increasing
sequence, and `π` is twice that value.  The main established properties
include:

- `1 < π/2`, hence positivity of `π`;
- `cos (π/2) = 0` and `sin (π/2) = 1`;
- positivity and non-negativity of cosine on the appropriate first-quadrant
  intervals;
- addition formulae for sine and cosine;
- shifts by `π/2` and `π`;
- period `2π`;
- the standard double-angle identities.

The integration modules also compute antiderivatives of sine and cosine and
use these results in the construction and analysis of `π`.

## 9. Rational powers, real powers, logarithms, and normalized exponential

### Rational powers

Positive real bases support natural, integer, and rational powers.  The
rational-power construction is independent of the chosen numerator and
denominator representation.  It satisfies:

- exponent addition and multiplication laws;
- compatibility with roots, reciprocals, and integer powers;
- base and exponent monotonicity, including strict forms;
- continuity on the positive-real domain;
- Bernoulli and AM--GM inequalities;
- convexity and secant-slope monotonicity estimates.

These quantitative slope results supply the upper and lower Lipschitz bounds
used to extend rational exponents to real exponents.

### Real powers

For a positive base `x` and arbitrary real exponent `y`, the development
constructs `x ^ᵣ y`.  It agrees with rational powers on rational exponents and
satisfies:

```text
x ^ᵣ 0 = 1
x ^ᵣ 1 = x
x ^ᵣ (a + b) = (x ^ᵣ a) · (x ^ᵣ b)
(x ^ᵣ a) ^ᵣ b = x ^ᵣ (a · b).
```

Real power is continuous in the exponent.  It is also continuous in a
positive base, and is strictly increasing in the base when the exponent is
positive.  Lower-Lipschitz estimates in the exponent are available on
bounded intervals when the base is greater than one.

The derivative with respect to the exponent is proved:

```text
d/dy (x ^ᵣ y) = (x ^ᵣ y) · ln x.
```

### Logarithm and normalized exponential

The logarithm is defined on positive reals.  It is continuous, injective, and
strictly increasing, with:

```text
ln 1 = 0
ln (x · y) = ln x + ln y
ln (1/x) = -ln x
ln (x ^ᵣ y) = y · ln x
d/dx ln x = 1/x.
```

The logarithm construction is based on Cauchy sequences of rational powers.
The sequence modules prove their monotonicity, reciprocal symmetry, Cauchy
bounds, strict separation, and the slope estimates needed for injectivity and
differentiation.

A distinguished positive base `eBase` is normalized by `ln eBase = 1`.
Exponentiation with that base defines `realExp : ℝ → ℝ₊`.  The maps
`realExp` and `ln` are mutually inverse, strictly monotone, and form a group
isomorphism between additive reals and multiplicative positive reals.
Moreover:

```text
(realExp)' = realExp.
```

The apart nonzero multiplicative real group is identified with the direct
product of the positive multiplicative group and the two-element sign group.

### Two exponential constructions

The folder currently contains both:

- `expℝ`, defined by the Taylor series;
- `realExp`, defined as normalized real power with base `eBase`.

Both have a proved self-derivative theorem and their own algebraic or order
properties.  No module in the current tree proves that these two functions
are equal.  Statements using one should therefore not be silently read as
statements about the other.

## 10. Arcsine

On `[0,1)`, arcsine is constructed by integrating

```text
1 / sqrt (1 - x²).
```

The construction is continuous and strictly increasing.  Its range lies in
`[0,π/2)`, it is injective, and it is inverse to sine between the
corresponding first-quadrant intervals.  The derivative of arcsine on
`(0,1)` is established with the explicit positive square-root and inverse
witnesses required constructively.

The construction is extended by odd symmetry to

```text
arcSin : (-1,1) → (-π/2,π/2).
```

On these open intervals, sine and the symmetric arcsine are mutually inverse,
giving an equivalence.  Continuity, rational-clamp compatibility, and strict
monotonicity of sine on the interval are proved along the way.

The present symmetric inverse deliberately uses open endpoints; it is not a
global inverse to the periodic sine function.

## 11. The real circle

Two concrete circle models are formalized:

- a quotient of the real line by integral turns, with trigonometric
  coordinates evaluated at multiples of `2π`;
- the subtype of `ℝ × ℝ` satisfying `x² + y² = 1`.

The quotient circle is a set.  Sine and cosine descend to it, and the
coordinate map to the unit-vector model is proved to be an equivalence.

The unit-vector model carries:

- an abelian group structure corresponding to angle addition;
- rotations as group translations and equivalences;
- a rational-radius premetric inherited from squared Cartesian distance;
- a local chart obtained from the symmetric arcsine;
- constructive angle approximation for arbitrary unit vectors.

A local unwinding theorem is proved for interval maps whose image remains at
squared distance below `2` from the starting point.  It produces a real angle
function relative to that starting point.  A pointed version normalizes the
angle to zero at the left endpoint.

This is a local path-lifting result with an explicit hemisphere-style
distance hypothesis, not yet an unrestricted global covering-space theorem.

## 12. Complex numbers over the Cauchy reals

### Algebra, norm, and inversion

Complex numbers are pairs `ℂ = ℝ × ℝ`.  The standard operations make them a
commutative ring with real and rational embeddings and `i² = -1`.
Conjugation is an involutive commutative-ring equivalence.

The squared norm and modulus satisfy:

- non-negativity and the expected values at `0`, `1`, and `i`;
- invariance under negation and conjugation;
- multiplicativity;
- zero reflection;
- the triangle and reverse-triangle inequalities;
- compatibility with natural powers.

Complex apartness is positive squared distance.  A complex reciprocal and
division are defined only from an explicit apartness witness.  Both
cancellation laws, proof irrelevance, reciprocal involution, preservation of
apartness, and the formula for the modulus of a witnessed reciprocal are
proved.

### Metric and polar geometry

The modulus gives the canonical complex premetric.  The real and imaginary
projections, real embedding, modulus, translations, negation, and conjugation
have nonexpanding maps or direct metric estimates.  Multiplication by a fixed
complex scalar is Lipschitz and continuous from an explicit rational modulus
bound; truncated Archimedean existence supplies high-level versions.

Complex Cauchy sequences are complete by taking coordinatewise real limits.

The unit complex numbers form an abelian group and are equivalent to the real
circle above.  For apart nonzero complex numbers, polar decomposition is an
equivalence

```text
ℂˣ ≃ ℝ₊ × UnitCircleℂ.
```

This decomposition selects a radius and unit direction, but not a global real
argument.

### Complex sequences and series

The formalization includes:

- complex convergence, Cauchy sequences, limits, and uniqueness;
- convergence and Cauchy laws for constants, addition, negation,
  subtraction, and conjugation;
- generic preservation by nonexpanding and Lipschitz maps;
- preservation by multiplication with a fixed complex scalar;
- finite sums, convergent series, and power-series terms;
- finite-sum modulus bounds and absolute convergence;
- a constructive geometric-series convergence theorem under an explicit
  positive rational contraction bound;
- identification of the geometric-series sum with the witnessed inverse of
  `1 - z`.

When only `|z| < 1` is supplied, extraction of a rational contraction bound is
propositionally truncated, and the resulting existence statement reflects
that truncation.

### Complex differential calculus

Complex differentiation uses punctured difference quotients.  There are total
and predicate-relative notions, rational open balls, open domains,
differentiability, and holomorphicity predicates.

The established derivative rules cover:

- affine, identity, constant, and square functions;
- addition, negation, subtraction, and fixed scalar multiplication;
- products with explicit local value and derivative bounds;
- composition when the inner map preserves apart increments;
- natural powers and finite Horner-form polynomials;
- witnessed reciprocals and quotients on apart domains.

Reusable local-bound certificates are closed under restriction, congruence,
radius shrinking, constants, identity, negation, addition, multiplication,
and fixed scalar multiplication.

The Cauchy--Riemann equations are proved equivalent to real Jacobians being
complex-linear, and the corresponding complex derivative and Jacobian action
are identified.

The current complex calculus does not yet include an unrestricted chain rule,
a general differentiability-implies-continuity theorem, or complex
integration.  Joint continuity of binary multiplication and limit
preservation by binary multiplication and inversion are also planned rather
than completed.

### Complex elementary functions

Using the normalized real exponential and the real circle functions, the
development defines:

- `cis`;
- the complex exponential;
- complex sine and cosine;
- principal roots of unity and all their natural powers.

The complex exponential satisfies the zero, addition, conjugation,
negative/inverse, real-axis, and Euler formulae.  Complex sine and cosine
satisfy the exponential decomposition, parity, addition formulae,
`cos² z + sin² z = 1`, and agreement with real sine and cosine on the real
axis.

Complex exponential, sine, and cosine derivatives and a complex logarithm
have not yet been formalized.

For a finer-grained account of the complex implementation and its next
milestones, see
[`Complex/DevelopmentPlan.md`](Complex/DevelopmentPlan.md).

## 13. Experimental files and scope boundaries

The four modules under `Dirty` are demonstrations and evaluation experiments:

- rational bisection approximations of square and natural roots;
- recovered decimal evaluation of a root;
- experiments with Lipschitz extension and proof irrelevance;
- small type and normalization demonstrations.

They should not be read as additional library-level theorems.

The root-level `.agda` files such as `Foundation`, `Algebra`, `Analysis`,
`Calculus`, `Transcendental`, and `Geometry` mainly collect the developments
described above.  Likewise, the many nested aggregator files do not introduce
new mathematics beyond their leaves.

The Markdown files `Organization.md`, `GeneralityRefactorPlan.md`, and the
documents under `Complex` and `Exponentiation` describe architecture,
migration, performance, or future work.  This file is the complementary
summary of the mathematics that is already present.
