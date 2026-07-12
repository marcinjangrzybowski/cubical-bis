# CauchyReals Migrated Definitions

This index records the modules that have been cleaned enough to be used as
ordinary source modules. It is meant as a navigation aid: look here first before
reviving code from `Dirty/` or adding another helper.

## Core real infrastructure

- `Base.agda`
  Defines the Cauchy real HIT `ℝ`, closeness `_∼[_]_`, eliminators and
  recursors for `ℝ`, and basic substitution/transport helpers for closeness.

- `Closeness.agda`
  Basic algebra and order-facing lemmas for the closeness relation.

- `Order.agda`
  Order relations on `ℝ`, negation/subtraction, absolute value, positive
  subtypes `ℝ₊` and `ℝ₀₊`, interval predicates, rational decision bridges, and
  `clampᵣ`.

- `OrderBounds.agda`
  Reusable min/max and interval-bound lemmas for order proofs.

- `RationalsImports.agda`
  Project-local rational and positive-rational import facade, including
  numerals and common operations used throughout the Cauchy-real development.

- `LiftingExpr.agda`
  Reflection helpers and solver wrappers for transporting rational/algebraic
  equalities into Cauchy-real goals.

- `Positive.agda`
  Small positive-real helpers factored out from later developments.

## Continuity, Lipschitz maps, and algebra

- `Lipschitz.agda`
  Lipschitz and non-expanding function interfaces, extension from rational
  functions, and closeness preservation lemmas.

- `Continuous.agda`
  Pointwise and predicate-indexed continuity, composition combinators,
  continuity of clamp, negation, min/max, and the general
  `IsContinuousWithPred-ᵣ` lemma.

- `Multiplication.agda`
  Construction of multiplication on `ℝ`, commutative-ring structure, powers,
  multiplication continuity, rational homomorphism lemmas, and square algebra.

- `Inverse.agda`
  Apartness, inverse on nonzero and positive reals, division operations,
  sign lemmas, and inverse continuity.

- `Power.agda`
  Integer/natural power support over `ℝ`, parity lemmas, absolute-value power
  lemmas, and zero/one power simplifications.

- `PowerDerivative.agda`
  New-style derivative statements for ordinary power functions.

- `InverseDerivative.agda`
  New-style derivative results for inverse functions and interval-restricted
  inverse derivatives.

## Sequences, summation, and approximations

- `Sequence.agda`
  Real dichotomy helpers, sequence type `Seq`, sequence sums, geometric
  progressions, Cauchy sequence infrastructure, limits, series convergence,
  and finite stitching helpers.

- `Sequence/Limits.agda`
  Smaller limit-oriented sequence facts factored out from the larger sequence
  module.

- `Summation.agda`
  Finite sums over `Fin`, fold/zip algebra, finite-sum inequalities, powers of
  two, and injection helpers for finite indices.

- `Aproximations.agda`
  Digit/extraction utilities and approximation-facing helpers for evaluating
  concrete Cauchy reals.

## Metric spaces

- `Metric.agda`
  Public metric facade for the Cauchy-real metric modules.

- `Metric/Base.agda`
  `IsMetric`, `MetricSpaceStr`, `MetricSpace`, uniform-continuous maps,
  subspace metrics, interval metric spaces, and basic metric combinators.

- `Metric/PNorm.agda`
  Product metrics, p-norm estimates, pair maps, and the `ℝ × ℝ` metric
  structure.

- `Metric/Discrete.agda`
  Discrete metric structure, the trivial one-point metric space, and uniform
  continuity from the trivial metric space.

## Partitions and integration

- `Partition.agda`
  Partitions and tagged partitions with the newer endpoint-oriented design,
  equal partitions, mesh estimates, partition transformations, clamping of
  tagged partitions, Riemann sums, and refinable tagged partitions.

- `TaggedPartitionConcatenation.agda`
  Concatenation of partitions/tagged partitions and Riemann-sum algebra for
  splitting integrals across adjacent intervals.

- `Integration.agda`
  Definitions of `on[_,_]IntegralOf_is_` and `on[_,_]IntegralOf_is'_`,
  uniqueness, substitution, translation, and preintegration machinery.

- `IntegrationMore.agda`
  Active legacy integration lemmas still used by checked modules: clamp
  transport, integral inequalities, linearity, constants, and uniform
  integration helpers. This still needs a future split; it was not moved to
  `Dirty/` because active cleaned modules import it.

- `FundamentalTheoremOfCalculus.agda`
  FTOC statements in the new derivative style, additive integral lemmas,
  Cauchy sequences of integrals/derivatives, and endpoint-weak versions using
  non-strict interval assumptions.

## Derivatives and mean value

- `Derivative.agda`
  Bishop-style derivative definitions using two points `x` and `y`, local and
  uniform derivative variants, derivative algebra, continuity consequences,
  and null-derivative lemmas.

- `MeanValue.agda`
  Bishop proposition 7, Rolle's theorem, mean value theorem, endpoint-weak
  mean value theorem, and null-derivative-to-constant results using the new
  derivative definitions.

## Uniform convergence and uniform continuity

- `Uniform.agda`
  Dependency-light uniform-continuity and uniform-convergence infrastructure:
  boundedness on intervals, pointwise extraction, Cauchy function sequences,
  uniformly convergent series, and dichotomy helpers.

- `LipschitzSequence.agda`
  Lipschitz estimates for sequences of functions.

## Bisection, roots, and exponentiation

- `Bisection.agda`
  New Cauchy-real bisection/inverse construction based on rational bisection,
  lower-slope/inverse-Lipschitz hypotheses, and compact-interval inverse
  machinery.

- `NthRoot.agda`
  Nth-root construction using the new bisection module, continuity of roots,
  root/power equivalences, and rational root approximation helpers.

- `NthRoot/NonNegative.agda`
  Nonnegative nth-root variants and supporting inequalities.

- `Exponentiation.agda`
  Public exponentiation facade for the split exponentiation modules. It still
  imports modules with lossy-unification flags; keep this in mind when working
  on the next cleanup pass.

- `Exponentiation/Core.agda`
  Positive integer powers, integer powers, roots, root/power algebra,
  continuity of integer powers, and positive/nonnegative coercions.

- `Exponentiation/Approximation.agda`
  Approximation machinery for exponentiation and rational approximation over
  bounded intervals.

- `Exponentiation/Convexity.agda`
  AM-GM, slope monotonicity, and convexity-style inequalities for powers.

- `Exponentiation/Derivative.agda`
  New-style derivative results for positive powers and integer powers.

- `Exponentiation/LogSequence*.agda`
  Logarithm sequence construction and its elementary, Bernoulli, delta,
  inequality, and square estimates.

- `Exponentiation/RealPowerBase.agda`
  Multiplicative group structure for positive/nonzero reals, automorphism
  infrastructure, interval inverse-Lipschitz helpers, and real-power support.

- `Exponentiation/RealPower.agda`
  Real-power construction from the logarithm sequence machinery.

- `ExponentiationMore.agda`
  Active legacy exponentiation/log module still imported by arcsine and ExpLog
  material. It remains outside `Dirty/` only because checked modules still
  depend on it; future work should split or replace the remaining imports.

- `ExponentialSeries.agda`
  Exponential series construction, convergence, positivity, and uniform
  continuity of the exponential series.

- `ExponentialSeriesDerivative.agda`
  New-style derivative support for the exponential series.

## Trigonometry and pi

- `TrigBase.agda`
  Sine and cosine series, convergence, derivative facts in the new derivative
  style, continuity, bounds by exponential series, and Pythagorean identities.

- `TrigonometricIdentities.agda`
  Values at `π/2`, phase-shift identities, periodicity, double-angle
  identities, and supporting rational-injection lemmas.

- `PiNumber.agda`
  Construction and estimates around `π`, sine/cosine boundedness, integrals of
  sine and cosine, ratio-test tools, and trigonometric Lipschitz bounds.

## Arcsine

- `ArcSin/Prelim/Basic.agda`
  Integration/order preliminaries for arcsine, cosine positivity on
  `(-π/2,π/2)`, and monotonicity facts for sine/cosine on basic intervals.

- `ArcSin/Prelim/Monotone/Quarter.agda`
  Strict monotonicity of sine on the first quadrant.

- `ArcSin/Prelim/Monotone/Full.agda`
  Strict monotonicity of sine on the symmetric open half-interval.

- `ArcSin/Positive/Core.agda`
  Positive arcsine core construction, monotonicity, and uniform-continuity
  support for the inverse-square-root integrand.

- `ArcSin/Positive/Continuity/Estimate.agda`
  Lipschitz estimate machinery used in continuity of positive arcsine.

- `ArcSin/Positive/Continuity.agda`
  Continuity of positive arcsine on `[0,1)`.

- `ArcSin/Positive/Properties/Definition.agda`
  Positive arcsine definition by integral and basic endpoint facts.

- `ArcSin/Positive/Properties/Derivative.agda`
  Derivative of positive arcsine and supporting first-quadrant sine facts.

- `ArcSin/Positive/Properties/Injection.agda`
  Injectivity of positive arcsine.

- `ArcSin/Positive/Properties/Monotone.agda`
  Strict monotonicity of positive arcsine.

- `ArcSin/Positive/Properties/Range.agda`
  Range of positive arcsine and section result `arcSin (sin x) = x` on the
  first quadrant.

- `ArcSin/Positive/Properties/Inverse.agda`
  Inverse laws and equivalence-facing facts for positive arcsine.

- `ArcSin/Symmetric/Base.agda`
  Symmetric interval/absolute-value conversions and definition of symmetric
  arcsine.

- `ArcSin/Symmetric/Properties/Continuity.agda`
  Continuity of symmetric arcsine on `(-1,1)`.

- `ArcSin/Symmetric/Properties/Rational.agda`
  Rational/symmetric clamp lemmas for arcsine.

- `ArcSin/Symmetric/Properties/Inverse.agda`
  Inverse laws for symmetric arcsine and the sine isomorphism on
  `(-π/2,π/2)`.

## Circle

- `Circle/Base.agda`
  Cartesian circle primitives: squared norm/distance, `distCircle`, circle
  equality, `√½`, and elementary square/absolute-value facts.

- `Circle/Angle/Bounds.agda`
  Bounds used by angle extraction from points on the circle.

- `Circle/Angle/FirstQuadrant.agda`
  First-quadrant angle construction and supporting trigonometric bounds.

- `Circle/Angle/CaseSplit.agda`
  Case split for constructing angles from arbitrary points on `distCircle`.

- `Circle/Core.agda`
  Quotient circle, circle relation, injections, sine/cosine from the circle,
  map to `distCircle`, surjectivity, `cos=1` consequences, and circular
  distance `cDist`.

- `Circle/Equivalence.agda`
  Injectivity/equivalence between quotient circle and `distCircle`, overlap
  quotient equivalence, and distance/circle compatibility.

- `Circle/Group.agda`
  Circle group structure, rotations, paths between circle points, and rotation
  isometries.

- `Circle/Chart.agda`
  Open half-circle chart and equivalence for restricted circle injection.

- `Circle/Metric.agda`
  Metric structure on `distCircle` and the upper-half equivalence for small
  distance from the base point.

- `Circle/Unwind.agda`
  Unpointed path-unwinding lemma for functions into `distCircle`.

- `Circle/PointedUnwind.agda`
  Pointed/basepoint-normalized path-unwinding lemma.

## Dirty quarantine

The following modules are preserved under `Dirty/` because they are obsolete,
experimental, contain holes/lossy flags, or are not yet migrated to the current
style:

- `Dirty/Alternating.agda`
- `Dirty/AproxDemo.agda`
- `Dirty/Bisect.agda`
- `Dirty/ExpExtended.agda`
- `Dirty/ExpLog.agda`
- `Dirty/NthRootEvalTest.agda`
- `Dirty/PreviouslyInUniform.agda`
- `Dirty/TrigBaseQ.agda`
- `Dirty/TypesDemo.agda`

Deleted obsolete modules:

- `BisectionAprox.agda`: no definitions remained; the file explicitly marked
  itself obsolete.
- `ExponentiationDer.agda`: old derivative API body was only kept as a
  commented migration reference.
- `ArcSin/Positive/Properties/Base.agda`: empty re-export wrapper.
- `ArcSin/Positive/Properties/Extras.agda`: its only general lemma moved to
  `Continuous.agda`.
- `CircleMore.agda`: compatibility re-export wrapper after the circle split.
