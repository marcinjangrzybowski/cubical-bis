# CauchyReals Migrated Definitions

This index records the modules that have been cleaned enough to be used as
ordinary source modules. It is meant as a navigation aid: look here first before
reviving code from `Dirty/` or adding another helper.

For the complementary inventory of `Dirty/` and commented-out declarations,
including completeness and migration estimates, see
[UnmigratedDefinitions.md](UnmigratedDefinitions.md).

## Core real infrastructure

- `Foundation/Base.agda`
  Defines the Cauchy real HIT `ℝ`, closeness `_∼[_]_`, eliminators and
  recursors for `ℝ`, and basic substitution/transport helpers for closeness.

- `Foundation/Closeness.agda`
  Basic algebra and order-facing lemmas for the closeness relation.

- `Foundation/Order/Base.agda`
  Order relations on `ℝ`, negation/subtraction, absolute value, positive
  subtypes `ℝ₊` and `ℝ₀₊`, interval predicates, rational decision bridges, and
  `clampᵣ`.

- `Foundation/Order/Density.agda`
  Dependency-light Cauchy-real rational-density bound `<ᵣ→Δ`, whose conclusion
  explicitly mentions the rational embedding. The established `Bounds` and
  `Inverse` paths reexport it for compatibility.

- `Foundation/Order/Bounds.agda`
  Reusable interval/absolute-value adapters and the inverse-dependent positive
  unit-fraction bound `∃UnitFractionBelowℝ₊`, together with compatibility
  reexports of the density and Archimedean rational upper bounds.

- `Foundation/Rationals.agda`
  Project-local rational and positive-rational import facade, including
  numerals and common operations used throughout the Cauchy-real development,
  plus the established `ℚmax-min-minus` compatibility spelling for the
  generic rational negation De Morgan law.

- `Cubical/Tactics/CauchyReals/ExpressionLifting.agda`
  Canonical reflection helpers and solver wrappers for transporting
  rational/algebraic equalities into Cauchy-real goals.

- `Algebra/Expression/Lifting.agda`
  Compatibility facade reexporting the canonical Cauchy-real expression
  tactic namespace.

- `Foundation/Order/Positive.agda`
  Small positive-real helpers factored out from later developments.

- `Foundation/UniversalProperty.agda`
  Cauchy presentations, their limit map, and the set-valued factorization and
  uniqueness theorem corresponding to HoTT Book Lemma 11.3.11.

## Continuity, Lipschitz maps, and algebra

- `Analysis/Lipschitz/Base.agda`
  Lipschitz and non-expanding function interfaces, the fixed-constant
  extension from rational functions, and closeness preservation lemmas.

- `Analysis/Lipschitz/Extension.agda`
  Constant-independent Lipschitz extension `fromLipschitz'` and its rational
  computation law `fromLipschitz'-rat`.

- `Analysis/Continuity/Core.agda`
  Dependency-light pointwise continuity, unary and binary rational
  extensionality, and their composition/non-expanding combinators, plus
  constant and primitive addition, negation, absolute-value, minimum, and
  maximum continuity facts needed by foundational ordered algebra.

- `Analysis/Continuity/Predicate.agda`
  Predicate-indexed continuity and composition, openness of predicates and
  real intervals, restriction, predicate dropping, and rational
  extensionality on open domains, plus the symmetric closed-interval to open-
  interval inclusion `sym-intervalℙ⊆ointervalℙ`.

- `Analysis/Continuity/Base.agda`
  Remaining extended continuity, limit, and rational compatibility support,
  together with compatibility reexports from `Continuity.Core`,
  `Continuity.Predicate`, `Continuity.Clamp`, `Continuity.Order`,
  `Continuity.Uniform.Base`, `Continuity.Approximation`, and the focused
  ordered-algebra modules.

- `Analysis/Continuity/Approximation.agda`
  Rational approximation structures `ℚApprox`, `ℚApproxℙ`, and their
  pointwise variants, together with the pointwise/packed equivalence,
  conversion to closeness-based approximation, and composition under uniform
  continuity. `Continuity.Base` retains the established names as restricted
  compatibility reexports.

- `Analysis/Continuity/Clamp.agda`
  Focused clamp continuity, interval membership and elimination, endpoint
  bounds and fixpoint laws, monotonicity, and distance contraction. It owns
  the established `IsContinuousClamp` family, `≤clampᵣ`, `clamp≤ᵣ`, and
  `∈ℚintervalℙ→clampᵣ≡` formerly defined in `Continuity.Base`; the old path
  retains restricted compatibility reexports.

- `Analysis/Continuity/Uniform/Base.agda`
  Dependency-light global and predicate-indexed uniform-continuity interfaces,
  including restriction of a full-real map to a predicate subtype and the
  rational-domain predicate interface `IsUContinuousℚℙ`.

- `Analysis/Continuity/Order.agda`
  Unary and binary rational-density comparison for continuous functions,
  their nonnegative and half-line variants, generic closed-lower, open-lower,
  and closed-interval dependent comparisons, and arbitrary open-predicate
  comparison `≤ContWP` with its upper/lower-bounded nonzero-domain variants.
  The broad `Continuity.Base` facade reexports the former base-owned spellings
  for compatibility.

- `Analysis/Order/Functions.agda`
  Reusable `IsStrictlyIncreasingOn` and `IsNondecreasingOn` predicates.

- `Analysis/Continuity/Apart.agda`
  Extends inequalities proved away from zero across zero by continuity.

- `Analysis/Continuity/AdditiveAutomorphism.agda`
  The continuous automorphism group `Aut[_]ᵣ`, rational linearity for
  continuous additive automorphisms, scalar automorphisms, extraction of the
  scalar at one, and the theorem that every such automorphism acts by that
  scalar. This module has no real-power dependency and is exported by the
  `Analysis` facade.

- `Analysis/Continuity/EndpointExtension.agda`
  Uniformly continuous monotone extension from strict half-lines to their
  closed endpoints, in both left- and right-end forms.

- `Analysis/Pasting/Base.agda`, `Analysis/Pasting/StrictLower.agda`, and
  `Analysis/Pasting/ClosedLower.agda`
  Function pasting at a closed cut and strict/closed lower-domain variants,
  with checked left/right computation laws. Previous names were `pasting`,
  `pasting<`, and `pasting≤`.

- `Algebra/Multiplication.agda`
  Construction of multiplication on `ℝ`, commutative-ring structure, powers,
  multiplication continuity, rational homomorphism lemmas, and square algebra.
  Its square theorem and rational-power embedding theorem are compatibility
  adapters to generic commutative-ring exponentiation and homomorphism laws.
  Its continuity dependencies are the focused `Continuity.Core` and
  `Continuity.Predicate` modules rather than the broad compatibility facade.

- `Algebra/Ring.agda`
  Focused access to the Cauchy-real ring structure and generic ring theory,
  the additive group `+Groupℝ`, and the canonical normalization
  `fromℕ≡fromNatℝ` between the ring-theoretic natural embedding and the
  established real numeral instance.

- `Algebra/Order/Multiplication.agda`
  Focused nonnegative- and positive-factor multiplication monotonicity for
  Cauchy reals, including the rational-factor wrappers `≤ᵣ-·o` and
  `≤ᵣ-o·`. The rational wrappers are also reexported from
  `Algebra/Inverse.agda` for compatibility.

- `Algebra/Order/Multiplication/Properties.agda`
  Post-instance specializations of generic coordinatewise multiplication
  monotonicity (`<ᵣ₊Monotone·ᵣ` and its two mixed variants), together with
  positive and nonnegative power preservation and the positive-factor
  nonstrict scaling equivalence `z≤x≃y₊·z≤y₊·x`. The established spellings
  are reexported from `Algebra.Inverse`.

- `Algebra/Order/Positive.agda`
  Definitionally compatible generic positive/nonnegative real subtypes and
  their closure witnesses. It owns the established `_₊+ᵣ_`, `_₊·ᵣ_`, and
  `_₊^ⁿ_` spellings as aliases to `PositiveReals`; `Algebra.Inverse`
  reexports them for compatibility while retaining positive inverse and
  division itself.

- `Algebra/Order/Density.agda`
  Order density of `ℝ`, specialized from the generic characteristic-not-two
  midpoint theorem. `Algebra.Inverse` retains `denseℝ` as a compatibility
  reexport.

- `Algebra/Order/Addition/Base.agda`
  Dependency-light additive identities, distribution over maximum,
  nonstrict translation monotonicity, strict/nonstrict negation reversal, and
  the internal pre-instance proof of the nonstrict symmetric subtraction
  rearrangement. It also owns the eight established negation-induced
  half-line and function-space isomorphisms, whose generic
  `negHalfLine...Iso` counterparts live in
  `Algebra.OrderedCommRing.Properties`. These established names remain
  available through `Continuity.Base`.

- `Algebra/Order/Addition/Bootstrap.agda`
  Explicit pre-instance boundary for strict/mixed addition monotonicity,
  positive-real addition, strict cancellation, and difference/order
  conversion helpers used while assembling the real ordered-ring instance and
  proving open-predicate support. Its normalization proofs use only the
  dependency-light additive laws.

- `Algebra/Order/Addition/Strict.agda`
  The absolute-value bound and rational-approximation support used to prove
  strict translation invariance, together with `<ᵣ-+o`, `<ᵣ-o+`, and six
  explicitly suffixed pre-instance additive rearrangement proofs. Their
  established unsuffixed names are instance-backed specializations in
  `Addition.Properties` and remain available through the focused addition and
  old continuity facades.

- `Algebra/Order/Lattice.agda`
  Focused min/max identities, distributivity and absorption laws, and the
  strict and nonstrict lattice bounds used by the Cauchy-real ordered-ring
  instance, together with coordinatewise min/max monotonicity and the positive
  and nonnegative min/max subtype constructors, plus the positive-domain
  monotone-image bounds `incr→max≤` and `incr→≤min`. Generic coordinatewise
  `∧Monotone`/`∨Monotone` live in pseudolattice theory and are exposed as
  `⊓Monotone`/`⊔Monotone` by ordered-ring theory. Positive maximum and both
  nonnegative operations mirror the generic subtype lattice API; positive
  minimum and its dependent monotone-image bound retain real-specific
  bootstrap proofs. These established names remain available through
  `Continuity.Base`.

- `Algebra/Order/AbsoluteValue.agda`
  The comparison between the continuously lifted real absolute value and its
  lattice form, triangle and reverse-triangle inequalities, sign
  simplifications, nonnegative-domain monotonicity, zero reflection, and the
  min/max absolute-difference theorem `absᵣ-min-max` with its rational helper.
  The monotonicity theorem and the stronger join-minus-meet identity
  `abs≡⊔-⊓` have generic counterparts in
  `Algebra.OrderedCommRing.Properties`; the real spellings retain
  dependency-light bootstrap proofs. Established declarations moved from
  `Continuity.Base` and `Algebra.Inverse` remain reexported there for
  compatibility.

- `Algebra/Order/Apartness.agda`
  Real apartness, its distance characterization, nonzero absolute-value
  positivity, the nonzero-real carrier `ℝ₋₊` and its subtype equality,
  negation preservation, and the open nonzero predicate `0＃ₚ`. The latter
  declarations remain available through `Algebra.Inverse`, while the former
  real-power path reexports the nonzero carrier for compatibility.

- `Algebra/Order/Addition/Properties.agda`
  Focused real specializations of generic strict and nonstrict additive
  cancellation, negation reversal, and positive/negative difference
  implications and equivalences, including all established additive
  rearrangement spellings, together with the positive-summand weakening
  `≤Weaken<+ᵣ`. The focused addition and old continuity facades reexport the
  seven declarations formerly supplied by pre-instance proofs; established
  inverse-path spellings remain compatibility reexports.

- `Algebra/Signs.agda`
  The real sign function on nonzero reals, its open-domain continuity and
  rational computation law, sign/absolute-value identities, and alternating
  sign actions used by power and trigonometric developments. The real sign
  family remains available through `Algebra.Inverse` for compatibility.

- `Algebra/Order/Archimedean.agda`
  The `ℝArchimedeanRing` instance and positive-rational upper bounds for
  positive and nonnegative reals, specialized from the generic
  `ArchimedeanRingTheory.∃ι₊₁Larger` theorem. Its numeral compatibility path is
  supplied by `Algebra.Ring`.

- `Algebra/Inverse.agda`
  Inverse on nonzero and positive reals, division operations, inverse
  continuity, and compatibility reexports for extracted ordered-algebra,
  continuity-comparison, rational, positive-operation, apartness, and sign
  facts. Its remaining predicate uniform-continuity adapter uses positive
  inverse essentially and is tracked as a deferred analytic migration.

- `Analysis/Lipschitz/Inverse/Base.agda`
  Predicate-indexed inverse-Lipschitz maps and their injectivity theorem.

- `Analysis/Lipschitz/Inverse.agda`
  Lower-Lipschitz bounds and conversion to inverse-Lipschitz estimates.

- `Algebra/Power/Base.agda`
  Integer/natural power support over `ℝ`, retaining the established parity,
  absolute-value, zero/one, and square spellings as generic commutative-ring or
  ordered-ring adapters. Continuity of real natural powers and the remaining
  even-power absolute-value proof stay local; the module depends on focused
  `Continuity.Core` rather than the broad compatibility facade.

- `Algebra/Power/Order.agda`
  Instance-backed real and rational adapters for generic ordered-ring
  natural-power bounds, base monotonicity, apartness preservation from one,
  strict exponent growth above one, nonstrict positive-exponent order
  reflection, and exponent antitonicity on `[0,1]`. The established nonstrict
  reflection names remain available from the sequence compatibility path;
  strict reflection remains in `Analysis/Sequence/Base.agda` because it uses
  inverse-backed strict positive-factor cancellation unavailable from the
  generic ordered-ring interface.

- `Calculus/Derivative/Power.agda`
  New-style derivative statements for ordinary power functions.

- `Calculus/Derivative/Inverse.agda`
  New-style derivative results for inverse functions and interval-restricted
  inverse derivatives.

## Sequences, summation, and approximations

- `Analysis/Sequence/Base.agda`
  Real dichotomy helpers, sequence type `Seq`, sequence sums, geometric
  progressions, Cauchy sequence infrastructure, limits, series convergence,
  and finite stitching helpers. Its former basic natural-power order block is
  now a restricted compatibility reexport from `Algebra.Power.Order`; the
  inverse/reflection family remains here pending a stronger algebraic owner.

- `Analysis/Sequence/Limits.agda`
  Smaller limit-oriented sequence facts factored out from the larger sequence
  module.

- `Analysis/Sequence/AlternatingSeries.agda`
  Alternating rational sequences, parity bounds on partial sums, and the
  Cauchy criterion for decreasing magnitudes tending to zero.

- `Calculus/Integration/Summation.agda`
  Finite sums over `Fin`, fold/zip algebra, finite-sum inequalities, powers of
  two, and injection helpers for finite indices. Its sigma-`Fin` addition fold
  now has an explicit bridge to canonical `FinVec` sums; the established
  algebraic, monotonicity, and absolute-value fold laws are adapters to generic
  `Semiring.BigOps`, `Ring.BigOps`, and `OrderedCommRing.SumTheory` results.
  Only representation-specific map, transport, concatenation, and
  finite-product folds remain local.

- `Approximation.agda`
  Public approximation facade.

- `Approximation/Recovery.agda`
  Digit/extraction utilities and recovery-based helpers for evaluating
  concrete Cauchy reals.

## Premetric spaces

- `Metric.agda`
  Facade for the canonical real, interval, product, reversal, and mapping
  interfaces based on `Relation.Premetric`.

- `Analysis/Metric/Premetric.agda`
  The Archimedean-ring premetric on `ℝ`, its equivalence with Cauchy-real
  closeness, and closed/unit-interval subspace instances.

- `Analysis/Metric/Compatibility/Base.agda`
  Adapters between the established `IsUContinuous` interface and generic
  uniformly continuous maps on `ℝPremetricSpace`.

- `Analysis/Metric/Compatibility/Predicate.agda`
  Adapters between predicate-indexed `IsUContinuousℙ` witnesses and generic
  uniformly continuous maps from `PremetricSubspace ℝPremetricSpace P`.
  Recovery from a packaged generic map is propositionally truncated because
  its modulus is hidden.

- `Analysis/Metric/Product.agda` and `Analysis/Metric/Reversal.agda`
  The coordinatewise real-plane premetric and the canonical nonexpanding
  reversal map, including its unit-interval restriction.

- `Analysis/Metric/PNorm.agda`
  Facade for the retained real-root p-norm inequalities and supporting
  nonnegative-real arithmetic.

- `Analysis/Metric/PNorm/Base.agda`
  Real-root p-norm inequalities and supporting nonnegative-real arithmetic.

- `Analysis/Metric/Discrete.agda`
  Facade for the canonical unit-premetric aliases and maps.

- `Analysis/Metric/Discrete/Base.agda`
  Aliases for the generic `UnitPremetricSpace` and canonical
  nonexpanding and uniformly continuous maps out of it.

## Partitions and integration

- `Calculus/Integration/Partition/Base.agda`
  Partitions and tagged partitions with the newer endpoint-oriented design,
  equal partitions, mesh estimates, partition transformations, clamping of
  tagged partitions, Riemann sums, and refinable tagged partitions.

- `Calculus/Integration/Partition/Concatenation.agda`
  Concatenation of partitions/tagged partitions and Riemann-sum algebra for
  splitting integrals across adjacent intervals.

- `Integration.agda`
  Public facade for the complete integration layer.

- `Calculus/Integration/Base.agda`
  Definitions of `on[_,_]IntegralOf_is_` and `on[_,_]IntegralOf_is'_`,
  uniqueness, substitution, translation, positive input-scaling substitution
  (`integral'-pre·<` and `integral'-pre·`), and preintegration machinery.

- `Calculus/Integration/Properties.agda`
  Clamp transport, integral inequalities, linearity, constants, and additive
  interval laws.

- `Calculus/Integration/Uniform.agda`
  Construction and algebra of integrals for uniformly continuous functions.

- `Calculus/Integration/FundamentalTheorem.agda`
  FTOC statements in the new derivative style, additive integral lemmas,
  Cauchy sequences of integrals/derivatives, and endpoint-weak versions using
  non-strict interval assumptions.

## Derivatives and mean value

- `Calculus/Derivative/Base.agda`
  Bishop-style derivative definitions using two points `x` and `y`, local and
  uniform derivative variants, derivative algebra, continuity consequences,
  and null-derivative lemmas.

- `Calculus/Derivative/Uniqueness.agda`
  Uniqueness of Bishop-style derivative values and transport across equal
  functions.

- `Calculus/Derivative/Scaling.agda`
  Bishop-style derivative rules for scaling the input of a function.

- `Calculus/Derivative/MeanValue.agda`
  Bishop proposition 7, Rolle's theorem, mean value theorem, endpoint-weak
  mean value theorem, and null-derivative-to-constant results using the new
  derivative definitions. Bishop proposition 7 is now an instance-backed
  adapter to generic finite-sum positive-summand existence rather than a
  Cauchy-real rational-density induction.

## Uniform convergence and uniform continuity

- `Analysis/Uniform.agda`
  Dependency-light uniform-continuity and uniform-convergence infrastructure:
  boundedness on intervals, pointwise extraction, Cauchy function sequences,
  uniformly convergent series, and dichotomy helpers.

## Bisection, roots, and exponentiation

- `Approximation/Bisection.agda`
  New Cauchy-real bisection/inverse construction based on rational bisection,
  lower-slope/inverse-Lipschitz hypotheses, and compact-interval inverse
  machinery.

- `Transcendental/Roots/Base.agda`
  Nth-root construction using the new bisection module, continuity of roots,
  root/power equivalences, and rational root approximation helpers.

- `Transcendental/Roots/NonNegative.agda`
  Nonnegative nth-root variants and supporting inequalities.

- `Exponentiation.agda`
  Public facade for the complete exponentiation, real-power, and logarithm
  stack. Implementations import `Exponentiation/Base.agda` or a narrower leaf.

- `Exponentiation/Base.agda`
  Facade for the rational/integer exponentiation construction and its
  approximation, convexity, Bernoulli, and derivative layers.

- `Exponentiation/RationalPower/Core.agda`
  Positive integer powers, integer powers, roots, root/power algebra,
  continuity of integer powers, and positive/nonnegative coercions.

- `Exponentiation/Approximation/Base.agda`
  Approximation machinery for exponentiation and rational approximation over
  bounded intervals.

- `Exponentiation/Approximation/InverseLipschitz.agda`
  Extension of bounded rational lower-slope estimates to inverse-Lipschitz
  estimates for the corresponding real approximants. This split checks
  without lossy unification.

- `Exponentiation/RationalPower/Convexity.agda`
  AM-GM, slope monotonicity, and convexity-style inequalities for powers.

- `Exponentiation/RationalPower/Derivative.agda`
  New-style derivative results for positive powers and integer powers.

- `Exponentiation/Logarithm/Sequence/*.agda`
  Logarithm sequence construction and its elementary, Bernoulli, delta,
  inequality, and square estimates.

- `Exponentiation/RealPower/Infrastructure.agda`
  Multiplicative group structure for positive/nonzero reals, interval
  inverse-Lipschitz helpers, and real-power support. Its former additive group
  and continuous-automorphism names are restricted compatibility reexports
  from their algebra and analysis owners.

- `Exponentiation/RealPower/Construction.agda`
  Real-power construction from the logarithm sequence machinery.

- `Exponentiation/RealPower/Definition.agda`
  Public operations for real powers and logarithms, their continuity, and
  basic identities.

- `Exponentiation/RealPower.agda`
  Public real-power facade.

- `Exponentiation/RealPower/BaseContinuity.agda`
  The exp-log representation of real powers and continuity of `x ↦ x ^ y` on
  positive bases.

- `Exponentiation/RealPower/Laws.agda`
  Difference factorization for real powers.

- `Exponentiation/RealPower/BaseOrder.agda`
  Strict monotonicity of positive-base real power for positive exponents.

- `Exponentiation/RealPower/NonzeroRealGroup.agda`
  Group isomorphism decomposing nonzero reals into a positive magnitude and a
  Boolean sign.

- `Exponentiation/RealPower/Bounds.agda` and
  `Exponentiation/RealPower/LowerLipschitz.agda`
  Compact-interval upper and lower slope estimates, lower-Lipschitz bounds,
  and inverse-Lipschitz consequences for real exponentiation.

- `Exponentiation/RealPower/Derivative.agda` and
  `Exponentiation/RealPower/DerivativeEverywhere.agda`
  Bishop-style differentiability of a bounded real-power approximant at zero
  and at every real exponent.

- `Exponentiation/RealPower/CalculusProof.agda` and
  `Exponentiation/RealPower/Calculus.agda`
  Global Bishop-style derivative of `x ^ y` with respect to `y`, and the
  logarithm power law, replacing the old quotient-slope results.

- `Exponentiation/RealPower/Composition.agda`
  Composition of real powers, `(x ^ a) ^ b = x ^ (a · b)`.

- `Exponentiation/Normalized/Base.agda`,
  `Exponentiation/Normalized/BaseLaw.agda`, and
  `Exponentiation/Normalized/BaseIndependence.agda`
  Construction and characterization of the normalized exponential base and
  independence from its auxiliary starting base.

- `Exponentiation/Normalized/Exponential.agda` and
  `Exponentiation/Normalized/Exponential/*.agda`
  Normalized real exponential, logarithm inverse laws, algebraic laws, order
  behavior, and the public normalized-exponential facade.

- `Exponentiation/Logarithm.agda`
  Public logarithm facade.

- `Exponentiation/Logarithm/StrictMonotonicity.agda` and
  `Exponentiation/Logarithm/Injectivity.agda`
  Strict order estimates for logarithm and the inverse-Lipschitz proof of
  injectivity.

- `Exponentiation/Logarithm/Order.agda` and
  `Exponentiation/Logarithm/Laws.agda`
  Product/additive logarithm laws and global order consequences.

- `Exponentiation/Logarithm/DerivativeBounds.agda` and
  `Exponentiation/Logarithm/Derivative.agda`
  Bounded-interval estimates and the Bishop-style derivative of logarithm.

- `Exponentiation/ExpLog/Derivative.agda`, `Exponentiation/ExpLog.agda`, and
  `Exponentiation/ExpLog/Group.agda`
  Derivative of normalized exponential, public exp/log facade, and the
  additive-to-positive-multiplicative group isomorphism.

- The former `ExponentiationMore.agda` catchall is now split among
  `RealPower/Definition.agda`, `RealPower/Composition.agda`,
  `Logarithm/StrictMonotonicity.agda`, and `Logarithm/Injectivity.agda`.
  None of these modules uses lossy unification.

- `Exponentiation/Series/Base.agda`
  Exponential series construction, convergence, positivity, and uniform
  continuity of the exponential series.

- `Exponentiation/Series/Derivative.agda`
  New-style derivative support for the exponential series.

## Trigonometry and pi

- `Trigonometry/Base.agda`
  Sine and cosine series, convergence, derivative facts in the new derivative
  style, continuity, bounds by exponential series, and Pythagorean identities.

- `Trigonometry/Identities.agda`
  Values at `π/2`, phase-shift identities, periodicity, double-angle
  identities, and supporting rational-injection lemmas.

- `Trigonometry/Pi.agda`
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
  Coordinatewise premetric structure on `distCircle`, its canonical inclusion
  maps, and the upper-half equivalence for small distance from the base point.

- `Circle/Unwind.agda`
  Unpointed path-unwinding lemma for functions into `distCircle`.

- `Circle/PointedUnwind.agda`
  Pointed/basepoint-normalized path-unwinding lemma.

## Dirty quarantine

The following modules are preserved under `Dirty/` because they are obsolete,
experimental, contain holes/lossy flags, or are not yet migrated to the current
style:

- `Dirty/AproxDemo.agda`
- `Dirty/ExpExtended.agda`
- `Dirty/NthRootEvalTest.agda`
- `Dirty/TypesDemo.agda`

Deleted obsolete modules:

- `BisectionAprox.agda`: no definitions remained; the file explicitly marked
  itself obsolete.
- `ExponentiationDer.agda`: old derivative API body was only kept as a
  commented migration reference.
- `ArcSin/Positive/Properties/Base.agda`: empty re-export wrapper.
- `ArcSin/Positive/Properties/Extras.agda`: its only general lemma moved to
  `Analysis/Continuity/Base.agda`.
- `CircleMore.agda`: compatibility re-export wrapper after the circle split.
- `Dirty/Bisect.agda`: superseded by the rational-backed inverse construction
  and interval isomorphism in `Approximation/Bisection.agda`.
- `Dirty/TrigBaseQ.agda`: its completed material was split among
  `Algebra/Signs.agda`, `Algebra/Power/Base.agda`, `Analysis/Uniform.agda`,
  `Exponentiation/Series/*.agda`, `Trigonometry/Base.agda`,
  `Calculus/Integration/FundamentalTheorem.agda`, and
  `Transcendental/Roots/NonNegative.agda`.
- `Dirty/Alternating.agda`: its theorem core moved to
  `Analysis/Sequence/AlternatingSeries.agda`; unrelated evaluator experiments were not
  retained in the analysis hierarchy.
- `Dirty/PreviouslyInUniform.agda`: endpoint extension moved to
  `Analysis/Continuity/EndpointExtension.agda`; its nth-root and FTOC material was already present
  in checked modules, leaving no unique definitions.
- `Dirty/ExpLog.agda`: all valid exp/log and scalar-action results had already
  migrated; its remaining additive-automorphism classification statement was
  unprovable and was discarded.
