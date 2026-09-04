# Constructive pi plan

The public target is not an arbitrary real named `pi`, but the uniquely
characterized first positive zero of cosine.  The checked specification is
`IsFirstPositiveCosineZero`; it includes positivity on every nonnegative point
strictly before the zero, implies the least-nonnegative-zero property, and is
unique.  `CharacterizedHalfPi` packages such a real with its characterization
and is itself a proposition; `characterizedPi` is twice its underlying value.

## Checked Bishop boundary

`Bishop/Iteration.agda` follows the construction in
`Cubical/HITs/CauchyReals/Trigonometry/Pi.agda`:

```text
a 0       = 0
a (n + 1) = a n + cos (a n)
```

The iteration is identified with the partial sums of its cosine increments.
`Bishop/Limit` isolates the missing existence obligation as
`BishopPiHalfCauchy`.  Given that witness, completeness defines a unique
half-pi candidate and hence a pi candidate.  Independently of how convergence
is proved, every limit candidate has cosine zero.  The first iterate is
checked to be exactly one.

The checked base-interval estimate follows the alternating-series style used
in Bishop's constructive analysis: four-term cosine blocks form an increasing
cofinal subsequence of partial sums on `0 <= x <= 1`.  Consequently
`1 - (1/2) x^2 <= cos x`, hence `1/2 <= cos x` and `0 < cos x` throughout
that interval.

The damped recurrence

```text
d 0       = 0
d (n + 1) = d n + (1/2) cos (d n)
```

is checked through the same explicit analytic boundary.  It is identified
with the partial sums of its scaled-cosine increments; every limit candidate
has cosine zero, because successive differences tend to zero and the nonzero
rational half-scalar can be cancelled.  Its remaining existence obligation is
`DampedBishopPiHalfCauchy`.

The cosine-zero characterization implies `sin half * sin half = 1`; positivity
of that sine is enough to select `sin half = 1`.  A generic positive-quarter-
turn API then gives phase-shift, half-turn, and full-period identities.  For a
characterized half-pi these yield the expected values at pi and periodicity at
twice pi, conditional only on that remaining sine-orientation fact.

## Restricted sine equivalence target

For a candidate `quarter`, `SineQuarterInterval quarter` is the closed
interval `[-quarter,quarter]`, while `SineUnitInterval` is `[-1,1]`.
`restrictedSine` is a checked map between them, using the global sharp bound
`|sin x| <= 1`.  The endpoint values are `sin (-quarter) = -1` and
`sin quarter = 1` for a positive quarter turn.  The restricted map is
continuous, and both closed intervals are complete.

Surjectivity has been isolated without adding an existence axiom:
`SineQuarterIntermediateValue quarter` says, propositionally, that every
`y` in `[-1,1]` has a preimage in the quarter interval.  It is equivalent to
surjectivity of `restrictedSine`.  For a positive first cosine zero the
embedding is now derived internally, so this intermediate-value statement is
the only remaining interval-level input to the requested equivalence.  This
makes a truncated closed-interval intermediate-value theorem the exact
remaining analytic boundary, rather than hiding it inside an inverse function.

The interval embedding now also has a quantitative converse modulus.  A
positive rational separation between inputs produces a positive rational
separation between their sine values; equivalently, sufficiently close sine
values force interval points to be close.  The modulus is pointwise truncated,
which is adequate for propositions but does not by itself choose the whole
Cauchy modulus required by the sequential completion.

`SineQuarterApproximateIntermediateValue` records the correctly bundled
bisection target: interval points with one native `SeqWitness`, together with
convergence of their sine values to the requested target.  It is proved
equivalent to `SineQuarterIntermediateValue`.  The forward proof takes the
source limit, preserves both interval bounds, and uses continuity of sine and
uniqueness of limits to obtain an exact preimage.  Thus only construction of
this approximate sequence remains, not any further completion or endpoint
argument.

There is also a choice-explicit, weaker input.  `PositiveRationalChoice₀`
assembles radiuswise truncated tails into a native `SeqWitness` and selects the
pointwise truncated sine-closeness reflection modulus.
`SineQuarterApproximateImageDensity` then asks only that, for each target and
each positive rational tolerance independently, there merely exists an
interval point whose sine is within that tolerance.  Dyadic sampling produces
a convergent image sequence; reflection reconstructs source Cauchyness, and
the preceding completion theorem supplies the exact preimage.  Thus a finite
located search with slack comparisons is sufficient under this explicit
choice hypothesis—no coherent infinite bisection sequence is required.  The
slack-band and endpoint inequalities, midpoint containment, and truncated
overlapping midpoint branch comparison are already checked as the first
finite-bisection layer.

There is now a second checked reduction that follows the rational-first shape
of the Bishop/HIT constructions.  `RationalSineInverseConstruction quarter`
contains a function `g : ℚ → ℝ`, the equation
`sin (g q) = clamp[-1,1] (rat q)`, and proofs that every `g q` lies in the
quarter interval.  A chosen sine-closeness reflection modulus makes the graph
of `g` Cauchy-continuous.  The sequential universal property then constructs
`G : ℝ → ℝ`; joint rational approximation, continuity of sine, and the
non-expanding clamp prove the exact equation `sin (G y) = clamp[-1,1] y`.
A parallel clamp argument proves `G y` remains in the quarter interval.
Consequently this rational data, with either a chosen or merely bundled chosen
reflection modulus, implies the intermediate-value theorem and the restricted
sine equivalence.  Approximation-family adapters obtain this exact rational
construction from limiting interval points; specialized adapters accept the
strict rational Cauchy witnesses used by `Cubical.Data.Rationals.Bisection`, or
only rational points with convergent sine images when positive-rational choice
is supplied.

The injective side is complete.  The first-zero characterization gives strict
positivity of cosine on the whole open symmetric quarter interval.  Midpoint
and half-difference lemmas place the two factors of
`sin y - sin x = 2 cos((x+y)/2) sin((y-x)/2)` in their positive regions; the
checked identity then proves `SineQuarterStrictlyIncreasing`, injectivity, and
embedding.  `restrictedSine-isEquivFromIntermediateValue` packages the result
so callers no longer provide strict monotonicity separately.

`Pi/RestrictedSine.agda` specializes the obligations and the resulting
equivalence theorems, including the approximate-IVT and rational-lift routes, to
`CharacterizedHalfPi`, so the intended
`[-pi/2,pi/2]` statement is explicit even before the unconditional half-pi
construction is available.

The historical `Cubical/HITs/CauchyReals/ArcSin` development remains a useful
specification, but its inverse theorem is for open intervals and depends on a
much larger roots, integration, fundamental-theorem, and arcsine stack.  There
is also no carrier comparison transporting that result to the sequential
Analysis reals.  The existing HIT inverse-bisection implementation is not a
drop-in IVT: its reusable theorem assumes rational endpoints, rational function
values, and a uniform positive lower slope.  Restricted sine has a
characterized real endpoint, non-rational values at rational arguments, and
zero derivative at the endpoints.  A direct located, approximate-comparison
bisection theorem for the current closed-interval and completeness APIs is
therefore the reusable next step.

No unconditional `halfPiℝ` or `piℝ` is exported: doing so before constructing
convergence and the complete first-zero characterization would hide the
central analytic obligations.

## Routes considered

- The historical full Bishop step is the formal specification.  Its old proof
  uses integration, the fundamental theorem of calculus, strict integral
  comparison, and mean-value estimates to establish positivity and geometric
  contraction.
- The checked damped Bishop step is the preferred convergence optimization.
  Exact global Lipschitz estimates and positivity on each step should yield
  the rational contraction `7/8`; then the increments are directly dominated
  by the existing geometric series `(7/8)^n`.  It retains the same first-zero
  characterization while needing less integration infrastructure.
- A Leibniz or Machin-series value can be made computable earlier, but the
  current arctangent development neither reaches `atan 1` nor proves the
  inverse-trigonometric equations needed to identify its value as a cosine
  zero.
- An IVT/bisection definition now has complete closed intervals, the
  continuous strictly increasing restricted sine embedding, sharp endpoint
  values, quantitative inverse control, and an approximate-sequence target
  equivalent to exact intermediate value.  With explicit positive-rational
  choice, the remaining theorem is only approximate image density: a finite
  located/approximate-comparison search may produce each tolerance witness
  independently, without a bundled Cauchy sequence, rational-valued
  evaluation, or a positive endpoint slope.
- A rational-first Bishop route can instead construct exact inverse values only
  for rational targets.  The new rational-lift layer handles arbitrary real
  targets and proves the exact clamped sine law.  What remains on this route is
  the computational rational bisection (or an equivalent imported HIT
  construction).  A bundled global inverse modulus is no longer an implicit
  obligation: the pointwise truncated modulus is assembled exactly when the
  caller supplies `PositiveRationalChoice₀`.
- Defining pi through an integral currently lacks general integrability,
  fundamental-theorem, and comparison results.

## Next proof obligations

1. Extend the partition core in `Calculus/MeanValue/Uniform.agda` to exact
   signed endpoint inequalities without introducing slow transparent proof
   composition.
2. Supply radiuswise uniform derivative witnesses for sine and cosine and
   derive exact global one-Lipschitz estimates.
3. Use the damped contraction and geometric-series domination to construct a
   Cauchy witness.
4. Prove positivity before the limit and positivity of sine at the limit,
   package `IsFirstPositiveCosineZero`, and only then expose unconditional
   `halfPiℝ`, `piℝ`, and their periodicity laws.
5. Finish restricted-sine surjectivity by proving
   `SineQuarterApproximateImageDensity` with finite located bisection, or by
   constructing the stronger `RationalSineInverseConstruction`.  Under the
   explicit positive-rational choice hypothesis, the checked sampling,
   reflection, completion, and rational-lift bridges finish the equivalence.
