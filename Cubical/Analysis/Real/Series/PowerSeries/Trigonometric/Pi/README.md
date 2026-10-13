# Constructive π in Analysis

Analysis is choice-free by project policy. Countable-choice exact-inverse
adapters were intentionally removed; only constructive proofs and generic
results using independently supplied mathematical witnesses remain.

π is twice the uniquely characterized first positive zero of cosine.
The checked specification for that zero is
`IsFirstPositiveCosineZero`; it includes positivity on every nonnegative point
strictly before the zero, implies the least-nonnegative-zero property, and is
unique.  `CharacterizedHalfPi` packages such a real with its characterization
and is itself a proposition; `characterizedPi` is twice its underlying value.

## Checked Bishop construction

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

now has an unconditional native Cauchy witness, `dampedBishopPiHalfCauchy`.
The construction uses the following modules:

- `Damped/Bounds.agda` proves preservation of positive cosine on each prefix;
  `Damped/Invariants.agda` applies it to every interval `[0,d n]`.
  It uses the existing lower bound on `[0,1]` and the signed endpoint
  inequalities from Analysis's uniform FTC. Since `d 1 = 1/2`, sine is at
  least `1/4` on each later step. Consequently
  `cos(d(n+2)) <= (7/8) cos(d(n+1))`.
- `Damped/Estimates.agda` bounds every increment by `(7/8)^n` and applies
  the native geometric-series Cauchy theorem. The contraction starts after
  the first step; the initial increment is handled separately.
  `Damped/Convergence.agda` applies these estimates to the recurrence and
  constructs its native sequential limit.
- `Damped/Characterization.agda` proves that the resulting limit is positive,
  has cosine zero, and has positive cosine at every nonnegative point
  strictly before it. A single radius from the gap to the limit suffices to
  find an iterate beyond such a point.

`Estimates/UniformDerivative.agda` supplies the global radiuswise-uniform
sine and cosine derivative estimates. The addition formulas translate the
remainders at zero, and the sharp absolute bounds by one control the
coefficients. Only finitely many truncated witnesses are combined. Neither
this argument nor the geometric Cauchy construction assumes countable choice.

`dampedBishopHalfPi` inhabits `CharacterizedHalfPi`. `Value.agda` exports
`halfPiℝ`, `piℝ`, and `twoPiℝ`, with no existence hypotheses. The original
undamped Bishop API remains available as an independent conditional route;
it is not used to construct these constants.

The cosine-zero characterization implies `sin half * sin half = 1`.
`Orientation.agda` now proves the positive sign from the characterization:
the derivative of sine at zero makes `sin h` positive for sufficiently small
positive rational `h`, and
`cos(half-h) = sin(half) * sin(h)` has a positive left-hand side.
Thus `characterizedHalfPi-sineOne` proves `sin half = 1`, and
`characterizedHalfPi-quarterTurn` supplies the quarter-turn structure without
an additional orientation input. The generic phase-shift, half-turn, and
full-period identities therefore apply to every characterized half-pi.
Older APIs accepting `CharacterizedHalfPiSineOne` remain compatible; the
witness can always be supplied by `characterizedHalfPi-sineOne`.

## Exact restricted inverses

`Pi/InverseValue.agda` constructs the native equivalences

- `sinℝ-restrictedEquiv : [-halfPiℝ,halfPiℝ] ≃ [-1,1]`;
- `cosℝ-restrictedEquiv : [0,piℝ] ≃ [-1,1]`.

The subtype-valued `arcSinℝ` and `arcCosℝ` need no supplied IVT,
equivalence, approximation sequence, or modulus. They satisfy both inverse
laws, uniqueness, and continuity. `InverseValue/Properties.agda` specializes
the existing inverse properties: values at `-1`, `0`, and `1`, arcsine
oddness, `arccos(-x) = piℝ - arccos(x)`, and weak and strict monotonicity.
`inverseTrigRadius` is an explicit rational uniform-continuity modulus for
both functions, including the endpoints.

### Construction in Analysis

The first-zero characterization already gives strict increase and embedding
of sine on the complete closed quarter interval. For each target `y` in
`[-1,1]`, `QuarterTurn/Restriction/Iteration.agda` constructs

```text
x 0       = -quarter
x (n + 1) = x n + (y - sin (x n))
```

Sine's sharp non-expanding bound keeps every iterate in the interval with
`sin(x n) <= y`. The nonnegative residual decreases, and induction proves
`n * (y - sin(x n)) <= x n + quarter <= 2*quarter`. A rational bound on the
width gives an explicit residual convergence rate. It is eliminated once
into the proposition bundling the image Cauchy witness and its limit;
there is no selection of a family of truncated witnesses.

The earlier midpoint factor estimates now have an explicit converse modulus.
The uniform FTC and `cos t >= 1/2` on `[0,1]` give `sin t >= t/2`.
`QuarterTurn/Injectivity/Separation/Quantitative.agda` uses
`probe = min(1,input)/2` and `output = (probe/2)^2`. Applying this with
`input = epsilon/4` reflects image closeness back to the source interval.
Thus the image Cauchy witness yields native source Cauchy data, and the
existing completeness and continuity proof produces an exact preimage.
Cosine uses the interval reflection `x ↦ quarter - x`.

See [the restriction construction](../QuarterTurn/Restriction/README.md)
for the generic iteration modules and exact theorem names.

### Existing interfaces and comparison

`QuarterTurn/Restriction/Existence.agda` provides `restrictedSineEquiv` and
`restrictedCosineEquiv` for any characterized positive quarter turn.
`Pi/InverseExistence.agda` supplies
`characterizedHalfPi-sineIntermediateValue` to the existing conditional
characterized-half-pi interfaces. Their signatures remain compatible.

Finite slack-bisection still proves approximate image density, and the
rational-target completion adapters still accept their explicit input data.
The new construction supplies a deterministic sequence and a rational
modulus directly; it does not upgrade radiuswise truncated density to a
chosen family. General exact IVT remains separate.

The historical HIT arcsine theorem concerns open intervals and a different
real carrier. Its reusable rational inverse-bisection theorem also requires
rational endpoints and values and a positive lower slope. The native proof
uses Analysis's non-expanding estimate, uniform FTC, and sequential
completion, allowing real endpoints where the sine derivative vanishes.
No carrier comparison or choice-dependent adapter is used.

## Public trigonometric characterization

The public `Pi` and `Trigonometric` facades export:

- `halfPiℝ-characterization`, `halfPiℝ-unique`, and
  `halfPiℝ-leastNonnegativeCosineZero`;
- `cosℝ-halfPiℝ = 0` and `sinℝ-halfPiℝ = 1`;
- `piℝ-characterization`, `piℝ-unique`, and `piℝ-leastPositiveSineZero`,
  including strict positivity of sine on `(0,piℝ)`;
- `sinℝ-piℝ = 0`, `cosℝ-piℝ = -1`, the half-pi and pi shift laws,
  and `sinℝ-periodic` / `cosℝ-periodic` with period `twoPiℝ`;
- negative half-pi/pi/full-period shifts and reflections in
  `Reflection.agda`, including `cos x = -sin(x-halfPiℝ)`;
- invariance under all integer multiples of `twoPiℝ`, values at those
  multiples, and the circle turn-coordinate equalities in
  `IntegerPeriod.agda`.

Here the equations describe theorem statements; the constants themselves
are defined through native sequential completion. No comparison with the HIT
Cauchy reals is assumed. The historical development supplies a mathematical
model, while this proof uses Analysis's own uniform derivative, FTC, and
geometric-series infrastructure.

## Further work

The restricted sine/cosine inverses are constructed. Identifying the native
quotient circle with the Cartesian unit circle and extending the inverse
calculus remain separate developments.

The inverse construction's individual-module checks, facade checks, aggregate
checks, and dependency audit are recorded in
[the restriction verification notes](../QuarterTurn/Restriction/README.md#verification--2026-10-08).
