# Restricted sine and cosine inverses

`Existence.agda` constructs the equivalences

```text
sin : [-quarter, quarter] ≃ [-1,1]
cos : [0, 2*quarter]      ≃ [-1,1]
```

for a positive quarter turn characterized as the first positive cosine zero.
`Pi/InverseValue.agda` specializes them to the native `halfPiℝ`, without an
intermediate-value, approximation, modulus, or equivalence argument from the
caller. Its `arcSinℝ` and `arcCosℝ` return interval points; `fst` extracts
their real values. Both inverse laws and uniqueness are available, including
at the endpoints. `Pi/InverseValue/Properties.agda` supplies zero and endpoint
values, parity/reflection, weak and strict order laws, and an explicit uniform
continuity bound.

## Deterministic construction

For `-1 ≤ target ≤ 1`, start at the left endpoint and iterate

```text
x(0)   = -quarter
x(n+1) = x(n) + target - sin(x(n)).
```

The implementation writes the last line as
`x(n) + (target - sin(x(n)))`. Every term is determined by real arithmetic;
there are no real-order decisions or selected approximate preimages.

`Real/Functions/Inverse/Iteration/Base.agda` proves the reusable interval
argument for an increasing function with Lipschitz constant one. Each iterate
stays in the bracket and its image stays below the target. The nonnegative
residual decreases, and induction proves

```text
n * residual(x(n)) ≤ x(n) - a ≤ b - a.
```

`Rate.agda` uses rational division and a strict integer ceiling to turn a
rational bound on `b-a` into a whole convergence modulus. `Convergence.agda`
unpacks one truncated bound on the interval width into a proposition; the
explicit formula supplies every subsequent cutoff. This produces a native
Cauchy witness for the image sequence and convergence to the target.

The remaining issue is convergence of the source points, since cosine
vanishes at the endpoints. `Injectivity/Separation/Quantitative.agda` computes
a global closeness-reflection modulus. For a positive rational input radius
`ε`, it uses

```text
probe = min(1, ε/4)/2
δ     = (probe/2)^2.
```

The estimate `sin(t) ≥ t/2` for `0 ≤ t ≤ 1`, proved by native uniform FTC
from the existing cosine lower bound, makes this rational `δ` valid in the
existing midpoint/half-difference separation proof. The formula is defined
directly; it is not extracted from radiuswise truncated existence. The
rational halving/squaring helpers are opaque, with computation lemmas, to
avoid expanding positivity proofs during specialization.

`Iteration.agda` combines this reflection modulus with the image Cauchy
witness to obtain `SineQuarterApproximation`. The existing interval-limit
construction then gives an exact preimage. Injectivity supplies the sine
equivalence, and the existing interval reflection supplies the cosine
equivalence and `arccos(y) = quarter - arcsin(y)`.

## Existing interfaces

The finite slack-bisection density theorem remains available. Density alone
still does not select a coherent sequence. The new arithmetic iteration
provides that sequence independently.

The APIs accepting supplied equivalences, intermediate values, or rational
inverse data remain compatible. `Pi/InverseExistence.agda` constructs
`characterizedHalfPi-sineIntermediateValue` for every characterized half-pi,
so it supplies the formerly missing argument to those interfaces.

This construction assumes neither a comparison with HIT Cauchy reals nor any
choice principle. It does not establish general exact IVT for arbitrary
continuous functions.

## Verification — 2026-10-08

All twelve new proof modules and all four updated facades passed
`agda-codex` after their final source edits, with exit code 0, no holes,
unsolved metas, constraints, or warnings. `Cubical/Analysis/Everything.agda`
and `Cubical/Analysis.agda` also passed with the memory guard enabled.

The import audit reaches all 493 Analysis modules, with no missing imports,
orphan modules, cycles, HIT Cauchy-real dependencies, or choice-named
dependencies. The new source contains no postulates, holes, unsafe pragmas,
or choice assumptions. `git diff --check` is clean.
