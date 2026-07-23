# Constructive complex numbers over the Cauchy reals

The stable public entry point is:

```agda
open import Cubical.HITs.CauchyReals.Complex
```

The implementation uses `ℂ = ℝ × ℝ`.  It deliberately does not package `ℂ`
as the library's classical `Field`: constructively, an inverse is obtained
from positive norm (apartness), not from a proof of mere inequality.

## Available layers

- `Base`, `Algebra`: coordinates, `0ℂ`, `1ℂ`, `iℂ`, real/rational
  embeddings, a commutative-ring structure, and natural powers.
- `Conjugation`, `NormSquared`, `Modulus`: conjugation, squared norm,
  constructive square-root modulus, multiplicativity, zero reflection,
  triangle and reverse-triangle inequalities, and positivity.
- `Apartness`, `Inverse`: `z #ℂ w` means positive squared norm of `z - w`;
  `invℂ` and `_／ℂ[_,_]` require this positive witness and provide both
  cancellation laws, proof irrelevance, and inverse involution.
- `Metric`: the canonical modulus premetric, nonexpanding coordinate maps,
  translation/negation/conjugation maps, and coordinatewise completeness.
- `UnitCircle`, `Polar`: an abelian unit-circle group, equivalences with the
  existing Cauchy-real circle, and
  `polarEquiv : ℂˣ ≃ ℝ₊ × UnitCircleℂ`.
- `Calculus`: a constructive punctured-neighbourhood difference quotient,
  affine and square derivative theorems, holomorphic witnesses, and the exact
  Cauchy--Riemann characterization of complex-linear real Jacobians.
- `Analysis`: Cauchy and convergent complex sequences, completeness-based
  limits, uniqueness, finite sums, convergent series, power-series terms, and
  the finite geometric-series identity.
- `Transcendental`: `cis`, the complex exponential, complex sine and cosine,
  their addition/parity/Euler/Pythagorean laws, agreement on the real axis,
  and explicit principal roots of unity and all their natural powers.

`Examples.agda` checks representative uses: a Gaussian-integer product, the
derivative of the square map at `i`, a principal cube root of unity, and the
finite geometric-series identity.

## Constructive conventions

Division always displays the nonzero/apartness witness in its type.  Sequence
convergence is stated using the canonical rational-radius premetric.  Polar
coordinates are only formed for `ℂˣ = Σ[ z ∈ ℂ ] 0ℂ #ℂ z`; no choice of a
global argument function is assumed.  Roots of unity are built from explicit
angles, so their existence does not rely on algebraic closure.
