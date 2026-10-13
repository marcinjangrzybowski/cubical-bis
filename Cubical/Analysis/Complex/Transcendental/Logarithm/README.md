# Native complex logarithms

The logarithm API distinguishes truncated existence at a nonzero point from
an actual function on a specified domain. It uses the native Analysis reals
and introduces no choice principle.

[Base](Base.agda) preserves the polar-witness constructor and the equivalence
by implications between positive apartness and truncated logarithm existence.
There is no selected logarithm on the whole punctured plane.

## The right-half-plane branch

[Domain](../../Domain/RightHalfPlane.agda) defines the intrinsic open domain
`ComplexRightHalfPlane = Σ z : ℂ, 0 < re z`. Its premetric and inclusion come
from the library's generic subspace construction.

[RightHalfPlane/Base](RightHalfPlane/Base.agda) constructs

```text
rightHalfPlaneLog z = (logℝ (modulusℂ z), argument z)
expℂ (rightHalfPlaneLog z) = z
```

The argument is the existing normalized restricted-arcsine construction in
`Polar.RightHalfPlane`; the radial logarithm is the existing deterministic
real logarithm. [Properties](RightHalfPlane/Properties.agda) proves agreement
with the real logarithm on the positive real axis, value zero at a
positive-real point whose value is one, and injectivity of the branch.

[Continuity](RightHalfPlane/Continuity.agda) proves ordinary continuity on
the entire intrinsic half-plane. It uses the newly exposed normalized
argument value law, continuity of the complex modulus, and continuity of the
positive real reciprocal. [Derivative](RightHalfPlane/Derivative.agda) gives
its complex derivative `1/z` with respect to the coordinate `fst` at every
point of this domain. The statement needs no global bound and no total
extension of the branch to the plane.

[Uniform](RightHalfPlane/Uniform.agda) proves radiuswise uniform continuity
along a bounded uniformly continuous coordinate whose real part has a
supplied positive rational lower bound. The imaginary-coordinate estimate
uses bounded products and the existing quantitative arcsine modulus. The
radial estimate reuses exponential reflection to obtain uniform continuity
of the real logarithm above a fixed positive lower bound. Every radius
remains separately truncated.

## Reusable inverse calculus and integrals

[Derivative](Derivative.agda) proves the reciprocal derivative for any
supplied continuous logarithmic branch on a premetric source. It pulls back
the exponential derivative and applies the pointwise
[inverse differentiation theorem](../../Calculus/Derivative/Inverse.agda).
The pointwise and uniform inverse theorems share one absorption estimate;
neither divides by a nonzero increment. [Uniform](Uniform.agda) retains the
bounded version used by the line-integral FTC.

[Right-half-plane integrals](../../Integration/LineIntegral/RightHalfPlane.agda)
construct the logarithmic lift for every certified uniform path with
`η ≤ re (γ(t))` on its parameter interval, where `η` is supplied positive
rational data. Existing path bounds give the remaining uniformity hypotheses.
The native reciprocal integral is the endpoint difference of this branch;
closed paths have value zero. The same formula applies to any ambient
integrand satisfying `γ(t) * f(γ(t)) = 1` on the image.

The existing interval retraction extends the lift to real parameters outside
its interval. On the interval it agrees with the intrinsic branch, and the
integral uses the original curve and velocity.

The quantitative lower bound is a stated hypothesis. No theorem here selects
one from arbitrary pointwise positivity on a path. Rotated/slit-plane branch
atlases, the general compact C¹ upgrade, and Cauchy integral theory remain
further work.

## Validation

All 26 new or edited Agda files in this continuation and both Analysis
entry points pass `agda-codex`, exit 0. The 343 audited snapshots are current
and report no holes, metas, constraints or warnings. The
[integration validation](../../Integration/README.md#validation) records the
import and source audits. Completed 2026-10-10.
