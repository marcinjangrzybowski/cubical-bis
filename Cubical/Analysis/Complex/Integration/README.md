# Complex integration and the fundamental theorem

The public `Cubical.Analysis.Complex.Integration` facade uses the native
Analysis reals throughout. Complex Riemann integration is defined
coordinatewise from the existing tagged-partition integrals. A line integral
is the integral of `f (γ t) * γ′ t`; it is not defined by an endpoint formula.

## Proved endpoint theorem

`fundamentalTheoremOfComplexLineIntegrals` constructs

```text
HasComplexLineIntegral f path (F (pathFinish path) - F (pathStart path))
```

under the following explicit hypotheses:

- `path : UniformComplexPath a b` supplies `a ≤ b`, the curve and its
  velocity, uniform coordinate derivative estimates on `[a,b]`, and a
  positive rational bound on the velocity's l1 norm;
- `IsUniformPrimitiveAlongPath F f path` supplies a uniform first-order
  complex remainder estimate for `F`, with derivative `f`, along the path;
- a supplied positive rational constant bounds `normℂ (f (γ t))` on the
  parameter interval.

The primitive remainder is measured relative to the complex chord
`γ y - γ x`. Its controlling radius is in the real parameter interval.
The new chain rule combines this with the curve derivative and proves the
parameter derivative `(F ∘ γ)′ = (f ∘ γ) * γ′`. The existing real
Newton–Leibniz theorem then constructs both coordinate integrals. A separate
integrability assumption is unnecessary.

`complexLineIntegralOfPrimitive` identifies every supplied integral with the
endpoint difference. `closedPrimitiveComplexLineIntegral` proves zero for a
closed path. `complexPrimitiveLineIntegralPathIndependent` compares two
paths with the same endpoints and the same primitive, even when their
parameter intervals differ.

The path may have zero velocity or intersect itself. No division by a
parameter increment, nonzero-speed assumption or chosen argument is used.
Only parameter endpoints are ordered; the complex image is unrestricted.

## Polynomial application and segments

`polynomialDerivativeHasComplexLineIntegral path p` integrates the existing
formal polynomial derivative and returns the difference of polynomial values
at the endpoints. The uniform primitive estimate and derivative bound are
proved automatically from the polynomial Newton remainder and coefficient
bounds already in the library. The path's image bound follows from the
existing real mean-value estimates. A single merely existing rational bound
is eliminated into the proposition of having the displayed integral.

`polynomialDerivativeComplexLineIntegrable` packages the resulting integral;
`closedPolynomialDerivativeHasZeroLineIntegral` gives the closed-path case.
`constantHasComplexLineIntegral` proves the expected formula
`c * (pathFinish path - pathStart path)` for constant integrands.

`segmentUniformComplexPath start finish B bounded` supplies a straight-line
path on `[0,1]` from `start` to `finish`. The input `bounded` certifies
`normℂ (finish-start) ≤ B`. Its derivative and endpoint equations are proved,
including degenerate segments. No rational bound is selected from a merely
existing one to construct this path record.

## Finite contours, reversal and substitution

[Piecewise](Piecewise.agda) uses the library's finite graph paths. Each edge
contains a certified smooth piece and its endpoint equations. Its integral
is a finite sum of actual piece integrals; joins may have corners.
Concatenation adds these integrals, and the piecewise fundamental theorem
telescopes their endpoint differences. Polynomial and exponential primitives
supply the required certificates automatically. Reversal reverses both the
order of the pieces and each piece's parameter direction.

[Path reparameterization](Path/Reparameterization.agda) constructs the curve
`γ ∘ G`, with velocity `(γ′ ∘ G) * G′`, from a bounded uniformly differentiable
real parameter change whose image stays inside the original interval.
It requires neither monotonicity nor a nonzero speed. Reflection `a+b-t`
gives actual reversed paths, including zero-length intervals.

[Substitution](Substitution.agda) constructs a complex accumulation primitive
coordinatewise from a **supplied standard uniform-continuity witness**.
Consequently [line-integral reparameterization](LineIntegral/Reparameterization.agda)
preserves integrals when endpoints are preserved and changes the sign when
they are swapped. These conclusions hold without a complex primitive of the
integrand. Primitive-based versions instead use the radiuswise uniform
hypotheses of the endpoint theorem.

## Exponential and logarithmic lifts

[Exponential integrals](LineIntegral/Exponential.agda) prove
`∫γ expℂ(z) dz = expℂ(γ(b)) - expℂ(γ(a))` for every certified path.
Uniform exponential differentiation follows from the derivative at zero,
the addition law, and a bound on exponential values. Such bounds are derived
on every bounded path image using the existing modulus formula.

[Logarithmic lifts](LineIntegral/Logarithm.agda) accept a supplied radiuswise
uniformly continuous `L : ℝ → ℂ` with `expℂ(L(t)) = γ(t)`. They prove the
integral of `expℂ(-L(t)) * γ′(t)` equals `L(b)-L(a)`, and identify this
coefficient with the native reciprocal of the curve. Differentiability of
`L` is derived by the [uniform inverse theorem](../Calculus/Derivative/Uniform/Inverse.agda),
not assumed. A supplied single-valued logarithm branch on the path image
therefore gives the usual reciprocal endpoint formula and closed-path zero.
That supplied-lift interface is complemented by the constructed
[right-half-plane branch](../Transcendental/Logarithm/README.md).
[RightHalfPlane](LineIntegral/RightHalfPlane.agda) proves the reciprocal
endpoint formula for a path with a supplied positive rational `η` satisfying
`η ≤ re (γ(t))` on the interval. The branch and its uniform continuity are
constructed from the native real logarithm, restricted arcsine and path
image bounds. The reciprocal is the native witnessed inverse; an adapter
also accepts any ambient integrand satisfying the inverse law on the image.
Both have zero integral for closed paths. The [path construction](LineIntegral/RightHalfPlane/Path.agda)
uses the existing interval retraction to supply the lift outside its interval.
No global logarithm or lower bound from arbitrary pointwise positivity is
selected.

[Circle](LineIntegral/Circle.agda) gives an explicit positive unit-circle
path `t ↦ expℂ(0,t)` on `[0,2π]`, certifies its derivative, endpoints and unit
modulus, and uses the explicit lift `(0,t)` to compute its reciprocal integral
as `(0,2π)`. The value is proved nonzero. This is a contour calculation; a
winding classification or homotopy theorem is not assumed.

## Modules and reuse

| Module | Interface and proof source |
| --- | --- |
| [Base](Base.agda) | Coordinate Riemann integrals, uniqueness, proof independence and interval extensionality from the existing real API |
| [Operations](Operations.agda) | Addition, subtraction, negation, complex scaling and conjugation from real integral laws |
| [Curve](Curve.agda) | Coordinate/complex uniform derivative bridges, bounded-speed Lipschitz estimates and uniform continuity |
| [Path](Path.agda), [Continuity](Path/Continuity.agda), [Bounds](Path/Bounds.agda), [Path/Segment](Path/Segment.agda) | Certified bounded uniform paths, their endpoints and image bounds, and straight segments |
| [FundamentalTheorem](FundamentalTheorem.agda) | Complex-valued Newton–Leibniz by applying the existing real theorem to both coordinates |
| [LineIntegral/Base](LineIntegral/Base.agda) | Actual line-integral predicate and unique values for certified paths |
| [LineIntegral/FundamentalTheorem](LineIntegral/FundamentalTheorem.agda) | Uniform chain rule along the path and the endpoint theorem |
| [LineIntegral/Consequences](LineIntegral/Consequences.agda), [Polynomial](LineIntegral/Polynomial.agda) | Constant integrands, path independence, polynomial primitives and closed-path consequences |
| [Path/Reparameterization](Path/Reparameterization.agda), [Path/Reversal](Path/Reversal.agda) | Actual composed/reflected paths and certified chain-rule velocities |
| [UniformContinuity](UniformContinuity.agda), [Substitution](Substitution.agda) | Coordinate accumulation, integrability and change of parameter |
| [Path/Translation](Path/Translation.agda), [LineIntegral/Translation](LineIntegral/Translation.agda) | Geometric translation with unchanged velocity and covariance of actual integrals |
| [PowerSeries/Centered](LineIntegral/PowerSeries/Centered.agda), [PowerSeries/Reexpansion](LineIntegral/PowerSeries/Reexpansion.agda) | FTC for expansions about arbitrary centers and the canonical Taylor application |
| [Piecewise](Piecewise.agda), [Piecewise/PowerSeries](Piecewise/PowerSeries.agda) | Finite graph paths, concatenation, reversal and the telescoping FTC, including different local series on each piece |
| [Exponential](LineIntegral/Exponential.agda), [Logarithm](LineIntegral/Logarithm.agda), [RightHalfPlane](LineIntegral/RightHalfPlane.agda), [Circle](LineIntegral/Circle.agda) | Elementary primitives, continuous logarithmic lifts and the reciprocal circle integral |

The supporting [uniform complex calculus](../Calculus/Derivative/Uniform.agda)
includes an [indexed chain rule](../Calculus/Derivative/Uniform/Chain.agda),
[real-parameter coordinate bridges](../Calculus/Derivative/Uniform/RealParameter.agda),
[exact and affine derivatives](../Calculus/Derivative/Uniform/Basic.agda), and
[uniform polynomial estimates](../Calculus/Derivative/Uniform/Polynomial.agda).
The chain rule reuses the previous complex remainder identity and norm
estimates. The [path record](Path/Structure.agda) is generated with
its predicates abstract and instantiated afterwards; this keeps native real
order and derivative normalization out of record composition generation.
Scalar coordinate algebra is shared with horizontal derivative
restriction through [RealScalar](../Algebra/RealScalar.agda).
The finite-contour proofs separate recursion on integral data from the
subsequent equality of values; this avoids normalization of dependent pairs
containing completed-real sums. The inverse estimate similarly separates
generic remainder algebra and an absorption inequality before substituting
the concrete half-scale coefficient.


## Constructive scope and next work

Every derivative error tolerance has its own propositionally truncated radius.
These are never assembled into a chosen modulus. The supplied speed bound
constructs a uniform continuity modulus for the path directly. Integral
existence in the endpoint theorem comes from uniform differentiation and the
real partition proof, not from a choice-dependent convergence converse.

The theorem is for the stated bounded uniform path class. Ordinary pointwise
holomorphicity and pointwise differentiability alone are not converted into
these hypotheses. Uniform derivative data on an ambient domain can be pulled
back by `uniformComplexDerivativeAlongPrecompose`; the global ambient adapter
is `uniformComplexDerivativeGivesPrimitiveAlongPath`.

[Boundedness](LineIntegral/Bounded.agda) removes the separately supplied
integrand bound when `f ∘ γ` is radiuswise uniformly continuous. The
[uniform factor criterion](../Calculus/Derivative/Uniform/Factor.agda)
derives a uniform derivative from a jointly uniformly continuous supplied
divided difference. Neither result converts arbitrary pointwise C¹ data
into uniform derivative estimates.

The [power-series application](LineIntegral/PowerSeries.agda) now derives
both the uniform primitive estimate and the integrand bound from a supplied
native Cauchy witness for `normℂ(a[n+1]) * ((n+1) * R^n)`. The original
and derivative functions need only have the respective sums along a path
whose image satisfies `normℂ γ(t) ≤ R`. The resulting endpoint integral,
integrability and closed-path zero require no extra bound on the integrand.

The [strict-interior version](LineIntegral/PowerSeries/Interior.agda) derives
the derivative-majorant witness from the original norm-majorant at an outer
radius `R`, for a path with a supplied bound `normℂ γ(t) ≤ r < R` and `0 ≤ r`.
Thus endpoint integrals and closed-path zero no longer need a separate
derivative-convergence assumption in this setting. The same certified path
class and along-path sum representations are retained.

The [trigonometric application](LineIntegral/Trigonometric.agda) now proves
`∫γ cos(z) dz = sin(γ(b)) - sin(γ(a))` and
`∫γ sin(z) dz = cos(γ(a)) - cos(γ(b))` for every certified uniform path.
It uses the standard complex series identities and their formal coefficient
derivatives. The path-image bound plus one supplies the strict outer radius;
no convergence, integrand bound or integrability input is requested from the
caller. Both integrals vanish on closed paths.

Further work includes that compact-domain upgrade and additional logarithm
branch domains and compatibility. Cauchy's theorem for a holomorphic integrand
without a supplied primitive, Cauchy's integral formula, and general homotopy
invariance are separate results.

## Validation

The local-logarithm continuation adds 17 Agda modules and updates nine
existing Agda files. All 26 passed direct `agda-codex` checks after their
final source edits. Both `Cubical/Analysis/Everything.agda` and
`Cubical/Analysis.agda` then passed with exit code 0. All 343 audited
complex/supporting and entry-point snapshots match current sources and
report no holes, unsolved metas, constraints or warnings.

The import audit reaches all 829 Analysis modules and 1,230 Cubical modules
transitively, with no missing imports, orphan Analysis modules, cycles,
choice dependencies or `CauchyReals` imports. The source audit found no
postulates, holes or new options in the complex and supporting modules.
Local documentation links resolve and `git diff --check` passes.
Validation completed on 2026-10-10.

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


## Centered series and finite local expansions

[Path translation](Path/Translation.agda) preserves the actual velocity and
speed bound. [Line-integral translation](LineIntegral/Translation.agda)
then follows by integrand equality. The
[centered power-series theorem](LineIntegral/PowerSeries/Centered.agda)
reuses the existing strict-interior FTC on the recentered path. Its data are
`0 ≤ r`, `norm(γ(t)-center) ≤ r < R`, a native Cauchy majorant for the
coefficient sequence at `R`, and along-path sums for `F` and its formal
derivative `f`. The conclusions are a uniform primitive estimate, actual
integrability, the endpoint value `F(finish)-F(start)`, and zero for closed
paths. The center can be anywhere in the complex plane.

For coefficients originally expanded at zero, the
[canonical reexpansion application](LineIntegral/PowerSeries/Reexpansion.agda)
requires `norm(center)+r<R` instead. Native Taylor convergence and
[compatibility of all derivatives](../Series/PowerSeries/Translation/Derivatives.agda)
construct the required local series from the original majorant. One
intermediate radius is used inside propositional elimination; no radiuswise
choice or additional native derivative-majorant witness is introduced. The function values
still need only represent the original sums along the path.

[Piecewise/PowerSeries](Piecewise/PowerSeries.agda) accepts a local centered
series certificate on each certified piece. Centers, coefficients, radii and
parameter intervals may differ. Certificates may be merely known to exist:
each truncation is eliminated into its integral proposition, and the existing
finite telescoping theorem constructs the piecewise integral. The common
`F` and `f` are essential; arbitrary unrelated local primitives are not
silently glued. Endpoint formulas, closed-path zero and path independence
are exported.

## Constructed power-series primitives (2026-10-12)

[Complex formal primitives](../Series/PowerSeries/Primitive.agda) reuse the
real `formalPrimitive` in both coordinates, with an arbitrary integration
constant. Their formal derivative is exactly the original coefficient
sequence. The integrated series has a native Cauchy majorant at the same
nonnegative radius as the original series, and its derivative majorant is
exactly the original majorant. A smaller radius is unnecessary here.

[Actual primitive values](../Series/PowerSeries/Primitive/Domain.agda) are
constructed on the closed norm ball and take the specified constant at zero.
Their uniform derivative concerns chords within that ball, including its
boundary; this is not an ambient boundary differentiability claim.
[The parameter-value FTC](LineIntegral/FundamentalTheorem/Along.agda)
accepts primitive and derivative values indexed by the path parameter. The
existing ambient FTC now reuses this theorem's chain-rule proof.

[Centered path values](LineIntegral/PowerSeries/Primitive/Path.agda) use the
existing interval retraction to supply total parameter functions, without
extending a series outside its convergence ball. The
[constructed-primitive FTC](LineIntegral/PowerSeries/Primitive.agda) proves
actual integrability, endpoint evaluation and closed-path zero from one
native majorant and `norm(γ(t)-center) ≤ R`, with `0 ≤ R`. An ambient
integrand may be supplied by its series representation only along the path;
no ambient primitive is needed. Endpoint sums of the integrated series also
suffice to state the result with independently named endpoint values.

[Finite contours](Piecewise/PowerSeries/Primitive.agda) have endpoint
formulas, closed-path zero and path independence for one common series,
center and radius. Canonical primitive values at the corners make the
finite sum telescope. The earlier local-series theorem still allows
different centers when a common primitive is supplied. Neither theorem
glues unrelated local primitives automatically.

Next prove that constructed primitives commute with Taylor reexpansion
when the new constant is the primitive's value at the new center. Then use
that compatibility to handle differently centered local descriptions with
coherent endpoint values.

Pointwise holomorphicity alone, pointwise C¹-to-uniform upgrades and Cauchy
integral theory remain outside this checkpoint.

## Centered FTC validation

Centered FTC validation: all 12 changed Agda files (seven new modules and
five facade updates) and both Analysis entrypoints pass `agda-codex` with exit
code 0 after their final source edits. All 425 audited complex/support/root
snapshots match current source hashes and report zero holes, metas,
constraints and warnings. All 909 Analysis modules are reachable
(1,310 transitive Cubical modules), with no missing imports, cycles,
orphans, choice dependencies, alternate real carriers or source flags.
All 350 audited local documentation links resolve; whitespace checks pass.

## Constructed-primitive validation

Constructed-primitive validation (2026-10-12): all 19 changed Agda files
(12 new modules, five facade updates and two reused integration modules)
and both Analysis entrypoints pass `agda-codex` with exit code 0 after their
final source edits. All 437 audited complex/support/root snapshots match
current sources and report zero holes, metas, constraints and warnings.
All 921 Analysis modules are reachable (1,322 transitive Cubical
modules), with no missing imports, cycles, orphans, choice dependencies,
alternate real carriers or source flags. All 379 audited local documentation
links resolve; whitespace checks pass.
