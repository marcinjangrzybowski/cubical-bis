# Native complex differential calculus

This is the second milestone of the [missing-layer plan](../DEVELOPMENT_GAPS_2026-10-09.md).
The public [Calculus facade](../Calculus.agda) exports general derivatives and
holomorphicity, using the native sequential real carrier throughout.

## Derivative and constructive boundary

`IsComplexDerivativeAt f d z` means that, for every positive rational `ε`,
there merely exists a positive rational coordinate radius `δ` such that

```
normℂ ((f w -ℂ f z) -ℂ d ·ℂ (w -ℂ z))
  ≤ℝ rat (fst ε) · normℂ (w -ℂ z)
```

whenever `z ∼ℂ[ δ ] w`. Here `normℂ` is the existing l1 norm. The derivative
acts by complex multiplication; this is complex differentiability, not an
arbitrary real-linear approximation to a map of two real coordinates.
The definition includes zero increments and never divides by an increment.
The product premetric and l1 norm are related using the existing factor-of-two
estimate, with half-radius adjustments made explicitly.

`IsComplexDerivativeAlongAt` replaces `w -ℂ z` by a supplied coordinate
map's displacement on an arbitrary premetric source. It supports open
subspace and path APIs. Its rules requiring continuity explicitly request
continuity of the coordinate map. Uniqueness is proved for the full complex
plane and intrinsic functions on open subspaces. It is not asserted for
arbitrary coordinates, which may be constant.

Each derivative radius stays under its own propositional truncation. Finite
combinations of witnesses stay under truncation too. No global modulus,
countable choice, or comparison with the HIT Cauchy reals is used.

## Interfaces and proofs

| Module | Results |
| --- | --- |
| [Derivative/Base](Derivative/Base.agda) | Pointwise, global and coordinate derivative predicates; proposition proofs; continuous pullback |
| [Derivative/Restriction](Derivative/Restriction.agda), [Uniqueness](Derivative/Uniqueness.agda) | Horizontal real/imaginary restrictions, uniqueness of derivative values and functions, proposition-valued derivative existence |
| [Derivative/OpenSubspace/Uniqueness](Derivative/OpenSubspace/Uniqueness.agda), [Tower/OpenSubspace](Derivative/Tower/OpenSubspace.agda) | Intrinsic derivative and tower uniqueness on open subspaces, without ambient extensions |
| [Derivative/Translation](Derivative/Translation.agda) | Coordinate-translation invariance and translation of ambient derivative towers |
| [Derivative/Continuity](Derivative/Continuity.agda) | A local linear bound and continuity from a derivative at one point; global and coordinate versions |
| [Derivative/Basic](Derivative/Basic.agda), [Algebra](Derivative/Algebra.agda) | Constants, identity, complex-linear maps, sums, negation and subtraction |
| [Derivative/Product](Derivative/Product.agda), [Chain](Derivative/Chain.agda) | Pointwise product and chain rules, with global and coordinate forms; no continuity hypothesis on derivative functions |
| [Derivative/Factor](Derivative/Factor.agda) | A continuous supplied divided difference certifies a derivative, without computing a quotient |
| [Derivative/Coordinates](Derivative/Coordinates.agda) | Real coordinate remainders bounded by the full complex displacement; widening the controlling displacement by a norm bound |
| [Derivative/Polynomial](Derivative/Polynomial.agda) | Polynomial continuity and analytic correctness of the existing list-polynomial and monic formal derivatives; continuity of the polynomial derivative |
| [Holomorphic](Holomorphic.agda) | Ambient holomorphicity on a selected domain, entire functions, restriction and continuity; constants, identity, linear maps and polynomials are entire; entire functions are closed under algebra and composition |

The polynomial proof reuses `quotientPolynomialℂ`, its exact division identity,
and `polynomialDividedDifference-diagonalℂ`. It does not introduce another
formal differentiation algorithm. Derivative uniqueness reuses the native
real uniqueness theorem, after proving the horizontal restriction lemmas.
Separate horizontal derivatives alone are not claimed to imply complex
differentiability.

`IsHolomorphicOn U f` concerns an ambient function `f : ℂ → ℂ` at points
satisfying `U`; on open `U` it gives the usual notion for such a function.
Intrinsic functions on open subspaces use the coordinate derivative API;
the [right-half-plane logarithm](../Transcendental/Logarithm/README.md) is
now a proved example with ambient coordinate `fst`. General intrinsic
holomorphicity packaging remains separate.
`IsEntire f` supplies the unique derivative value at every point. Projecting
these actual witnesses gives a derivative function without selecting any
of the truncated local radii.

The internal [Estimates](Derivative/Estimates.agda),
[SmallError](Derivative/SmallError.agda) and
[Identities](Derivative/Identities.agda) modules share norm bounds, local
little-o operations and abstract-ring remainder identities across the rules.
The bounded-multiplication witness transformation has an explicit type to
avoid expensive elaboration of completed-real arithmetic.

## Elementary complex derivatives

The elementary-function facades now export
[`expℂHasSelfDerivative`](../Transcendental/Exponential/Derivative.agda),
[`sinℂHasDerivative` and `cosℂHasDerivative`](../Transcendental/Trigonometric/Derivative.agda),
proving `exp′ = exp`, `sin′ = cos` and `cos′ = -sin` for arbitrary complex
increments. They also export `expℂ-isEntire`, `sinℂ-isEntire` and
`cosℂ-isEntire`. These theorems concern the functions already defined in
`Transcendental`, and compose using the general complex chain rule, including
its coordinate version.

The exponential proof uses the native real derivatives directly. Write
`E(x + iy) = e(x) G(y)` with `G(y) = (c(y), s(y))`, and let `rₑ`, `r꜀`,
`rₛ` be the three embedded real derivative remainders. Its complex remainder
is the sum of

- `G(y′) rₑ`;
- `e(x) (r꜀ + i rₛ)`;
- `e(x) (G(y′) - G(y)) (x′ - x)`.

The first two terms are small by the real derivative estimates and norm
bounds on coordinate increments. The last is small by continuity of `G`.
The [abstract ring identity](../Transcendental/Exponential/Derivative/Algebra.agda)
and [generic separated-function proof](../Transcendental/Exponential/Derivative/Separated.agda)
keep normalization of completed real series out of the estimate. Instantiating
with native `expℝ`, `cosℝ`, `sinℝ` gives the exponential derivative.
Sine and cosine then follow from their existing exponential definitions,
using the sum, subtraction and chain rules.

This proves complex differentiability everywhere. The standard complex
power-series representations are now proved separately in the series layer.
Their higher derivative towers and Taylor representations at zero are now
proved too. General holomorphic Taylor representation and Cauchy integral
theory remain later results; neither is inferred from the word “entire”. No quotient of increments, choice of
radii, new real carrier or new real trigonometric functions is used.

## Uniform calculus for integrals

The [uniform derivative API](Derivative/Uniform.agda) keeps a separate
truncated radius for every tolerance and measures remainders relative to a
supplied coordinate. Its [indexed chain rule](Derivative/Uniform/Chain.agda)
and [real-parameter bridge](Derivative/Uniform/RealParameter.agda) support
the line-integral FTC. The [uniform factor criterion](Derivative/Uniform/Factor.agda)
uses joint radiuswise uniform continuity of a supplied divided difference;
it does not divide by a chord.

[Uniform inverse differentiation](Derivative/Uniform/Inverse.agda) derives
the inverse derivative from a bounded inverse coefficient and the forward
uniform estimate. A coarse estimate first gives a local Lipschitz bound by
absorbing half of the inverse chord; a finer estimate then bounds its
remainder. It never divides by a possibly zero increment or selects a
family of radii. This proves differentiation of a supplied continuous
logarithmic lift and its reciprocal line-integral formula. Uniform
exponential differentiation is derived independently from the derivative
at zero and the addition law.

[Pointwise inverse differentiation](Derivative/Inverse.agda) now uses the
same [chord estimate](Derivative/Inverse/Estimates.agda) without a global
bound: a single truncated rational bound for the reciprocal coefficient is
sufficient at the selected point. Pulling back `exp′ = exp` gives the
reciprocal derivative of every supplied continuous logarithmic branch.
The constructed right-half-plane branch is continuous and therefore has
this derivative throughout its intrinsic open domain.

## Next work

The [series layer](../Series/README.md) now proves complex power-series
differentiation from supplied derivative majorants, including uniform
estimates sufficient for the line-integral FTC. Its continuous factor is the
uniform sum of monomial divided differences, and its diagonal is the formal
derivative series.

The [open-subspace adapter](Derivative/OpenSubspace.agda) now converts
relative complex derivatives into ambient derivatives for supplied extensions.
The [interior series construction](../Series/PowerSeries/Interior/Holomorphic.agda)
proves holomorphicity from original sum representations and a single native
outer-radius norm-majorant witness, constructing derivative-series sums.

The [elementary series identities](../Series/PowerSeries/Exponential/HasSum.agda)
and [trigonometric identities](../Series/PowerSeries/Trigonometric/HasSum.agda)
now identify the existing functions with their standard complex power series,
with absolute native convergence everywhere and uniform convergence on bounded
families. Their formal coefficient derivatives agree with the established
function derivatives. The new [sine/cosine line-integral formulas](../Integration/LineIntegral/Trigonometric.agda)
are applications of the strict-interior series FTC.

The [derivative-tower API](Derivative/Tower.agda) now treats coherent explicit
families of derivatives and proves ambient uniqueness from order zero.
[Repeated power-series derivatives](../Series/PowerSeries/RepeatedDerivative/Tower.agda)
are constructed at every order on smaller bounded coordinate families from
one original outer-radius witness. The [Taylor theorem for represented
series](../Series/PowerSeries/Taylor/Interior.agda) gives uniform representation
on intrinsic open norm balls and a tail-majorant remainder estimate.

[Local coefficient uniqueness](../Series/PowerSeries/Taylor/Uniqueness.agda)
now follows from intrinsic tower uniqueness. A
[whole-interior derivative tower](../Series/PowerSeries/RepeatedDerivative/Interior.agda)
provides actual derivatives at every interior center, and
[reexpansion identification](../Series/PowerSeries/Taylor/Reexpansion.agda)
shows that any supplied convergent translated representation has the
canonical normalized coefficients. Exponential, sine and cosine have proved
Taylor representations at every center.
[General reexpansion](../Series/PowerSeries/Translation.agda) now proves native
convergence and representation for these canonical coefficients under
`norm(center) + r < R`, with uniform sums and majorant-tail remainder bounds.

[Reexpansion preserves every derivative](../Series/PowerSeries/Translation/Derivatives.agda)
by intrinsic tower uniqueness. The
[centered FTC](../Integration/LineIntegral/PowerSeries/Centered.agda) and its
[canonical reexpansion application](../Integration/LineIntegral/PowerSeries/Reexpansion.agda)
now handle certified paths bounded relative to arbitrary expansion centers.
[Finite local-series certificates](../Integration/Piecewise/PowerSeries.agda)
give endpoint formulas, closed-path zero and path independence across pieces
with different centers. The common primitive is an explicit hypothesis.

[Constructed power-series primitives](../Series/PowerSeries/Primitive/Domain.agda)
now have intrinsic uniform derivatives on the closed convergence ball at
the original nonnegative radius. Their normalization at zero is arbitrary.
The [parameter-value FTC](../Integration/LineIntegral/FundamentalTheorem/Along.agda)
and [series application](../Integration/LineIntegral/PowerSeries/Primitive.agda)
use those domain values without requiring an ambient primitive.

1. Prove that normalized primitives agree under Taylor reexpansion, and use
   that agreement for differently centered local descriptions of a contour.
   General Taylor representation from holomorphicity alone remains separate.
2. Extend the intrinsic right-half-plane domain and logarithm to further
   local domains, and add reciprocal differentiation and branch compatibility.
3. Extend the [line-integral FTC](../Integration/README.md), now proved for
   bounded uniform paths and finite piecewise contours, to broader sufficient
   hypotheses. Pointwise C¹ data alone are not yet upgraded to the uniform
   hypotheses. Cauchy integral theory remains separate.

## Initial calculus validation

- All 17 new or edited Agda files (16 new modules and the updated Complex
  facade) pass `agda-codex` with exit code 0 after their final edits.
- Both `Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` pass
  after integration of the public calculus imports.
- All 248 source snapshots in the expanded complex/root audit match current
  files and report zero holes, unsolved metas, constraints and warnings.
- The import audit reaches all 737 native Analysis modules, with 1136 Cubical
  modules transitively. There are no orphan Analysis modules, missing imports,
  cycles, Cauchy-real imports or choice imports. The audited sources contain
  no holes, postulates or new option pragmas.
- All 108 local links in the five development/progress documents resolve,
  and `git diff --check` passes.

## Elementary derivative validation

- All 10 new or edited Agda files (six new modules and four updates), the
  Complex facade and both Analysis entry points pass `agda-codex`, exit 0.
- All 254 audited complex/root source snapshots match the current files,
  with no holes, unsolved metas, constraints or warnings.
- All 743 native Analysis modules are reachable (1142 Cubical modules
  transitively), with no missing imports, cycles, orphans or Cauchy-real/choice
  dependencies. Source assumption and whitespace checks are clean.
- All 120 local links in the five updated development/progress documents
  resolve, and `git diff --check` passes.

## Uniform calculus and contour validation

The 2026-10-10 continuation checked all 34 changed Agda files and both
Analysis entry points with exit code 0. All 324 audited snapshots are
current and have no holes, metas, constraints or warnings. The
[integration notes](../Integration/README.md#validation) record the import,
source and documentation checks for this milestone.

## Local logarithm validation

The pointwise inverse theorem, constructed right-half-plane branch and
reciprocal integrals passed all 26 changed-file checks and both Analysis
entry points on 2026-10-10. The 343 audited snapshots are current and clean;
see the [integration validation](../Integration/README.md#validation).
