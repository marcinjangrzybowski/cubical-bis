# Missing complex-analysis layers — 2026-10-09

This follows the [library reuse audit](REUSE_AUDIT_2026-10-09.md). The starting
point has 197 modules, with unusually substantial polynomial and constructive
FTA developments, but several elementary complex-analysis APIs are absent.
The comparison is against the native real analysis, generic premetric and
algebra libraries, and the other complex development as a mathematical
reference. It does not identify the two real carriers.

## Preferred order

| Priority | Missing layer at the start of this pass | Why it belongs here / implementation route |
| --- | --- | --- |
| 1 | Complex exponential, sine and cosine | The native real exponential, sine, cosine and `cisℝ` already supply the construction. Define `expℂ(x+iy) = expℝ(x) cisℝ(y)` and the complex trigonometric functions from the two exponentials. Prove laws by shared ring algebra, and continuity by existing composition/product APIs. |
| 2 | General complex differentiation and holomorphic functions | Polynomial-specific formal derivatives and Newton estimates do not yet provide a derivative predicate for arbitrary `ℂ → ℂ`. Use a small-remainder estimate with `normℂ`, avoiding division by a possibly zero increment. Establish uniqueness, continuity, algebra and chain rules, then differentiate the elementary functions. |
| 3 | General complex series and power series | Coordinate sequence limits and geometric bounds exist, but there is no general complex series interface. Build sums and convergence coordinatewise from native real series; relate absolute convergence to the l1 norm. Do not turn radiuswise truncated convergence into a selected global modulus. |
| 4 | Apartness, reciprocal/domain API and local logarithms | A witnessed reciprocal and inverse bounds exist. Add a reusable binary apartness/domain interface and the remaining algebraic and continuity laws on the apart-from-zero domain. A local logarithm needs an explicit argument branch; a global logarithm on all nonzero complex numbers must not be advertised. |
| 5 | Complex path integrals and analytic theorems | First lift the existing real integral coordinatewise along a supplied differentiable path. Cauchy's theorem, Cauchy integral formula, argument principle and residue calculus require the preceding calculus plus domain/path infrastructure. |
| 6 | Cartesian unit circle and winding bridge | Native quotient-circle winding already exists in `Analysis/Circle`. Relate it to the unit-modulus complex subtype and complex loops through a proved equivalence and compatible metric/continuity maps. The argument principle will need this bridge; quotient-circle winding alone does not supply it. |

These are foundational gaps, separate from the remaining FTA-specific small
separated factorization obligations. Completing the latter is not required
before defining the elementary functions. A new derivative or convergence
predicate must be distinguished from a proved theorem about it.

## First implementation milestone

The selected first milestone is the elementary-function layer, with actual
laws and continuity proofs rather than statement-only placeholders:

- complete the parity/periodicity and continuity interface for `cisℝ`;
- expose continuity of the real embedding, conjugation and natural powers;
- add the complex exponential, its addition/Euler/conjugation/inverse laws,
  positive modulus and imaginary period;
- add complex sine and cosine, real-axis agreement, addition/parity identities,
  the algebraic identity `cos² + sin² = 1`, and continuity;
- expose preservation of supplied sequence limits through the generic
  premetric continuity theorem;
- construct a logarithm from a supplied polar witness, and prove that
  truncated logarithm existence is equivalent, by explicit implications, to
  positive apartness from zero.

The sine/cosine identity is an algebraic square identity, not the claim that
the squares of their complex moduli sum to one. The exponential uses the
existing real power-series value. The first milestone did not yet prove its
complex derivative; that proof is now supplied by the calculus extension
below. Identification with the standard complex power-series sum is now
proved in [Exponential/HasSum](Series/PowerSeries/Exponential/HasSum.agda).

The trigonometric algebra is factored over an abstract commutative ring with
explicit half and imaginary-unit equations. This keeps normalization of
native completion terms out of ring-solver proofs. The other Cauchy-real
complex modules are not imported, and no choice axiom or new postulate is used.

## Implemented modules

| Module | Main interface |
| --- | --- |
| [Continuity/Algebra](Continuity/Algebra.agda) | Continuity of real embedding, conjugation and every natural power |
| [Polar/Cis/Properties](Polar/Cis/Properties.agda), [Continuity](Polar/Cis/Continuity.agda) | Conjugation under negation, full-turn periodicity and continuity of `cisℝ` |
| [Exponential](Transcendental/Exponential.agda) | `expℂ`, zero/addition/conjugation/Euler laws, modulus `expℝ (re z)`, positive apartness, reciprocal/subtraction laws, imaginary full-turn period and continuity |
| [Trigonometric](Transcendental/Trigonometric.agda) | `sinℂ`, `cosℂ`, zero values, odd/even and addition laws, algebraic Pythagorean identity, real-axis agreement, Euler decomposition, half/full-turn values, real full-turn period and continuity |
| [Logarithm](Transcendental/Logarithm.agda) | Actual logarithm from a supplied polar witness; both implications between positive apartness and truncated exact logarithm existence |
| [Sequence/Continuous](Sequence/Continuous.agda), [Transcendental/Sequence](Transcendental/Sequence.agda) | Generic continuous-map preservation of supplied limits, with exponential/sine/cosine specializations |

The [Transcendental facade](Transcendental.agda) is exported from the public
[Complex API](../Complex.agda). The helper algebra remains parameterized over
an arbitrary commutative ring. A private opaque alias for `expℝ` controls
normalization during coordinate proofs; its value, zero and addition laws
come directly from the existing real exponential API.

The [differential-calculus milestone](Calculus/README.md) now supplies the
remainder-based definition, pointwise uniqueness and continuity, basic algebra,
product and chain rules, and analytic correctness of the existing polynomial
derivatives. The holomorphic/entire interfaces include polynomial examples and
closure laws. The elementary derivative extension now proves
`expℂHasSelfDerivative`, `sinℂHasDerivative` and `cosℂHasDerivative`, and
entireness of all three functions. The exponential remainder is assembled
from the three existing native real derivative estimates; the trigonometric
derivatives reuse the complex chain and algebra rules. Each radius remains
independently truncated, with no global modulus selected. See the
[proof notes](Calculus/README.md#elementary-complex-derivatives).

The [series foundations](Series/README.md) are now implemented. The intrinsic
right-half-plane domain and its continuous logarithm with reciprocal
derivative are also now constructed. General domain calculus and reciprocal
differentiation remain further work. The user-requested integration milestone
is now supplied by the [bounded uniform line-integral layer](Integration/README.md).

## Series checkpoint and next implementation

The new layer supplies coordinate partial sums and unique sums, algebra and
conjugation, tail removal/reconstruction, finite and infinite norm bounds,
absolute comparison from native Cauchy witnesses, uniform convergence and
continuity. Power series have absolute and uniform convergence from a
supplied real radius-majorant witness and continuous values along bounded
continuous coordinates. The geometric series converges on the full Euclidean
unit disk and satisfies `(1-z) * sum = 1`.

The proofs reuse `Real.Series.Base`, `Operations`, `Tails`, `Absolute` and
`Uniform`, and the existing complex sequence API. They keep a supplied sum
separate from a native Cauchy witness. Radiuswise truncated tail bounds are
not promoted to a selected modulus. The [series notes](Series/README.md)
describe the precise interfaces and the l1/Euclidean radius distinction.

The next selected addition, [Cauchy products](Series/Product.agda), is now
implemented: finite convolution laws, native Mertens with only one absolute
factor, absolute native Cauchy closure and an absolute-sum bound. The
[power-series bridge](Series/PowerSeries/Product.agda) proves multiplication
of values, and the [radius bound](Series/PowerSeries/Product/Bounds.agda)
preserves native Cauchy radius majorants without radius loss. These reuse
real convolution, real Mertens and absolute-product estimates, and generic
commutative-ring power laws. The geometric series now supplies absolute
native Cauchy data on the full Euclidean unit disk, so it is directly
compatible with these product theorems.

Continue in this order:

1. Power-series differentiation from supplied derivative majorants is now
   proved, using the uniform sum of monomial divided differences. The
   uniform version supplies endpoint line integrals and closed-path zero.
   Strict-interior convergence, ambient differentiation and holomorphicity
   now follow from one original outer-radius norm-majorant witness. The
   interior FTC derives its derivative witness too. Every finite repeated
   derivative now has a constructed native majorant and uniform sum on smaller
   radii. Coherent derivative towers and Taylor coefficient recovery give
   uniform Taylor representation for supplied convergent series, with a
   majorant-tail remainder estimate.
2. The existing complex exponential, sine and cosine are now identified
   with their standard complex power-series sums, preserving their definitions
   and derivative theorems. Native absolute convergence holds everywhere and
   uniform convergence holds on bounded families. The sine/cosine endpoint
   integrals follow from the strict-interior series FTC. Explicit ambient
   derivative towers and their series sums now give Taylor representation at
   every center for all three functions. Intrinsic open-subspace derivative
   and tower uniqueness prove local coefficient uniqueness. A canonical
   derivative tower on the whole open convergence ball constructs Taylor
   coefficients at any interior center; every supplied convergent reexpansion
   is identified with them. [General reexpansion](Series/PowerSeries/Translation.agda)
   now has native convergence for `norm(center) + r < R`, representation of
   the original sum, uniform representation and summable-tail remainder bounds.
   Finite binomial translation, a larger-radius coefficient bound and a common
   geometric modulus justify the limit interchange without choice.
   [Reexpansion preserves all derivatives](Series/PowerSeries/Translation/Derivatives.agda).
   The [centered FTC](Integration/LineIntegral/PowerSeries/Centered.agda), its
   [canonical Taylor application](Integration/LineIntegral/PowerSeries/Reexpansion.agda),
   and [finite piecewise local-series FTC](Integration/Piecewise/PowerSeries.agda)
   are now proved. [Complex primitives](Series/PowerSeries/Primitive.agda)
   now reuse the real formal-primitive coefficients and converge at the same
   nonnegative radius as the original majorant. Their intrinsic domain
   derivative gives the [path FTC](Integration/LineIntegral/PowerSeries/Primitive.agda)
   and [finite-contour theorem](Integration/Piecewise/PowerSeries/Primitive.agda)
   without a supplied ambient primitive. Next prove compatibility of these
   normalized primitives under Taylor reexpansion, then use it for coherent
   differently centered local descriptions.
   Holomorphic Taylor representation without an assumed series and Cauchy
   integral theory remain separate work.
3. Extend the apartness/domain, reciprocal/local-logarithm and integration
   layers in the main priority table.

## Complex line-integral FTC milestone

The user requested integration before the remaining power-series work. The
[integration API](Integration/README.md) defines coordinate Riemann integrals
and actual line integrals of `f(γ(t))*γ′(t)`. A bounded uniform complex chain
rule transfers a primitive estimate along the curve to the two parameter
coordinates; the existing real Newton–Leibniz theorem then constructs the
integral with value `F(γ(b))-F(γ(a))`.

The path class supplies uniform coordinate derivatives and a rational speed
bound. The general theorem additionally consumes a uniform primitive estimate
along the path and a bound on `f ∘ γ`. Polynomial primitives have both
estimates constructed from existing coefficient/Newton bounds. Closed paths,
path independence and straight segments are included. No integrability
hypothesis is needed in the endpoint theorem, and no choice axiom is used.

The continuation now supplies finite piecewise paths using existing graph
paths, concatenation, reversal, and smooth reparameterization with the actual
chain-rule velocity. Substitution uses coordinate accumulation under supplied
standard uniform continuity. Radiuswise continuity supplies the required
integrand bounds without choosing moduli. Polynomial and exponential endpoint
formulas extend to finite contours.

The uniform factor criterion and uniform inverse theorem support weaker
sufficient hypotheses and differentiation of supplied continuous logarithmic
lifts. Such a lift gives the reciprocal integral as its endpoint change; a
single-valued branch gives closed-path zero. An explicit positive circle with
lift `(0,t)` instead has reciprocal integral `2πi`, proved nonzero.

The [local logarithm milestone](Transcendental/Logarithm/README.md) now
constructs the right-half-plane branch, proves its continuity, reciprocal
derivative and positive-real normalization, and gives reciprocal integrals
for certified paths with an explicit positive lower bound on their real part.
The argument reuses the existing polar arcsine construction. Pointwise and
uniform inverse differentiation share one absorption estimate; modulus and
positive reciprocal continuity and real logarithm uniformity are reusable
supporting results.

Next integration priorities are the pointwise C¹-to-uniform compact-domain
upgrade, further branch domains and compatibility, and broader contour
applications. Elementary complex-series identification and the sine/cosine
endpoint formulas are now proved.
The current theorems do not derive a primitive from holomorphicity. Cauchy's
theorem, the integral formula, and the Cartesian-circle/winding bridge remain
separate obligations.

## First-milestone validation

- All 21 new or edited Agda files (19 new modules and two updated facades)
  pass `agda-codex` with exit code 0 after their final edits.
- `Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` both pass
  after the public imports were integrated.
- The source-hash audit validates all 232 snapshots covering the complex
  modules, supporting root modules and public entry points, with no holes,
  unsolved metas, constraints or warnings.
- The import audit reaches all 721 native Analysis modules and 1120 Cubical
  modules transitively. It finds no missing imports, orphan Analysis modules,
  cycles, Cauchy-real imports or choice imports. The audited sources contain
  no holes, postulates or new option pragmas.
- All 88 local links in the four updated development/progress documents
  resolve, and `git diff --check` passes.

## Local logarithm checkpoint

The intrinsic half-plane branch, its derivative and its reciprocal integral
applications are checked and publicly exported. All 26 changed Agda files
and both Analysis entry points pass with exit code 0; the 343 current
snapshots have no holes, metas, constraints or warnings. See the
[integration validation](Integration/README.md#validation) for the final
source and import audit.
