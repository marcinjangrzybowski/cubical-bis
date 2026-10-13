# Native complex analysis and the constructive FTA

Started 2026-10-08 at the user's request. Public entry point:

```agda
open import Cubical.Analysis.Complex
```

This development uses `ℂ = ℝ × ℝ`, where `ℝ` is Analysis's native sequential
completion. It imports no other real-number implementation. The directory's
[choice-free policy](../AGENTS.md) applies throughout.

The [library reuse audit](REUSE_AUDIT_2026-10-09.md) records the comparison
against the rest of Cubical, the shared implementations now used, and the
native representations and constructive boundaries retained.

The [missing-layer plan](DEVELOPMENT_GAPS_2026-10-09.md) identifies the next
foundations beyond the FTA development. The new
[Transcendental](Transcendental.agda) layer provides the complex exponential,
sine and cosine from native real functions, with algebraic laws and continuity.
The [differential-calculus layer](Calculus/README.md) adds pointwise and global
complex derivatives, uniqueness, continuity, algebra/product/chain rules, and
analytic correctness of the existing formal polynomial derivatives. The
complex exponential, sine and cosine now have their expected derivatives
and are proved entire. The [series layer](Series/README.md) now adds general
sums, absolute and uniform comparison, continuous power-series values from
supplied majorants, and geometric-series convergence on the Euclidean unit
disk. Cauchy products now have finite algebra, native Mertens and absolute
convergence, and power-series multiplication preserves radius majorants.
Power-series differentiation now uses supplied derivative majorants, with
continuous derivative values and uniform estimates along bounded uniformly
continuous coordinates. On strict interior radii, the original norm-majorant
witness now constructs the derivative convergence as well. Original sum
representations give holomorphicity, with constructed derivative-series sums.
The [integration layer](Integration/README.md) now adds coordinate Riemann
integrals and a constructive endpoint theorem for complex line integrals
along bounded uniformly differentiable paths, with path independence and
polynomial-primitive applications. It now includes finite piecewise contours,
concatenation, reversal and smooth reparameterization, exponential primitives,
and reciprocal integrals from supplied continuous logarithmic lifts. The
explicit positive unit circle has reciprocal integral `2πi`.
Power-series derivatives now have endpoint integrals and closed-path zero
from an outer original-majorant witness when the path has a strictly smaller
norm-radius bound. The standard complex exponential, sine and cosine series
now sum to the existing functions, with absolute native Cauchy convergence
everywhere and uniform convergence on bounded families. Their coefficient
identities give the sine/cosine endpoint integral formulas and closed-path
zero for every certified uniform path. Every finite power-series derivative
now has a constructed uniformly convergent series on smaller radii from the
original majorant alone. The resulting intrinsic derivative tower recovers
the original Taylor coefficients, with uniform representation and a
majorant-tail remainder bound. Explicit elementary derivative towers give
Taylor series at every complex center for exponential, sine and cosine.
Intrinsic derivative and tower uniqueness now imply local coefficient
uniqueness. Canonical derivatives on the whole open convergence ball give
Taylor coefficients at every interior center, independent of the outer
radius; any supplied convergent reexpansion has these coefficients.
[General reexpansion](Series/PowerSeries/Translation.agda) now constructs native
convergence of those coefficients when `norm(center) + r < R`, proves
representation of the original sum, and supplies uniform sums and remainder
bounds on smaller closed radii. Reexpansion now preserves every derivative.
The [centered power-series FTC](Integration/LineIntegral/PowerSeries/Centered.agda)
handles `norm(γ(t)-center) ≤ r < R`, and its
[canonical Taylor application](Integration/LineIntegral/PowerSeries/Reexpansion.agda)
constructs the local expansion from the original outer majorant.
[Piecewise local expansions](Integration/Piecewise/PowerSeries.agda) may have
different centers while representing a common primitive; endpoint formulas,
closed-path zero and path independence follow.
[Constructed power-series primitives](Series/PowerSeries/Primitive.agda)
now converge at the same nonnegative radius as the original native majorant.
Their intrinsic uniform derivatives give a
[path FTC](Integration/LineIntegral/PowerSeries/Primitive.agda) and
[finite-contour endpoint theorem](Integration/Piecewise/PowerSeries/Primitive.agda)
without a supplied ambient primitive. Next establish primitive compatibility
under Taylor reexpansion. Holomorphic Taylor representation without a supplied
series, the pointwise C¹-to-uniform upgrade and Cauchy integral theory remain
subsequent work. The
[right-half-plane logarithm](Transcendental/Logarithm/README.md) is now an
actual continuous branch with derivative `1/z`, agreement with the real
logarithm, and normalization at one. Paths with a supplied positive lower
bound on their real part have the reciprocal endpoint formula and
closed-path zero without a supplied logarithmic lift.

## Selected theorem and current boundary

The first proved milestone is **approximate factorization of every monic polynomial**.
For each degree `n`, coefficient vector `p`, and positive rational `ε`,
`approximateFundamentalTheorem` supplies

```agda
∥ Σ[ roots ∈ Vec ℂ n ]
    CoefficientCloseness p ε (linearFactors roots) ∥₁
```

The implicit leading coefficient is exactly one. Each stored coefficient is
approximated in both real coordinates. The truncation stays inside the
tolerance quantifier: this statement supplies neither an ordering of roots
across tolerances nor a chosen Cauchy sequence.

This is a finite-accuracy milestone toward the root-multiset approach in
[Richman, *The fundamental theorem of algebra: a constructive development
without choice*](https://msp.org/pjm/2000/196-1/pjm-v196-n1-p10-p.pdf).
Its applicability here is a design choice, not an identification of this
sequential completion with the paper's real-number construction.

**Proved for every degree:** [Approximate.agda](FundamentalTheorem/Approximate.agda)
inhabits both `ApproximateRootExistence` and `ApproximateFundamentalTheorem`
from [Statement.agda](FundamentalTheorem/Statement.agda). The public theorems
are `approximatePolynomialRoots` and `approximateFundamentalTheorem`.
They apply to arbitrary native complex coefficients without apartness,
root-separation, or supplied-descent hypotheses.

**Exact factorization under strong separability is now proved.**
[Separable/Factorization.agda](FundamentalTheorem/Separable/Factorization.agda)
exports `stronglySeparableFundamentalTheorem`. Given the positive formal
certificate `StronglySeparable p`, its conclusion is

```agda
∥ Σ[ roots ∈ Vec ℂ n ]
    ((linearFactors roots ≡ p) × PairwiseApartRoots roots) ∥₁
```

The certificate is truncated existence of finite coefficient lists `s,t`
satisfying the coefficient identity `s*p + t*p′ = 1`. The roots are actual
native complex numbers, and distinct indices have positively separated roots.
[Separable/Root.agda](FundamentalTheorem/Separable/Root.agda) also exports
`stronglySeparableRootExistence` for positive degree. These statements keep
their original hypotheses and conclusions from the checked survey catalogue.

**The general completed-multiset FTA is now proved.**
[Completion.agda](FundamentalTheorem/Completion.agda) exports
`completedMultisetFundamentalTheorem`, constructing a complete matching space
and an equivalence with all degree-indexed native monic coefficient vectors.
The equivalence agrees with finite Gaussian products and has whole local
moduli in both directions. It retains multiplicity without requiring a
chosen ordering or extraction of individual native roots.

**Finite near-zero nets are now proved.**
[NearZeroNet.agda](FundamentalTheorem/NearZeroNet.agda) exports `nearZeroNet`
with the original surveyed type. Its finite Gaussian centers have small
residual and cover every point with sufficiently small residual.
The [cluster layer](FundamentalTheorem/Clusters/README.md) proves spectral
stability, actual-root separation, finite block matching and coefficient
continuity, and exact separated clusters under strong separability. General
small separated factorization remains open.

**Further work:** a general exact FTA, global complex square-root selection,
and the argument principle are not established here. The finite-accuracy theorem does not manufacture a chosen
sequence of approximate roots or a native Cauchy witness from radiuswise
truncated existence.

## Implemented layers

| Layer | Results |
| --- | --- |
| Algebra | Native complex commutative ring, real embedding homomorphism, `i² = -1`, conjugation equivalence and homomorphism, multiplicative squared norm, inverse given positive squared norm |
| Metric and norm | Coordinate product premetric; `l1` norm with triangle and submultiplicative bounds, separation, and preservation of limits; Euclidean modulus with exact multiplicativity, triangle inequality, and comparison with the `l1` norm |
| Continuity | Constants and closure under addition, subtraction, negation, and joint multiplication; continuous fixed-scalar multiplication, real embedding, conjugation and natural powers; continuous maps preserve supplied coordinate limits |
| Completeness | Coordinatewise native witnesses and limits; equivalence with a merely supplied global product Cauchy modulus; uniqueness and arithmetic laws for limits |
| Contraction | Deterministic geometric iteration on a closed `l1` ball, an actual fixed point, and uniqueness; no continuity hypothesis beyond the contraction bound |
| Polynomials | Horner lists with algebra and exact remainder division; coefficient majorants and Lipschitz estimates; degree-indexed monic vectors with synthetic deflation, products of linear factors, and degree-preserving translation, finite monomial expansion, and isolation of one selected term with a modulus bound for the remainder |
| Root certificates | Finite coefficient bounds for a polynomial self-map give an exact fixed point and a root of its difference from `X` |
| Roots | Positive real roots of every nonzero natural degree via native exp/log, with uniqueness and strict order laws; nonnegative real square roots by deterministic geometric approximation, with uniqueness and algebra/order laws; local complex square roots; truncated nth roots away from zero, unit nth roots, and approximate nth roots of every complex number |
| Polar form | De Moivre laws, an actual right-half-plane argument from restricted arcsine, and a finite truncated cover giving arguments away from zero |
| Elementary functions | Native complex exponential, sine and cosine; Euler, addition, parity, real-axis agreement, algebraic Pythagorean identity, real/imaginary periods and continuity; exponential modulus and reciprocal laws; preservation of supplied sequence limits; complex derivatives `exp′ = exp`, `sin′ = cos`, `cos′ = -sin`, and entireness |
| Differential calculus | Division-free complex derivatives at a point, globally and along supplied coordinates; uniqueness, continuity, algebra/product/chain and pointwise inverse rules; continuous divided-difference criterion; list and monic polynomial derivatives; holomorphic/entire predicates and entire algebra/composition closure |
| Series | Coordinate partial sums and unique sums; algebra, conjugation and tails; native Cauchy comparison, absolute convergence and remainder bounds; uniform sums and continuity; power-series convergence and complex differentiation from supplied radius and derivative majorants; uniform derivative estimates; standard exponential/sine/cosine series identities with absolute and bounded-family uniform convergence; constructed repeated derivatives and Taylor representation for convergent series, with tail-majorant remainders; intrinsic local coefficient uniqueness, whole-interior derivative towers and canonical arbitrary-center coefficients; Cauchy products, Mertens and absolute-product bounds; power-series multiplication with radius-majorant closure; absolute geometric convergence on the Euclidean unit disk with `(1-z) * sum = 1` |
| Integration | Coordinate Riemann integrals and linearity; bounded uniform paths and segments; complex Newton–Leibniz; primitive line-integral endpoint formula, closed-path vanishing and path independence; automatic polynomial-derivative integrals |
| Logarithms | Actual continuous right-half-plane branch with reciprocal derivative and real-axis normalization; reciprocal endpoint integrals on quantitatively interior paths. Supplied polar witnesses and truncated nonzero-point existence remain available; no global branch is chosen. |
| Cancellation | Normalization to unit modulus; a truncated unit nth-power direction giving the exact two-term bound `modulusℂ (a +ℂ b ·ℂ uⁿ) = absℝ (modulusℂ a - modulusℂ b)` for positive-modulus coefficients |
| Finite selection | Truncated finite near-maximizers; balanced weighted-power scales; finite nonincreasing index chains with three adjacent equal indices; degree-dependent selected-term and remainder bounds |
| Quadratics | Exact unique root of `z²-z+c` in the quarter-radius ball when `normℂ c ≤ 1/8`, exact factorization for that family, and approximate factorization of every monic quadratic |
| Constructive approximate FTA | Uniform polynomial descent with an explicit degree-dependent contraction; finite iteration and geometric decay give approximate roots in every positive degree; synthetic deflation and coefficient continuity give approximate linear factorization in every degree |
| Completed-multiset FTA | Constructed separated Gaussian matching completion; canonical factor/root equivalence in every degree; finite-factor computation and whole local moduli in both directions |
| Constructive separable exact FTA | Coercivity and two-point derivative estimates, a uniform inverse bound from Bézout, one sufficiently accurate approximate root followed by deterministic Newton iteration, formal certificate propagation, and finite exact factorization into pairwise apart roots |
| Finite near-zero nets | Gaussian centers with small residual covering every sufficiently small-residual point; the original `NearZeroNetTheorem` is inhabited |
| Separated clusters | Universal spectral certificates from finite margins; openness and nonvacuity; actual-root separation; bijective matching and coefficient continuity of separated finite blocks; empty, single-cluster, and strongly separable exact cases |

The metric is the coordinate product metric; `normℂ` is the sum of coordinate
absolute values. The separate `modulusℂ` is the Euclidean modulus and satisfies
`modulusℂ (z ·ℂ w) ≡ modulusℂ z · modulusℂ w`. The comparison bounds are
`modulusℂ z ≤ normℂ z ≤ modulusℂ z + modulusℂ z`. Squared norm remains
available for exact inverse algebra.

`ComplexSeqWitness` is a pair of native real `SeqWitness` values. Combining
two global witnesses uses only finite truncation elimination. Radiuswise
convergence is never converted to a global Cauchy modulus. The contraction
proof instead constructs a deterministic sequence, bounds its successive
increments geometrically, and applies the existing native summability and
completion APIs in each coordinate.

The nonnegative square root uses the explicitly defined sequence
`positiveSqrtℝ (x + (2⁻ⁿ)²)`. Its successive differences are bounded by
`2⁻ⁿ`, giving a native Cauchy witness. Passing the square equation and
nonnegativity to its limit yields the unique nonnegative square root,
including at zero. No decision that `x = 0` or modulus selection is used.

## Why the quadratic proof is choice-free

For one requested accuracy, located order permits a small horizontal shift
into the right or left open half-plane. Each such point has an exact square
root: its construction uses positive real square roots and a witnessed
positive reciprocal. This proves `approximateSquareRoot` with a truncated
witness at that accuracy.

For `X²+bX+a`, put `t=b/2` and approximate a square root of `t²-a`. The two
candidate roots are `-t+w` and `-t-w`. Their linear coefficient is exactly
`b`; their constant coefficient differs from `a` by the square-root error.
This proves `approximateFundamentalTheorem-degreeTwo` without a modulus
selection or a decision that a discriminant is zero.

The general induction is similarly finite. An approximate root gives an
exact monic quotient with a small constant remainder. Continuity of
multiplication by `X-r` determines one sufficient tolerance for the quotient;
the induction hypothesis supplies its approximate factors at that tolerance.

## Polar form, higher roots, and finite descent

`cisℝ θ` has unit Euclidean modulus, preserves addition as multiplication,
and satisfies De Moivre's formula. On the right half-plane the argument is
constructed using the native restricted arcsine of the normalized imaginary
coordinate. Strict interval bounds, cosine positivity, and Pythagoras prove
reconstruction. A finite rotated cover gives `nonzeroPolarWitness` under
propositional truncation for any point of positive modulus.

Combining a polar witness with the positive real nth root and division of
its angle by the degree proves `nonzeroComplexRoot`. `unitComplexRoot` also
preserves unit modulus. A small horizontal perturbation then proves
`approximateComplexRoot` for every input, without testing whether it is zero.
Consequently, binomials `X^(suc n) + a` have approximate roots at every
requested accuracy, and exact truncated roots when `a` has positive modulus.

`normalizeℂ` constructs an actual unit direction from a point of positive
modulus, with an exact reconstruction equation. `oppositeCoefficientPower`
combines normalization, conjugation, and unit nth roots: for two coefficients
of positive modulus there merely exists a unit `u` making the modulus of
`a + b * u^(suc n)` exactly `abs (modulus a - modulus b)`. This supplies
the angular cancellation estimate for the descent proof.

[Descent/Finite.agda](FundamentalTheorem/Descent/Finite.agda) states the
one-step estimate as `PolynomialDescent n q`: for every monic
polynomial of degree `suc n` and every strict upper bound `c` for its value's
modulus at zero, there merely exists a point with modulus below `q * c`.
`finitePolynomialDescent` iterates a supplied estimate a finite number of
times, using degree-preserving translations to recenter the polynomial.
[Descent/Approximate.agda](FundamentalTheorem/Descent/Approximate.agda) uses
`0 ≤ q < 1` and geometric decay to reach one requested tolerance and then
applies the factorization reduction. No infinite descent sequence is selected.
[Descent/Uniform.agda](FundamentalTheorem/Descent/Uniform.agda) now supplies
this estimate for every degree, with `q = descentContraction n` and checked
proofs that `0 < q < 1`. The final theorem applies these reductions to that
constructed descent proof.

## Finite quantitative scale selection

The scale-selection part of the Kneser route is now implemented over native
reals. [Descent/Scale.agda](FundamentalTheorem/Descent/Scale.agda) starts from
one positive final coefficient and inserts the remaining nonnegative
coefficients in a finite scan. At each insertion, located order either keeps
the radius or replaces it by a positive weighted-power root. The output
retains an exact selected value and strict upper bounds with rational slack.

[Descent/NearMaximumChain.agda](FundamentalTheorem/Descent/NearMaximumChain.agda)
constructs only a finite chain. Prefix near-maxima ensure nonincreasing
indices, while rescaling preserves the global comparison bound. For `N`
nonconstant coefficients, `2N + 1` indices suffice to find three consecutive
equal indices. The extracted certificate includes the bounded offset and
comparison bounds at all three radii.

The implementation uses the degree-dependent radius shrink `q = 4^(-N)`.
The proved bound `N*q ≤ 1/4` lets every other term use a common bound instead
of summing two geometric tails. Set `L = (q^N)^(2N-1)`. For any nonnegative
coefficient vector with positive final entry, positive target `t`, and
positive rational error `ε`,
[Descent/Remainder.agda](FundamentalTheorem/Descent/Remainder.agda) proves
`finitePowerRemainderScale`: there merely exist `r > 0` and an index `k`
such that, writing `s = a[k] * r^(k+1)`,

```text
L*t < s + ε
s < t + ε
sum(i ≠ k, a[i] * r^(i+1)) ≤ s/4 + N*ε/q^N
```

`L` is strictly between zero and one. The reciprocal in the error allowance
has a witnessed positive denominator. All selections and truncation
eliminations are finite; no infinite index path, root sequence, or chosen
family over tolerances is introduced.

## From finite scales to the full approximate theorem

[Descent/PolynomialScale.agda](FundamentalTheorem/Descent/PolynomialScale.agda)
applies the scale theorem to the moduli of the nonconstant coefficients.
The implicit monic leading coefficient supplies the required positive entry.
[Polynomial/Cancellation.agda](Polynomial/Cancellation.agda) selects an
angular direction at exactly the chosen radius. Finite monomial expansion
and `evaluateMonic-selectedBound` bound the remainder's complex modulus.

If the constant modulus is
`A > 0`, take `t = A/2` and choose one rational `ε > 0` with
`ε ≤ t`, `ε ≤ L*t/2`, and `N*ε/q^N ≤ L*t/8`. Then the checked scale
bounds imply `L*A/4 < s < A` and a remainder smaller than `s/2`.
Optimal cancellation gives a new modulus below `(1-L/8)*A`.
[Descent/ErrorControl.agda](FundamentalTheorem/Descent/ErrorControl.agda)
constructs this finite error choice;
[Descent/Absorption.agda](FundamentalTheorem/Descent/Absorption.agda) proves
the inequalities; [Descent/Positive.agda](FundamentalTheorem/Descent/Positive.agda)
assembles the positive-constant descent. The contraction factor is positive,
strictly below one, and depends only on degree.

For any strict bound `A < c`, located order gives either `A < (1-L/8)*c`
or `0 < A`. In the first case zero already meets the requested bound; in
the second the positive-constant theorem applies. This proves uniform descent
without deciding whether the constant coefficient is zero. Finite translated
iteration then reaches any requested tolerance. Finally,
[Reduction.agda](FundamentalTheorem/Reduction.agda) uses synthetic deflation
and coefficient continuity to produce the approximate linear factors.

The proof is a finite adaptation of
[Geuvers–Wiedijk–Zwanenburg](https://www.cs.ru.nl/F.Wiedijk/pubs/kneser.pdf),
with weaker degree-dependent constants and a finite index certificate. It
uses neither a selected infinite descent path nor a polynomial IVT.

## Next work

The [constructive FTA survey and plan](FTA_SURVEY_2026-10-08.md) compares the
literature formulations and their relationship to the checked approximate
theorem. Formal polynomial derivatives, local Newton bounds, exact
factorization under a positive Bézout separability certificate,
quantitative root matching, and completed root multisets are now proved.
Stage 6 is developing general separated clusters; finite spectral estimates,
near-zero nets, and the strongly separable cluster case are checked. The next
step constructs persistent partitions and exact completed block factors.
The bounded uniform line-integral FTC is now available. Cauchy integral theory
and winding remain later clients or alternative proof routes.

The [statement catalogue](FundamentalTheorem/Formulations/README.md) was
checked before resuming proofs. The proof modules establish Bézout evaluation
identities and
[`localNewtonRoot : LocalNewtonRootTheorem`](Polynomial/Newton.agda), which
constructs an actual unique root in a specified ball from quantitative Newton
bounds. Those bounds are now derived uniformly from the formal separability
certificate, and exact finite deflation preserves that certificate.

The separable proof has four parts:

1. [Coercivity](Polynomial/Monic/Coercivity.agda) bounds every point with
   residual modulus below 1, using Horner induction and locatedness.
2. [Divided-difference estimates](Polynomial/Differential/Estimates.agda)
   bound the Newton remainder between any two points in a ball. Bézout
   bounds control the derivative inverse uniformly at small-residual centers.
3. [Root existence](FundamentalTheorem/Separable/Root.agda) chooses finitely
   many tolerances and one approximate center inside the truncated conclusion,
   then constructs the exact limit by deterministic contraction.
4. [Formal deflation](FundamentalTheorem/Separable/DeflationAlgebra.agda)
   computes the next coefficient certificate. Finite induction gives exact
   factors; the derivative's inverse proves positive separation of each new
   root from all remaining factors.

Stages 1–5 of the survey plan are complete, including the completed-multiset
construction described below.
The exact milestone passed all changed-module checks and both Analysis
entry-point checks with exit code 0; see the current
[validation checkpoint](../PROGRESS.md).

## Quantitative root matching

[Matching.agda](FundamentalTheorem/Matching.agda) exports three new inhabitants
of the statement catalogue:

- `quantitativeRootMatching : QuantitativeRootMatching` supplies a whole
  rational modulus for matching bounded-coefficient factorizations, with
  multiplicity and without a separability hypothesis.
- `quantitativeFactorContinuity : QuantitativeFactorContinuity` gives the
  converse coefficient estimate for matched bounded root configurations.
- `approximateFormulationsInterderivable : ApproximateFormulationsInterderivable`
  supplies the direct implications between approximate roots and
  coefficientwise approximate factorization.

The matching proof removes one nearby pair at a time. Finite located search
finds a small factor; explicit permutations move it to the front; synthetic
Horner division controls the remaining coefficients. A rational coercive
radius turns the coefficient bound into a common bound on all roots, which
persists after each removal. The constants are explicit and deliberately
loose. A matching remains truncated at its requested radius; no exact root
ordering or infinite selected family is inferred.

The matching completion and coefficient equivalence are now constructed in
[Completion.agda](FundamentalTheorem/Completion.agda). The
[construction notes](FundamentalTheorem/Completion/README.md) explain its
finite matching reflection, jointly approximable graph, deterministic
rational search, and native coefficient induction. No rational presentation
of an arbitrary native real is selected. Unrestricted exact native roots
remain a separate target.

The matching checkpoint passed all 21 new/edited-file checks and both
Analysis entry points with exit code 0. Its snapshot audit had 177
current successful targets; the import/source audit reported no forbidden
assumptions, missing modules, or cycles. See [PROGRESS.md](../PROGRESS.md)
for the checkpoint counts.

The completed-multiset checkpoint passed all 23 new or edited Agda-file
checks, the complex facade, and both Analysis entry points with exit code 0.
All 198 affected-module snapshots are current and have no holes, metas,
constraints, or warnings. The import/source audit also remains clean.

## Cluster preparation and near-zero nets

The [cluster notes](FundamentalTheorem/Clusters/README.md) describe the
2026-10-09 proof pass and the remaining general construction. Matching
transfers finite diameter slack and positive gaps to the catalogue's
universal tests. Separated blocks inherit bijections and a whole rational
coefficient modulus. The result preserves multiplicity, including repeated
roots within blocks.

Synthetic division also retains a prescribed small-residual point in an
approximate factorization. This proves that separated spectra have no
common actual root and supplies the coverage proof for `nearZeroNet`.
One Gaussian factorization supplies the centers; coercive bounds and
evaluation perturbation give small residual at each center. This remains
a finite construction at each accuracy.

`stronglySeparableClusterFactorization` proves the cluster conditions from
the existing exact apart-root factorization, with formal coefficient
reconstruction. It does not prove the general cluster theorem: lifting
stable finite partitions to exact factors of arbitrary native polynomials
is still required.

The cluster/net checkpoint passed all 18 new or edited Agda-file checks,
the complex facade, and both Analysis entry points with exit code 0.
All 213 affected-module snapshots are current and complete, and the
source/import audit remains clean; see [PROGRESS.md](../PROGRESS.md).

## Proof organization and validation

Pure coordinate identities are proved over an abstract commutative ring and
then specialized to native reals. Analytic estimates use the existing real
order and convergence APIs. Horner evaluation is opaque, with explicit
empty/cons computation paths, and one-step estimates are proved separately.
This prevents Agda from repeatedly unfolding completed real arithmetic.
The matching estimates likewise separate abstract Horner steps and finite
real-product order arguments from complex evaluation. Explicit computation
paths keep recursive completed terms out of elaboration of order proofs.
The Euclidean modulus has an opaque definition and separate algebraic and
order modules. Natural powers of the exponential are first proved with the
exponential map abstracted as a parameter, keeping its series construction
out of the induction. Polar reconstruction separates the generic angle lemma
from the restricted-inverse construction, and abstracts transport endpoints
to avoid expanding the completed trigonometric series during unification.
The local logarithm isolates its positivity certificate and proves clamped
subtype equalities through the curve coordinate. Its unit normalization
keeps the positive real input abstract.
Scale data uses dependent pairs, and finite index comparisons use a separate
case function. Reciprocal error allowances are opaque, and strict scale
reflection uses native order and continuity. These choices keep completed
real constructions out of routine comparison elaboration. The native monomial
interface also uses an opaque nonconstant term with an explicit computation law, so its
modulus proof does not normalize the underlying complex polynomial term.

The development uses no postulates, added options, or choice assumptions.
Validation runs `agda-codex` on every new module and changed facade, followed
by `Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda`. The complete
pass and transitive import audit are recorded in the main progress document.
