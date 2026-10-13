# Which fundamental theorem of algebra is proved here?

This literate Agda guide compares the formulations in
`Cubical.Analysis.Complex.FundamentalTheorem`, against the source tree on
2026-10-13. Its organizing question is **what kind of root information a
theorem returns, under which hypotheses**.

Three central results are proved: approximate roots and factorization for
arbitrary native monic polynomials, exact factorization under strong
separability, and a canonical completed root multiset for every native
monic polynomial. The unrestricted exact-root theorem remains a statement
without a supplied proof in this development.

The code blocks below are part of one Agda module. Bindings to existing
proofs check that the advertised inhabitants have the stated types. A
binding whose type is `Type₀` merely names a mathematical statement; it
does **not** prove that statement. The prose, literature comparisons, and
claims about absent implementations are a source review, rather than
propositions verified by Agda. All guide bindings are private.

```agda
module Cubical.Analysis.Complex.FundamentalTheorem.FormulationsGuide where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_)
open import Cubical.Data.Sigma using (Σ; _×_)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Complex.Base using (ℂ)
open import Cubical.Analysis.Complex.Polynomial.Monic
  using (MonicPolynomial; linearFactors)
import Cubical.Analysis.Complex.FundamentalTheorem as FTA
import Cubical.Analysis.Complex.Polynomial.Newton as Newton
```

## The common setting

Here `ℂ = ℝ × ℝ`, with the native sequential completion from
[Real/Base.agda](../../Real/Base.agda). A limit can have already completed
reals as its terms. Rational density gives truncated approximants at each
radius; it does not provide a rational sequence naming every native real.
The [Analysis policy](../../AGENTS.md) excludes adding countable-choice
assumptions to bridge that gap.

`MonicPolynomial n` stores the `n` coefficients below the implicit leading
coefficient one. Thus the degree is known, including the degree-zero
polynomial one. Root-existence statements use degree `suc n`.
`CoefficientCloseness` bounds both real coordinates of every coefficient;
`MatchingClose` similarly uses coordinate closeness. The separate
`normℂ` is the sum of coordinate absolute values, while `modulusℂ` is the
Euclidean modulus. These are related metrics, but not identical definitions.

The logical distinctions matter:

| Form of output | Information supplied |
| --- | --- |
| `Σ[ z ∈ ℂ ] p(z) ≡ 0` | An actual root together with its equation |
| `∥ Σ[ z ∈ ℂ ] p(z) ≡ 0 ∥₁` | Mere existence of an exact root; no general root selector |
| `∀ ε → ∥ Σ[ z ∈ ℂ ] p(z) ≈ε 0 ∥₁` | Mere existence of a small-residual point at each tolerance |
| `¬ ¬ ∥ Σ[ z ∈ ℂ ] p(z) ≡ 0 ∥₁` | Refutation of the claim that there are no roots |
| A point of the completed matching space | A canonical unordered root object retaining multiplicity |

These outputs cannot be interchanged just by changing notation. In
particular, moving truncation outside an infinite family of approximations
requires an additional construction.

## Proved formulations

Each formulation in this section has a supplied proof. Conditional results
retain their hypotheses explicitly; the more general open targets follow
in a separate section.

### Approximate roots and approximate linear factorization

**Formulation.** For every positive rational tolerance, a positive-degree
monic polynomial has a small-residual point. For every degree and tolerance,
its coefficients can be approximated by those of a product of linear
factors. The candidate factors need not be exact roots of the original
polynomial.

**Status: both formulations are proved, for arbitrary native coefficients.**
The definitions are in [Statement.agda](Statement.agda); the inhabitants
are in [Approximate.agda](Approximate.agda). No separability, coefficient
presentation, or supplied convergence assumption is required.

```agda
private
  approximate-roots : FTA.ApproximateRootExistence
  approximate-roots = FTA.approximatePolynomialRoots

  approximate-factors : (n : ℕ) (p : MonicPolynomial n) (ε : ℚ₊) →
    PT.∥ Σ[ roots ∈ Vec ℂ n ]
      FTA.CoefficientCloseness p ε (linearFactors roots) ∥₁
  approximate-factors = FTA.approximateFundamentalTheorem

  approximate-equivalence : FTA.ApproximateFormulationsInterderivable
  approximate-equivalence = FTA.approximateFormulationsInterderivable

  exact-factorization-gives-approximation :
    ∀ {n} (p : MonicPolynomial n) → FTA.ExactFactorization p →
    (ε : ℚ₊) → FTA.ApproximateFactorization p ε
  exact-factorization-gives-approximation =
    FTA.exactFactorization→approximate
```

The root proof uses a degree-dependent contraction of the residual and
finitely many descent steps for the requested tolerance. Synthetic
division converts approximate roots to approximate factors. The reverse
reduction, in
[Matching/ApproximateEquivalence.agda](Matching/ApproximateEquivalence.agda),
uses coefficient and root bounds to control evaluation at one candidate.
Thus the displayed interderivability is backed by actual functions in both
directions.

Truncation remains **inside** the tolerance quantifier. Repeatedly asking
for better accuracy does not establish compatible root labels, summable
displacements, or an exact root. This is why this formulation deserves its
own section even though classically it accompanies the usual FTA.

### Exact factorization under strong separability

**Formulation.** Supply a positive algebraic separability certificate:
finite coefficient lists `s,t` satisfying the formal coefficient identity

\[
                  s\,p+t\,p'=1.
\]

`StronglySeparable p` is the propositional truncation of this certificate.
Polynomial identity compares zero-extended coefficients, so trailing zeros
in lists do not change its meaning. This is stronger constructive input
than the negative assertion that the polynomial has no multiple root.

**Status: exact roots and exact factorization into pairwise apart roots are
proved.** Apartness means a strictly positive Euclidean distance for
different indices, not just a negated equality.

```agda
private
  separable-roots : FTA.StronglySeparableRootExistence
  separable-roots = FTA.stronglySeparableRootExistence

  separable-factors : (n : ℕ) (p : MonicPolynomial n) →
    FTA.StronglySeparable p →
    PT.∥ Σ[ roots ∈ Vec ℂ n ]
      ((linearFactors roots ≡ p) × FTA.PairwiseApartRoots roots) ∥₁
  separable-factors = FTA.stronglySeparableFundamentalTheorem

  certificate-survives-deflation : FTA.SeparableDeflation
  certificate-survives-deflation = FTA.separableDeflation

  quantitative-local-root : FTA.LocalNewtonRootTheorem
  quantitative-local-root = Newton.localNewtonRoot
```

The implementation is in [Separable/Root.agda](Separable/Root.agda),
[Separable/Deflation.agda](Separable/Deflation.agda), and
[Separable/Factorization.agda](Separable/Factorization.agda). It bounds
small-residual points, uses Bézout data to obtain an inverse-derivative
bound, and takes one sufficiently accurate approximate center. A
fixed-derivative Newton map then has a deterministic contracting iteration.
The local theorem returns an actual root, a ball bound, and uniqueness in
that ball, under explicit inverse, correction, and error estimates.

The separable-root theorem derives those estimates rather than requiring
them as extra caller assumptions. Finite deflation propagates the formal
certificate and produces all roots under the final truncation. This uses
finite witness handling and an explicitly constructed iteration, not an
infinite selection of independent approximate roots.

The mathematical counterpart is Lubarsky and Richman,
[*Zero sets of univariate polynomials*](https://arxiv.org/html/1510.00732),
Theorem 4.4 (2015 preprint). Our checked statement is its native-carrier
adaptation. Dropping `StronglySeparable p` would change the theorem; the
code contains no such unrestricted conclusion.

### A canonical completed multiset of roots

**Formulation.** Replace an ordered vector of native roots by a point of a
completed space of finite root configurations. For each fixed degree `n`,
construct this space and an equivalence between it and `MonicPolynomial n`.
Multiplicity is retained: for example, the configurations `(a,a,b)` and
`(a,b,b)` have different multiplicities even though their underlying sets
can agree.

**Status: proved for all native monic polynomials, including repeated
roots.** [Completion.agda](Completion.agda) inhabits the entire specification
in [Formulations/Completion.agda](Formulations/Completion.agda).

```agda
private
  completed-multiset-FTA : FTA.CompletedMultisetFundamentalTheorem
  completed-multiset-FTA = FTA.completedMultisetFundamentalTheorem

  completed-spectrum-equivalence : (n : ℕ) →
    FTA.MatchingCompletion.Carrier (FTA.rootMultisetCompletion n)
      ≃ MonicPolynomial n
  completed-spectrum-equivalence = FTA.completedFactorEquivalence

  coefficients-recovered : (n : ℕ) (p : MonicPolynomial n) →
    FTA.completedFactors n (FTA.completedRoots n p) ≡ p
  coefficients-recovered = FTA.factors-roots

  matching-with-multiplicity : FTA.QuantitativeRootMatching
  matching-with-multiplicity = FTA.quantitativeRootMatching

  factors-vary-continuously : FTA.QuantitativeFactorContinuity
  factors-vary-continuously = FTA.quantitativeFactorContinuity
```

The base configurations are vectors of Gaussian rationals. Finite matching
at a radius means truncated existence of a bijection of finite indices
matching all entries within that radius. The construction separates this
premetric and completes it. The resulting package supplies a dense
isometric insertion, regular completeness, and sequential completeness
for a supplied truncated whole Cauchy witness.

`completedFactors` and `completedRoots` are inverse maps. The specification
also includes agreement with Gaussian finite products and local continuity
in both directions. Each local continuity assertion contains **one
truncation around a whole modulus function**. It is not a family of
separately truncated choices of tolerances. The quantitative finite
matching and factor-continuity results construct actual rational modulus
functions from a degree, a bound, and the requested accuracy.

The crucial existence steps are visible in
[Completion/FiniteSearch.agda](Completion/FiniteSearch.agda) and
[Completion/CoefficientInduction.agda](Completion/CoefficientInduction.agda).
For rational coefficients, a decidable error test and least-witness search
give a deterministic sequence of approximations. Native completion
induction, with reflected Cauchy witnesses and unique graph fibers,
extends the construction to arbitrary coefficients. It does not first
assign rational names to all native coefficients.

Richman's [*The fundamental theorem of algebra: a constructive development
without choice*](https://msp.org/pjm/2000/196-1/pjm-v196-n1-p10-p.pdf)
(Pacific Journal of Mathematics 196, 2000, pp. 213–230), especially its
multiset and completion sections, supplies the central mathematical
perspective. The implementation uses Gaussian configurations and the
native completion, not an asserted identification with the paper's carrier.
Its finite matching argument also follows the algebraic direction of
[Ruitenburg, Lemma 3.10](https://ncatlab.org/nlab/files/Ruitenburg-Roots.pdf).

This theorem gives an actual canonical **completed object**, but no
extraction of a vector of individual native roots. A completion need not
come with a surjection from native root vectors. Likewise, arbitrarily
close finite matchings do not automatically supply one exact permutation.
The equivalence therefore does not discharge the unrestricted exact FTA
discussed among the open formulations below.

### Finite near-zero nets

**Formulation.** Given a positive-degree monic polynomial and accuracy
`ε`, provide a finite nonempty vector of Gaussian centers and a positive
residual tolerance `δ`. Each center has residual below `ε`, and **every**
point with residual below `δ` is within `ε` of some center. The whole
finite package is propositionally truncated.

**Status: proved for arbitrary native coefficients.**

```agda
private
  finite-near-zero-net : FTA.NearZeroNetTheorem
  finite-near-zero-net = FTA.nearZeroNet

  small-residual-points-are-bounded : FTA.BoundedApproximateRoots
  small-residual-points-are-bounded = FTA.boundedApproximateRoots
```

[NearZeroNet.agda](NearZeroNet.agda) proves the original
[LocalRoots specification](Formulations/LocalRoots.agda). Synthetic
division retains any supplied small-residual point in an approximate
factorization. Matching to one accurate Gaussian factorization then puts
that point near a center. Coercivity and evaluation estimates bound the
centers' residuals. The implementation uses as many centers as the degree;
repetitions are allowed, while the statement permits any nonempty finite
number of centers.

This controls the entire sufficiently small-residual region, rather than
only finding one approximate root. It does not assert that a center is an
exact root, nor does it produce compatible nets at all accuracies.

A related quantitative formulation appears in Peshev and Skordev,
[*A Subrecursive Refinement of the Fundamental Theorem of Algebra*](https://store.fmi.uni-sofia.bg/fmi/logic/skordev/refinement.pdf)
(CiE 2006, LNCS 3988, pp. 435–444), Theorem 2. Their representation-based
complexity result is stronger algorithmic information than this native
finite-net theorem; no matching complexity bound is claimed here.

### Exact factorization in small degrees and a quadratic family

**Formulation.** Restrict exact linear factorization to degree zero,
degree one, or a quantitative family of quadratics.

**Status: proved.** [Factorization.agda](Factorization.agda) handles the
constant polynomial one and every monic linear polynomial:

```agda
private
  constant-factors : FTA.ExactFactorization []
  constant-factors = FTA.exactFactorization-constant

  linear-factors : (a : ℂ) → FTA.ExactFactorization (a ∷ [])
  linear-factors = FTA.exactFactorization-linear
```

[Quadratic.agda](Quadratic.agda) also proves
`exactFactorization-smallQuadratic`: exact factorization of `X² − X + c`
when `normℂ c ≤ 1/8`. Its root is constructed by contraction in a ball of
radius `1/4`. The general monic-quadratic result in that module is
approximate, as covered above.

There are useful proved conditional reductions as well.
`exactFactorization-fromRoot` combines a supplied root and an exact
factorization of the monic quotient. `exactFactorization-quadraticRoot`
needs only a supplied root of a quadratic, since the quotient is linear.
These conclusions are exact; the root arguments remain hypotheses.

### Exact separated-cluster special cases

**Formulation.** Produce an exact factorization into positive-degree
monic clusters with small spectra and positive gaps, under hypotheses
that permit constructing those clusters. The output includes total degree
and a formal coefficient-product identity.

**Status: proved for strongly separable polynomials, for the empty case,
and for a positive-degree polynomial already certified to have small
spectrum.** Strong separability supplies pairwise apart linear clusters at
any requested radius:

```agda
private
  separable-clusters : (n : ℕ) (p : MonicPolynomial n) (ε : ℚ₊) →
    FTA.StronglySeparable p → PT.∥ FTA.ClusterFactorizationData p ε ∥₁
  separable-clusters = FTA.stronglySeparableClusterFactorization

  one-already-small-cluster : ∀ {n} (p : MonicPolynomial (suc n))
    (ε : ℚ₊) → FTA.SpectrumDiameterBelow p ε →
    FTA.ClusterFactorizationData p ε
  one-already-small-cluster = FTA.singletonClusterFactorization
```

[Clusters.agda](Clusters.agda) also exports the empty case, robust spectral
certificates, openness, nonvacuity, separation of supplied actual roots,
and finite block matching and coefficient continuity. The single-cluster
case above **requires** the diameter certificate; it does not prove every
spectrum arbitrarily small.


The spectral predicates are those of
[Formulations/Clusters.agda](Formulations/Clusters.agda): they control every
sufficiently accurate finite factorization. The stated hypotheses are
part of these proved special cases. The general formulation is discussed
separately among the open targets below.

## Formulations not yet proved

The capitalized types in `Formulations` are a catalogue of obligations.
Successful compilation verifies those definitions as well as any supplied
inhabitants; it does not turn every catalogue entry into a proved theorem.
This guide links its positive claims to proof terms and labels the other
formulations as open. The implication types in `Formulations/Relations`
are likewise definitions of targets; one should inspect an actual
inhabitant before treating a catalogue arrow as a formalized reduction.

### Unrestricted exact roots and exact linear factorization

**Formulation.** Every positive-degree monic polynomial has an exact native
complex root. The factorization version says that every degree-`n` monic
polynomial is exactly a product of `n` linear factors. Both catalogue
statements use propositional truncation for existence:

\[
  \forall p\text{ of positive degree},\quad
  \left\|\sum_{z:\mathbb C}p(z)=0\right\|,
  \qquad
  \forall p\text{ of degree }n,\quad
  \left\|\sum_{r:\mathbb C^n}\prod_i(X-r_i)=p\right\|.
\]

**Status: open in this development.**
[Formulations/Basic.agda](Formulations/Basic.agda) defines
`ExactRootExistence` and `ExactFundamentalTheorem`. The following code checks
their well-formedness only; neither right-hand side is an exact-root proof.

```agda
private
  GeneralExactRootStatement : Type₀
  GeneralExactRootStatement = FTA.ExactRootExistence

  GeneralExactFactorizationStatement : Type₀
  GeneralExactFactorizationStatement = FTA.ExactFundamentalTheorem
```

**A possible exact-descent formulation.**
`CoherentVanishingResidualConstruction`, in
[Formulations/Relations.agda](Formulations/Relations.agda), asks for one
truncated package containing a sequence of points, its whole native Cauchy
witness, and convergence of the residuals to zero. That construction is
also open. The file defines the implication types
`CoherentDescentImpliesExactRoots` and
`ExactRootFactorizationInterderivable`; it does not supply their proofs.

For comparison, Geuvers, Wiedijk, and Zwanenburg's
[*A Constructive Proof of the Fundamental Theorem of Algebra without using
the Rationals*](https://www.cs.ru.nl/F.Wiedijk/pubs/kneser.pdf), Lemmas 4–5,
uses descent controlling both residuals and displacement, then a Cauchy
iteration. This is useful proof guidance. The present finite descent does
not by itself construct the coherent infinite package above.

“Open” here records the implementation boundary. It is not an impossibility
or independence result for this particular native real carrier.

### General exact factorization into small separated clusters

**Formulation.** For every `ε`, factor a monic polynomial exactly into
positive-degree monic factors whose spectra each have diameter less than
`ε`, with a positive gap between different factors. The factors may have
degree greater than one and may contain repeated roots.

The native predicates in
[Formulations/Clusters.agda](Formulations/Clusters.agda) test **all**
sufficiently accurate finite factorizations. A diameter certificate gives
a tolerance making every such configuration small; a separation
certificate gives a common positive gap for two such families. This
avoids presupposing an enumeration of exact roots. The requested output
also records total degree and an exact formal coefficient-product identity.

**Status: the general theorem is unproved.** The type
`SmallSeparatedFactorization` has no general inhabitant in this development.
The exact special cases and finite estimates appear in the proved section.

The remaining general construction needs persistent separated blocks,
their completed coefficient factors, and the exact reconstruction law.
Finite block estimates alone do not construct those limits. The precise
remaining steps are recorded in [Clusters/README.md](Clusters/README.md).
The corresponding literature theorem is
[Lubarsky–Richman, Theorem 3.2](https://arxiv.org/html/1510.00732).

### Weak FTA: exact-root existence under double negation

**Formulation.** A positive-degree monic polynomial cannot have no roots:

\[
              \neg\neg\left\|\sum_{z:\mathbb C}p(z)=0\right\|.
\]

**Status: statement only.** `WeakFundamentalTheorem` in
[Formulations/Basic.agda](Formulations/Basic.agda) has no supplied
inhabitant here. It is a negative conclusion about exact roots; it does
not return a root or truncated root witness. Conversely, arbitrarily
small residuals alone do not supply this negative-existence proof.

[Lubarsky–Richman, Theorem 4.5](https://arxiv.org/html/1510.00732) proves
the weak FTA in their setting after developing separability and finite
algebra. That literature result has not been imported as a proof for the
native carrier. Calling the theorem “weak” describes its logical output,
not the amount of formalization already completed.

### Exact roots from presentations, and restricted coefficient families

**Formulation.** Add explicit rational approximation data to the input.
`RationalPresentationℂ z` contains a sequence of Gaussian rationals, a
whole rational-tolerance-to-index modulus, and a convergence proof to `z`.
`CoefficientPresentations p` supplies this data for each coefficient.

**Status: all the following exact targets are statements only.**

| Catalogue type | Additional input and requested output |
| --- | --- |
| `PresentedExactRootExistence` | Coefficient names; truncated exact root together with its name |
| `PresentedRootAlgorithm` | Coefficient names; an actual exact root and name, without output truncation |
| `PresentedFundamentalTheorem` | Coefficient names; truncated exact factorization with a name for each root |
| `PresentedNonmonicRootExistence` | Names for a finite coefficient list and an apart-from-zero coefficient of some positive power; a truncated named exact root |
| `OneRealParameterFundamentalTheorem` | Coefficients given by algebraic rational functions of one common native real, with nonzero denominators; truncated exact factorization |

These are defined in [Formulations/Presented.agda](Formulations/Presented.agda)
and [Formulations/SpecialCases.agda](Formulations/SpecialCases.agda).
The nonmonic statement does not require knowing that the last coefficient
is invertible. The one-real-parameter statement does not require a
rational name for that parameter and does not cover arbitrary dependence
on two real coordinates.

[Ruitenburg, *Constructing roots of polynomials over the complex
numbers*](https://ncatlab.org/nlab/files/Ruitenburg-Roots.pdf), Theorems
3.13 and 3.16, treats modulated Cauchy coefficients and the one-parameter
case respectively. [Peshev–Skordev, Theorem 3](https://store.fmi.uni-sofia.bg/fmi/logic/skordev/refinement.pdf)
constructs root representations from coefficient representations with a
second-Grzegorczyk-class operator bound.

A presentation-dependent algorithm can return different roots for two
names of the same polynomial. `PresentedRootAlgorithm` deliberately does
not demand invariance under replacement of the names. Neither rational
density nor the completed-multiset theorem supplies these input names for
arbitrary native coefficients. Consequently these targets are not merely
restatements of the unrestricted native exact FTA.

### Quasifinite, quasilocated, and located zero sets

These formulations ask how much can be said about the **set of actual
zeros**, even without supplying a point of that set.

**Status: all three general targets are statements only**, in
[Formulations/ZeroSets.agda](Formulations/ZeroSets.agda).

| Catalogue type | Requested information |
| --- | --- |
| `QuasifiniteZeroSetTheorem` | At each radius, finitely many centers covering every actual root, and double-negated existence of a nearby root for every center |
| `QuasilocatedZeroSetTheorem` | For each point, an actual native real greatest lower bound of its distances to all actual roots |
| `LocatedZeroSetTheorem` | That greatest lower bound plus truncated existence of a near-minimizing actual root whenever the requested bound exceeds it |

The GLB specification gives nonnegativity, a lower bound on every root
distance, and maximality among lower bounds. It includes no
near-minimizing root. The located version adds precisely that stronger
information. Similarly, the double negation attached to each quasifinite
center must not be replaced by a positive root witness.

The finite near-zero nets discussed above are already proved, but their centers
only have small residuals. That conclusion does not establish the nearby
exact-root conditions above. A completed spectrum is also a different
object from the subset of native complex numbers satisfying `p(z)=0`.

The distinction between greatest lower bounds and located infima, and the
quasifiniteness result, comes from
[Lubarsky–Richman, Section 1 and Corollary 4.6](https://arxiv.org/html/1510.00732).
Their results still need native proofs here, including construction of
the stated GLB in this real carrier.

### Projective FTA, including roots at infinity

**Formulation.** Fix homogeneous degree `n` while allowing the leading
affine coefficient to vanish. Construct a completed multiset of points
on the projective line and its correspondence with nonzero homogeneous
polynomials up to projective equivalence. A projective root `[u:v]`
contributes `vX − uY`; `[1:0]` accounts for a root at infinity.

**Status: statement and underlying definitions only.**
[Formulations/Projective.agda](Formulations/Projective.agda) defines
`ProjectiveFundamentalTheorem`. Its output must include the premetric
proofs, matching completion, coefficient equivalence, finite-product law,
and whole uniform continuity moduli in both directions. None is assumed
as a missing global construction.

Representatives have coefficient Euclidean moduli summing to one, so the
zero homogeneous polynomial is excluded. Projective equality is expressed
by vanishing two-by-two minors. The metric and normalization are a native
model whose comparison with the literature's functional norm remains
future work.

The source formulation is [Richman, Theorem 6](https://msp.org/pjm/2000/196-1/pjm-v196-n1-p10-p.pdf).
The already proved monic completed-multiset theorem handles a fixed affine
degree. It does not settle this projective formulation, where multiplicity
at infinity must be retained as affine degree changes.

### A point-free root space

**Formulation.** Describe roots by a formal cover of Gaussian balls,
rather than by a selected native point. The catalogue defines a generated
cover with metric refinements and deletion of uniformly root-free opens.
`PointFreeFundamentalTheorem` asks for nontriviality and compactness of
that presentation for each positive-degree monic polynomial.

**Status: proposed statement only.**
[Formulations/PointFree.agda](Formulations/PointFree.agda) also separates
`NativeRootPointSoundness`: a supplied native exact root should respect
the formal covers. Neither general theorem is proved. Even soundness in
that direction would not identify every formal point with a native
complex number or construct a native root from nontriviality.

Coquand and Spitters, [*Formal topology and constructive mathematics:
the Gelfand and Stone–Yosida representation theorems*](https://arxiv.org/pdf/0808.2705)
(2008 preprint), provide context for separating point-free constructions
from point extraction. They are not the source of this precise polynomial
cover specification; the latter is a proposed interface in this repository.

## Checking this guide

To check this document from the repository root:

```sh
agda-codex Cubical/Analysis/Complex/FundamentalTheorem/FormulationsGuide.lagda.md
```

It uses the existing library options and imports the actual proof modules.
It adds no assumptions and does not change the public FTA facade.
