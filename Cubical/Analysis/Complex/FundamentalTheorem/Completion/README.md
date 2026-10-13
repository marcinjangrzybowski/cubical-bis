# Completed root multisets

The public [Completion facade](../Completion.agda) inhabits the original
[`CompletedMultisetFundamentalTheorem`](../Formulations/Completion.agda)
specification. For every degree, it constructs a complete matching space
and an equivalence with native monic coefficient vectors. Both whole local
continuity moduli and the computation law on Gaussian linear factors are
included. No separability hypothesis is needed.

The public maps are `completedFactors` and `completedRoots`, with
`factors-roots` and `roots-factors` as inverse laws. The result retains
multiplicities. It does not select an ordering or extract a vector of
individual native complex roots.

| Layer | Main files and results |
| --- | --- |
| Finite matching | [FiniteMatching](FiniteMatching.agda) proves symmetry, triangle, monotonicity, and finite roundedness. [SeparatedMatching](SeparatedMatching.agda) quotients by matching at every radius and proves a separated premetric. |
| Native completion | [Construction](Construction.agda) supplies insertion isometry, density, regular completeness, and sequential completeness. [Base](Base.agda) specializes it to Gaussian rationals. |
| Coefficient density | [Gaussian](Gaussian.agda) proves finite rational approximation. [Density](Density.agda) combines it with approximate FTA and factor continuity. |
| Local estimates | [Bounds](Bounds.agda) transfers bounds through matching. [LocalFactor](LocalFactor.agda) constructs a whole factor modulus near every completed configuration. |
| Graph and extension | [Graph](Graph.agda) defines joint approximation and coefficient uniqueness. [Coefficients](Coefficients.agda) provides native coefficient limits. [Extension](Extension.agda) constructs the factor map by sequential induction. |
| Reverse estimates | [GraphContinuity](GraphContinuity.agda) proves both whole local moduli and root uniqueness. [FactorMap](FactorMap.agda) packages the dense embedding. [SequentialClosure](SequentialClosure.agda) reflects Cauchy witnesses and proves closure of its image under native limits. |
| Rational existence | [Enumeration](Enumeration.agda) enumerates Gaussian configurations. [FiniteSearch](FiniteSearch.agda) proves least-witness selection for inhabited decidable natural predicates. [RationalFactors](RationalFactors.agda) gives the decidable test and selected approximation; [RationalRoots](RationalRoots.agda) constructs its dyadic limit. |
| General existence | [CoefficientInduction](CoefficientInduction.agda) extends proposition-valued, sequentially closed properties from Gaussian vectors to native coefficients. [Correspondence](Correspondence.agda) constructs the root map, inverse laws, and catalogue correspondence. |

The choice-free steps are explicit. An approximation of a native point
remains truncated at each radius. On rational coefficient input, the error
test is decidable; a successful index bounds a finite search for the unique
least successful index. Its uniqueness permits truncation elimination.
This is proved inside `FiniteSearch`, without a selection axiom.

The passage to arbitrary native coefficients uses their HIT eliminators.
Induction supplies unique completed root objects for the terms of an
already supplied native sequence. Quantitative matching computes the whole
root Cauchy witness from the coefficient witness and one finite bound.
It never flattens a native real into a rational sequence, or chooses roots
independently from a family of truncated approximation statements.

The estimates are deliberately loose, and the enumeration proof carries
no efficiency claim. The finite quotient relation is opaque with an explicit
insertion equivalence; this keeps the large quotient recursor out of metric
law elaboration. The original catalogue statement has not been weakened.

The next survey stage is now in progress: the
[cluster layer](../Clusters/README.md) supplies finite spectral estimates,
block matching/continuity, exact special cases, and the finite near-zero-net
theorem. General separated factors, weak FTA, presentation-sensitive exact
roots, and projective roots remain open. Unrestricted native exact FTA
remains separate.

Validation (2026-10-08): all 21 new modules, the two edited Agda modules,
the public complex facade, and both Analysis entry points checked with
`agda-codex`, returning exit code 0. All 198 affected-module snapshots match
the current sources without holes, metas, constraints, or warnings. The
import/source audit found no forbidden carrier or choice imports, missing
modules, cycles, or added assumptions. The full checkpoint is recorded in
[PROGRESS.md](../../../PROGRESS.md).
