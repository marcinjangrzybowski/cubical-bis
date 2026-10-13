# Constructive FTA statement catalogue

These Agda modules define theorem **types**, certificates, and the objects
needed to state them. They contain no assumed inhabitants of those theorem
types. A successful check means a statement is well formed, not that it has
been proved. This is the statement-first pass requested after the
[literature survey](../../FTA_SURVEY_2026-10-08.md).
The scope is the surveyed FTA formulations and their proposed interfaces,
not every lemma or subrecursive complexity bound in the cited papers.

| Survey formulation or proof obligation | Formal statement | Module |
| --- | --- | --- |
| Approximate roots; approximate factorization | `ApproximateRootExistence`; `ApproximateFundamentalTheorem` | [Existing Statement](../Statement.agda), re-exported by [Basic](Basic.agda) |
| Their interderivability | `ApproximateFormulationsInterderivable` | [Basic](Basic.agda) |
| Unrestricted native exact FTA (open) | `ExactRootExistence`; `ExactFundamentalTheorem` | [Basic](Basic.agda) |
| Positive separability certificate | `BezoutSeparability`; `StronglySeparable` | [Basic](Basic.agda), [generic certificate](PolynomialAlgebra.agda) |
| Exact separable roots and factorization into apart roots | `StronglySeparableRootExistence`; `StronglySeparableFundamentalTheorem` | [Basic](Basic.agda) |
| Preservation under deflation | `SeparableDeflation` | [Basic](Basic.agda) |
| Exact roots from explicit rational coefficient names | `PresentedExactRootExistence`; stronger `PresentedRootAlgorithm` | [Presented](Presented.agda) |
| Exact factorization with root names | `PresentedFundamentalTheorem` | [Presented](Presented.agda) |
| Presented nonmonic polynomial with a nonzero positive-power coefficient | `PresentedNonmonicRootExistence` | [SpecialCases](SpecialCases.agda) |
| Rational coefficient functions of one native real parameter | `OneRealParameterFundamentalTheorem` | [SpecialCases](SpecialCases.agda) |
| Stability retaining multiplicity | `QuantitativeRootMatching`; `QuantitativeFactorContinuity` | [Matching](Matching.agda) |
| Canonical completed unordered roots | `CompletedMultisetFundamentalTheorem` | [Completion](Completion.agda) |
| Exact small separated clusters | `SmallSeparatedFactorization` | [Clusters](Clusters.agda) |
| Weak FTA | `WeakFundamentalTheorem` | [Basic](Basic.agda) |
| Quasifinite zero sets | `QuasifiniteZeroSetTheorem` | [ZeroSets](ZeroSets.agda) |
| Native real quasidistance / GLB | `QuasilocatedZeroSetTheorem` | [ZeroSets](ZeroSets.agda) |
| Stronger located zero sets, for comparison | `LocatedZeroSetTheorem` | [ZeroSets](ZeroSets.agda) |
| Projective FTA, including infinity | `ProjectiveFundamentalTheorem` | [Projective](Projective.agda) |
| Proposed point-free direction | `PointFreeFundamentalTheorem`; `NativeRootPointSoundness` | [PointFree](PointFree.agda) |
| Local fixed-derivative Newton theorem | `LocalNewtonRootTheorem` | [LocalRoots](LocalRoots.agda) |
| Coercivity and finite near-zero nets | `BoundedApproximateRoots`; `NearZeroNetTheorem` | [LocalRoots](LocalRoots.agda) |
| Coherent exact-descent obligation and implications | `CoherentVanishingResidualConstruction`; implication types | [Relations](Relations.agda) |

The mathematical adaptations are explicit:

- Bézout is equality of zero-extended coefficients, not merely an identity
  at already known roots. A finite list may have trailing zero coefficients.
- Root matching uses a truncated bijection of finite index types at each
  tolerance. It neither forgets multiplicity nor chooses an exact ordering.
- Completion and projective metrics are part of the output specifications.
  No missing completion construction is accepted as a global assumption.
- Cluster diameter and separation use all sufficiently close finite
  factorizations; they do not presuppose a constructed spectrum object.
- Quasidistance uses a greatest lower bound. Near-minimizing actual roots
  belong only to the separate, stronger located-set statement.
- The projective model uses unit vectors for a phase-invariant coefficient
  l1 norm. It permits zero leading coefficients and excludes the zero
  homogeneous polynomial. Comparison with the paper's norm is future work.
- The point-free module defines a proposed formal ball cover and asks for
  nontriviality and compactness. It is not an attribution of this precise
  FTA to Coquand–Spitters. Native point soundness is separate; no equivalence
  of all formal points with the native real carrier is asserted.
- Supplied rational names and complete moduli are input data where stated.
  No radiuswise truncated family is promoted to an infinite chosen family.

The existing approximate FTA has inhabitants in
[Approximate.agda](../Approximate.agda). The other theorem types started as
proof targets. The derivative/Taylor algebra written
before the statement-first request remains separate in
[Polynomial/Differential](../../Polynomial/Differential.agda).

The complete statement-first pass checked on 2026-10-08: every new module,
the catalogue and public facades, `Cubical/Analysis/Everything.agda`, and
`Cubical/Analysis.agda` returned exit code 0. The snapshot audit found 139
current successful targets across the complex development and its earlier
dependencies, with no holes, unsolved metas, constraints, or warnings. The
import audit reached 628 Analysis modules / 1019 total modules, with no
missing modules, orphans, cycles, forbidden carrier/choice imports, or source
assumption flags. These counts record the statement-first checkpoint.

Proofs resume in the survey's order. The first five stages are complete;
stage 6 now has spectral estimates, exact special cases, and finite
near-zero nets. General separated clusters and the further formulations
remain open. The status below records actual inhabitants separately from
their statement types.

Proofs resumed after the complete statement checkpoint:

- [Separable/Certificate.agda](../Separable/Certificate.agda) proves that
  formal coefficient identities imply evaluation identities. A Bézout
  certificate consequently gives the derivative's inverse at any supplied
  root; root existence itself is supplied by the subsequent proof below.
- [Polynomial/Newton.agda](../../Polynomial/Newton.agda) now supplies
  `localNewtonRoot : LocalNewtonRootTheorem`: an actual native root, its ball
  bound, and uniqueness in that ball, from the stated quantitative premises.
  The proof constructs its Cauchy iteration through the existing contraction
  theorem.
- [BoundedRoots.agda](../BoundedRoots.agda) supplies
  `boundedApproximateRoots : BoundedApproximateRoots` by finite coercivity
  and one Archimedean bound. This bounds all small-residual points uniformly.
- [Separable/Root.agda](../Separable/Root.agda) supplies
  `stronglySeparableRootExistence : StronglySeparableRootExistence`.
  Its support modules derive every Newton premise from the formal Bézout
  certificate and a single sufficiently accurate approximate root.
- [Separable/Deflation.agda](../Separable/Deflation.agda) supplies
  `separableDeflation : SeparableDeflation`, preserving formal coefficient
  equality through division by an actual linear root factor.
- [Separable/Factorization.agda](../Separable/Factorization.agda) supplies
  `stronglySeparableFundamentalTheorem : StronglySeparableFundamentalTheorem`.
  Finite deflation produces an exact factor vector with positive metric
  apartness for distinct indices.

- [Matching/RootMatching.agda](../Matching/RootMatching.agda) supplies
  `quantitativeRootMatching : QuantitativeRootMatching`, including repeated
  roots and an explicit rational modulus.
- [Matching/FactorContinuity.agda](../Matching/FactorContinuity.agda) supplies
  `quantitativeFactorContinuity : QuantitativeFactorContinuity`.
- [Matching/ApproximateEquivalence.agda](../Matching/ApproximateEquivalence.agda)
  supplies `approximateFormulationsInterderivable : ApproximateFormulationsInterderivable`
  using the direct finite reductions in both directions.

- [Completion.agda](../Completion.agda) supplies
  `completedMultisetFundamentalTheorem : CompletedMultisetFundamentalTheorem`.
  It constructs the Gaussian-rational matching completion and its equivalence
  with all native monic coefficient vectors, including the finite-factor
  computation law and both whole local continuity moduli. See the
  [construction notes](../Completion/README.md) for the deterministic rational
  search and native coefficient induction.

- [NearZeroNet.agda](../NearZeroNet.agda) supplies
  `nearZeroNet : NearZeroNetTheorem`, with the original finite Gaussian net,
  center-residual, and universal-coverage requirements.
- [Clusters.agda](../Clusters.agda) supplies spectral-certificate stability,
  nonvacuity, actual-root separation, and finite block matching/continuity.
  It also proves `stronglySeparableClusterFactorization` and the empty and
  single-cluster cases. The general `SmallSeparatedFactorization` type has
  not been changed and remains uninhabited by this development. See the
  [remaining construction obligations](../Clusters/README.md).

The other FTA and zero-set targets remain unproved.
Unrestricted native exact FTA does not follow by dropping the
strong-separability premise.

The resumed certificate and Newton proof modules, their public facades, and
both Analysis entry points also checked with exit code 0. The resulting
snapshot audit had 144 successful targets; that import audit had
633 Analysis modules / 1024 total modules and no source/import flags.

The subsequent separable-FTA checkpoint also checks completely: all 21 new
or edited Agda files, followed by both Analysis entry points, returned exit
code 0. That checkpoint had 161 successful affected-module snapshots,
650 reachable Analysis modules / 1044 total modules, and no holes, metas,
constraints, warnings, or source/import flags. These counts include the
17 modules added for coercivity, Newton estimates, exact roots, and formal
finite factorization.

The matching checkpoint adds 16 modules and checks all 21 new or edited
Agda files, the complex facade, and both Analysis entry points with exit
code 0. Its audit has 177/177 current successful targets and reaches
666 Analysis modules / 1060 total modules. No holes, unsolved metas,
constraints, warnings, forbidden imports, or source-assumption flags remain.
The statement types were preserved; only the Basic module's status comment
was updated.

The completed-multiset checkpoint adds 21 modules. All 23 new or edited
Agda files, the complex facade, and both Analysis entry points checked with
exit code 0. Its audit has 198/198 current successful targets and reaches
687 Analysis modules / 1084 total modules, with no holes, metas, constraints,
warnings, or source/import flags. The original completion and correspondence
types were preserved; only their status comment was updated.

The first cluster/net checkpoint (2026-10-09) adds 15 modules. All 18 new or
edited Agda files, the complex facade, and both Analysis entry points checked
with exit code 0. All 213 affected-module snapshots are current and have no
holes, unsolved metas, constraints, or warnings; the source/import audit is
clean across 702 Analysis modules / 1099 total modules. Only the near-zero-net
status comment changed in the catalogue; its statement type is unchanged.

Implementation note: coefficient certificates and the formal-cover datatype
are generic definitions specialized to the native complex carrier. Large
quantitative packages use dependent pairs, and projective closeness receives
its degree explicitly. These choices avoid expensive expansion of completed
arithmetic while checking statement types; they do not alter the hypotheses.
