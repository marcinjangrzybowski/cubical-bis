# Separated clusters: finite estimates and special cases

This is the first proof pass for stage 6 of the
[FTA survey](../../FTA_SURVEY_2026-10-08.md), dated 2026-10-09. The public
[Clusters facade](../Clusters.agda) exports the results below. The original
[`SmallSeparatedFactorization`](../Formulations/Clusters.agda) statement for
arbitrary native polynomials remains open.

The catalogue describes diameter and separation by testing **every**
sufficiently accurate finite factorization. These tests now have a proved
connection to finite configurations and actual roots; they are not assumed
properties of an unspecified spectrum.

| Layer | Checked results |
| --- | --- |
| Metric estimates | [Distance](../../Modulus/Distance.agda) proves Euclidean distance symmetry, triangle, and endpoint perturbation bounds. Coordinate errors of one quarter of a radius change the distance by less than that radius. Its ring calculations are isolated in [DistanceAlgebra](../../Modulus/DistanceAlgebra.agda). |
| Finite margins | [Finite](Finite.agda) combines finitely many radius witnesses. [Geometry](Geometry.agda) obtains common diameter/separation margins and transports them along bijective matching. Repeated roots are allowed. |
| Local matching | [Matching](Matching.agda) constructs a whole modulus matching any two sufficiently accurate factorizations of one polynomial, from one coefficient bound. |
| Spectral certificates | [Certificates](Certificates.agda) turns a sufficiently accurate finite factorization with geometric slack into the catalogue's universal certificate. On exactly split polynomials, finite diameter and spectral diameter imply each other; finite positive gaps and spectral separation also imply each other. |
| Stability | [Stability](Stability.agda) proves openness under coefficient perturbation, symmetry of separation, and nonvacuity from approximate FTA. A positive-degree spectrum cannot be separated from itself. |
| Actual roots | [RootContainment](RootContainment.agda) retains a supplied small-residual point as the first factor of an approximate factorization. Separated positive-degree spectra have a uniform positive gap between actual roots and cannot have a common root. |
| Finite block control | [BlockPermutation](BlockPermutation.agda) restricts a bijection which cannot cross blocks. [BlockMatching](BlockMatching.agda) applies it when opposite blocks of the two configurations have positive cross-gaps. [BlockContinuity](BlockContinuity.agda) gives a whole rational modulus for both block coefficient vectors. |
| Exact special cases | [Assembly](Assembly.agda) constructs empty and single-cluster factorizations. [Linear](Linear.agda) constructs separated linear clusters from pairwise apart exact roots, hence proves `stronglySeparableClusterFactorization`. The product law is a formal coefficient identity. |

The related [NearZeroNet](../NearZeroNet.agda) module now inhabits the
original `NearZeroNetTheorem`. For any positive-degree native monic polynomial
and requested accuracy, it supplies a truncated finite Gaussian net and a
positive residual tolerance. Every center has small residual, and every
point below the supplied residual tolerance lies near some center. The proof
uses as many centers as the degree, with repetitions permitted.

To prove coverage, retain the given small-residual point in an approximate
factorization by synthetic division and approximate FTA for its quotient.
Match that factorization to one sufficiently accurate Gaussian factorization
of the original polynomial. The image of its first index gives a nearby
center. Coercive bounds and coefficient perturbation estimates prove the
residual bound at every center. No root is extracted from a net.

All truncation elimination stays within propositions. Witnesses for one
finite output are combined under its outer truncation. The estimates
construct their whole modulus functions. Neither a
rational presentation of arbitrary native coefficients nor a compatible
sequence of nets, roots, matchings, or partitions is assumed.

## Remaining route to general clusters

1. Construct a finite partition of a sufficiently accurate Gaussian
   configuration, with positive gaps and diameter slack. Prove that the
   partition persists nearby with fixed block cardinalities.
2. Extend the block-factor maps to that neighborhood of the native matching
   completion. The finite restriction and coefficient modulus above are
   available; existence of the completed block factors is still to prove.
   Any passage to a limit must construct a whole Cauchy witness or use the
   existing choice-free lifting machinery.
3. Prove the exact coefficient reconstruction identity for those limits and
   assemble the positive-degree blocks with the original degree, diameter,
   and pairwise separation fields.

The strongly separable case uses actual apart roots and does not discharge
these obligations for arbitrary polynomials. Repeated roots are allowed in
the finite estimates and single-cluster case; the general factor-construction
step is still missing. Weak FTA, presentation-sensitive exact roots, and
projective roots remain later stages of the plan.

Block labels are part of the finite estimates: a gap inside each
configuration alone would still allow the two blocks to be interchanged.
The restriction theorem requires cross-gaps from the first block of either
configuration to the opposite block of the other. Establishing this
consistent assignment is part of the remaining persistent-partition proof.

Validation (2026-10-09): all 18 new or edited Agda files, the public complex
facade, and both Analysis entry points checked with `agda-codex`, returning
exit code 0. The affected-module audit has 213/213 current successful
snapshots, with no holes, unsolved metas, constraints, or warnings. The
source/import audit is clean; full counts are recorded in
[PROGRESS.md](../../../PROGRESS.md).
