# Constructive formulations of the fundamental theorem of algebra

Survey and development plan, 2026-10-08. This document distinguishes literature
results, results checked in this repository, and proposed adaptations.
Implementation status updated 2026-10-09.

## Our starting point and foundations

The complex numbers here are pairs of the sequential-completion reals in
`Cubical.Analysis.Real`, not the other real carrier in `HITs/CauchyReals`.
Native limits accept sequences of already completed reals with a truncated
Cauchy modulus. Rational density is truncated separately at each radius;
it is not a function supplying rational approximants at all radii.

The checked [approximate FTA](FundamentalTheorem/Approximate.agda) gives, for
every monic degree-n polynomial p and positive rational ε,

```
∥ Σ (roots : Vec ℂ n), coefficients(p) ≈ε coefficients(∏(X - rootsᵢ)) ∥₁.
```

It also gives `∀ ε, ∥ Σ z, p(z) ≈ε 0 ∥₁` in positive degree. Synthetic
division proves the reduction from approximate roots to approximate
factorization. No general exact root or exact factorization follows merely
by interchanging `∀ ε` and truncation. In particular, the finite descent
proof does not supply an infinite compatible descent path.

## Formulations and their relationship

| Formulation | Output | Relation to the present result | Implementation assessment |
| --- | --- | --- | --- |
| Approximate roots / approximate factorization | A truncated finite witness at each tolerance | Both direct reductions are now formalized. The reverse reduction uses uniform coefficient/root bounds and one approximate factorization. | Established base and reusable equivalence proved. |
| Finite near-zero nets | A finite Gaussian net covering all sufficiently small-residual points, with small residual at every center | Obtained from Gaussian factor density, root matching, and synthetic division retaining a supplied small-residual point. It does not extract exact roots. | Original `NearZeroNetTheorem` now proved. |
| Exact FTA for strongly separable monic polynomials | Truncated actual roots and an exact finite factorization | Requires a positive separability certificate; native deterministic Newton iteration supplies convergence. It is not unrestricted exact FTA. | First exact milestone now proved, including pairwise apart roots. |
| Completed unordered root multisets | A canonical completed metric object, with multiplicities | The completion, coefficient equivalence, finite-factor law, and both whole local moduli are constructed. The output retains multiplicity without selecting an ordered vector of native roots. | General completed-multiset FTA now proved. |
| Exact roots from coefficient presentations | Root Cauchy names computed from supplied coefficient Cauchy names | Representation-sensitive. Native density does not automatically supply these presentations. | Valuable separate theorem if presentations are explicit. |
| Weak FTA | Double-negated exact root existence | Distinct from truncated exact existence and not an immediate consequence of small residuals. | Later, using separability and finite algebra. |
| Small separated factors | Exact factors representing separated clusters of small diameter | Retains clusters where individual roots cannot yet be extracted; factors can have degree greater than one. | Spectral certificates, finite block matching/continuity, and the strongly separable case are proved; general factor construction remains open. |
| Projective FTA | A completed root multiset on the projective line | Also accommodates uncertain degree and roots at infinity. An invertible leading coefficient alone is already handled by monic normalization. | Substantial later extension. |
| Point-free spectrum / localic roots | A locale describing roots rather than chosen points | A different output interface; extracting points needs separate justification. | Defer until a concrete client needs it. |

### Strong separability

Use a positive algebraic certificate, for example polynomials s and t with
`s*p + t*p′ = 1`. Do not replace it by the negative assertion that p has no
multiple roots. Lubarsky and Richman prove exact FTA for strongly separable
polynomials (Theorem 4.4), then weak FTA (Theorem 4.5). Their Theorem 3.2
describes exact factorization into arbitrarily small separated clusters;
Corollary 4.6 describes quasifinite zero sets. These results distinguish
information about a zero set from a supplied point in it.
Source: [Zero sets of univariate polynomials](https://arxiv.org/html/1510.00732).

Our implementation uses the existing native
contraction theorem. A bound on approximate roots and the Bézout identity
give a derivative lower bound at a sufficiently accurate approximate root.
The fixed-derivative Newton map is then a contraction on an explicit ball.
Choose that one approximate root inside a truncation elimination, construct
its entire iteration deterministically, and finish in truncated exact
existence. Finite deflation can repeat this without countable choice.

If `p = (X-r)q`, then `p′ = q + (X-r)q′`, so the certificate descends:

```
1 = [s*(X-r) + t]*q + [t*(X-r)]*q′.
```

Formal derivatives and this identity are useful before any general theory
of complex differentiability or integration.

### Completed root multisets and quantitative matching

Richman's development treats the root multiset as a completed metric object
and proves continuous dependence on coefficients; its projective version
is Theorem 6. This avoids requiring an ordering or extracting every root as
a native complex point. Source: [The fundamental theorem of algebra: A
constructive development without choice](https://msp.org/pjm/2000/196-1/pjm-v196-n1-p10-p.pdf).

The base consists of fixed-cardinality Gaussian-rational configurations,
followed by an appropriate separated completion. The literature's matching
distance is `minσ maxᵢ |rᵢ-sσ(i)|`; the native catalogue uses coordinate
closeness, related to the l1 norm and Euclidean modulus by explicit estimates.
It need not construct a real-valued minimum to state a matching radius.
The finite matching laws, separated reflection, and native sequential
completion are now constructed. Equality in the finite reflection means
matching at every radius. Over arbitrary completed coefficients, zero
matching distance must not silently be replaced by a
chosen exact permutation: finite undecidable alternatives can obstruct that
step. Nor does closeness of underlying sets preserve multiplicities.

Ruitenburg's Lemma 3.10 gives an algebraic root-matching argument; Theorems
3.13–3.16 cover exact roots for Cauchy reals, separated factors, simple-root
behavior, and a one-real-parameter coefficient setting. These provide a
promising alternative to developing contour integration just to prove
matching. Source: [Constructing roots of polynomials over the complex
numbers](https://ncatlab.org/nlab/files/Ruitenburg-Roots.pdf).

Our adaptation now supplies explicit quantitative moduli on bounded
coefficient and root sets. They provide the full functions needed when
constructing the completion-centered lifting data. Statements of the form
`∀ ε, ∥ Σ δ, ... ∥₁` are insufficient to manufacture such a package.
Approximate FTA and these stability estimates now construct the completed
root object and its equivalence with native coefficient vectors. The proof
uses deterministic search for rational coefficient vectors, followed by
induction over the native completion constructors; it does not choose a
rational presentation for an arbitrary native coefficient.

### Presented coefficients and exact roots

Peshev and Skordev compute root approximations from coefficient
approximation functions, refining the complexity of that computation. The
presentation is part of the input. Their near-zero nets control all points
with sufficiently small residual, which is stronger than merely finding
one small-residual point. Source: [A Subrecursive Refinement of the
Fundamental Theorem of Algebra](https://store.fmi.uni-sofia.bg/fmi/logic/skordev/refinement.pdf).

This suggests a separate exact-root interface for explicit rational Cauchy
presentations. It does not justify flattening every native sequential HIT
real to one rational sequence: a native limit may already have completed
reals as its terms. An algorithm depending on presentations also need not
descend to a single-valued root selector on coefficient values. Conversely,
countermodels involving other real carriers do not establish impossibility
for this carrier. We leave unrestricted native exact FTA open.

### Kneser descent and point-free approaches

Geuvers, Wiedijk, and Zwanenburg give a constructive Kneser proof. Their
Lemma 4 controls both a descent displacement and the new residual. Our
current finite adaptation proves the residual estimate needed for the
approximate theorem. Exact convergence additionally needs summable
displacements and an actual compatible iteration; infinitely iterating a
truncated one-step relation would not supply it.
Source: [A Constructive Proof of the Fundamental Theorem of Algebra without
using the Rationals](https://www.cs.ru.nl/F.Wiedijk/pubs/kneser.pdf).

Coquand and Spitters develop choice-free formal-topological representation
theorems and explain the distinction between point-free objects and chosen
points. This is relevant foundational context, not a ready-made proof of
our exact FTA target. Source: [Formal topology and constructive mathematics:
Gelfand and Stone–Yosida representation theorems](https://arxiv.org/pdf/0808.2705).

## Preferred development order and acceptance criteria

At the user's subsequent request, first formalize the statements without
proving them. The [statement catalogue](FundamentalTheorem/Formulations/README.md)
maps every formulation below to an Agda type and explains native adaptations.
Unproved theorem types have no assumed inhabitants, postulates, or holes.
Resume the following proof order only after checking the complete catalogue.

1. **Polynomial differential algebra.** Add formal derivatives, exact
   divided differences and a quadratic remainder, with generic commutative
   ring proofs and small native facades. Connect ordinary lists and monic
   vectors. Prove the algebra needed to propagate Bézout certificates.
2. **Quantitative local roots.** Prove bounded derivative/remainder estimates
   and a fixed-derivative Newton certificate using native complex balls and
   deterministic contraction. The output must contain an actual native
   limit and a proof that its residual is zero.
3. **Strongly separable exact FTA.** Bound approximate roots, derive the local
   certificate from one sufficiently accurate approximate root and Bézout
   data, and deflate finitely. Export truncated exact factorization under
   the stated positive algebraic certificate, not under an extra supplied
   root or an assumed convergence/choice principle.
4. **Quantitative root matching.** Prove bounded-coefficient stability of
   finite linear factorizations, with multiplicities and an explicit
   tolerance rule. Reuse the bounds and finite estimates for the reverse
   approximate-FTA implication.
5. **Completed multisets.** Build the separated metric completion and extend
   the coefficient/root correspondence using existing choice-free lifting
   machinery. Audit every passage from finite witnesses to a limit.
6. **Further formulations as clients.** Separated clusters, weak FTA,
   presentation-sensitive exact roots, then projective roots. Reassess
   unrestricted native exact FTA from the actual interfaces obtained.

Complex integration and winding remain useful future developments; they
are not prerequisites for the first five stages. Analytic derivatives can
reuse the polynomial remainder API when needed.

Every Agda addition must check with `agda-codex`, without holes, postulates,
new options, or choice assumptions. Check the Analysis aggregates, audit
imports and source assumptions, and update this plan and the progress
documents to distinguish finished stages from open obligations.

## Implementation status

- Existing base: arbitrary-degree approximate roots and approximate
  factorization are checked.
- Before the statement-first request, formal Horner derivatives, the exact
  quadratic Taylor identity, the ordinary/monic bridge, and derivatives of
  linear-factor multiplication were checked in `Polynomial/Differential`.
  This is part of stage 1; it does not prove separable exact FTA.
- The statement catalogue covers stages 1–6 and comparison formulations,
  including explicitly proposed projective and point-free native models.
  All its modules and both Analysis entry points checked with exit code 0
  before resuming proofs. Its types are separate from proof modules.
- After that checkpoint, the Bézout evaluation/derivative-inverse bridge and
  `localNewtonRoot : LocalNewtonRootTheorem` were checked. The latter gives an
  actual unique root in the supplied ball using deterministic native
  contraction, under its explicit inverse, remainder, and correction bounds.
- The subsequent proof pass supplies `boundedApproximateRoots`, uniform two-point
  divided-difference estimates, and derivative-inverse bounds from Bézout.
  It derives the Newton premises with finite tolerance choices and one
  approximate center, proving
  [`stronglySeparableRootExistence`](FundamentalTheorem/Separable/Root.agda).
- [`separableDeflation`](FundamentalTheorem/Separable/Deflation.agda)
  propagates the formal coefficient certificate. The proof interprets finite
  lists in the existing generic polynomial ring and reflects equality back
  to zero-extended coefficients. It does not replace the certificate by a
  pointwise identity or assume evaluation-extensionality.
- [`stronglySeparableFundamentalTheorem`](FundamentalTheorem/Separable/Factorization.agda)
  now proves exact factorization into pairwise apart native roots by finite
  deflation. This completes stages 1–3 with the catalogue's original types.
  No postulates, choice assumptions, supplied convergence data, or comparison
  to another real carrier are used.
- Stage 4 now supplies
  [`quantitativeRootMatching`](FundamentalTheorem/Matching/RootMatching.agda)
  and [`quantitativeFactorContinuity`](FundamentalTheorem/Matching/FactorContinuity.agda),
  with the catalogue's original types. Their moduli are actual rational
  functions of degree, a bound, and the requested accuracy. The matching
  is a truncated finite bijection and retains multiplicity, including
  coincident roots; it does not require separability.
- [`approximateFormulationsInterderivable`](FundamentalTheorem/Matching/ApproximateEquivalence.agda)
  gives both direct reductions. The reverse reduction uses a coefficient
  bound, a uniform root bound, and one sufficiently close finite
  factorization to obtain a small residual.
- Stage 5 supplies
  [`completedMultisetFundamentalTheorem`](FundamentalTheorem/Completion.agda)
  with the catalogue's original `CompletedMultisetFundamentalTheorem` type.
  Both maps and inverse laws, the Gaussian finite-factor computation law,
  and the whole local moduli are constructed. Further surveyed formulations
  and unrestricted native exact FTA remain open.
- The first stage-6 pass (2026-10-09) proves
  [`nearZeroNet : NearZeroNetTheorem`](FundamentalTheorem/NearZeroNet.agda)
  with its original Gaussian-center, small-residual, and universal-coverage
  fields. It also proves robust spectral certificates, their openness and
  nonvacuity, actual-root separation, restriction of finite matchings to
  separated blocks, and whole coefficient moduli for those blocks.
  [`stronglySeparableClusterFactorization`](FundamentalTheorem/Clusters/Linear.agda)
  satisfies the cluster specification under the existing separability
  hypothesis. General `SmallSeparatedFactorization` remains open.

The separable-FTA checkpoint passed `agda-codex` on every new or edited Agda
file and both Analysis entry points, all with exit code 0. The current
snapshot and import audits are recorded in [PROGRESS.md](../PROGRESS.md).

The matching checkpoint also passed all 21 new/edited-file checks and both
Analysis entry points with exit code 0. The full audit has 177 current
successful targets and no source/import flags; see [PROGRESS.md](../PROGRESS.md).
That checkpoint completed stages 1–4. Stage 5 now also preserves the
catalogue's original theorem type; see the completion construction below.

The completed-multiset checkpoint passed all 23 new or edited Agda-file
checks, the public complex facade, and both Analysis entry points with exit
code 0. All 198 affected-module snapshots match the current sources with no
holes, metas, constraints, or warnings. The import/source audit found no
forbidden assumptions, missing modules, or cycles; full counts are recorded
in [PROGRESS.md](../PROGRESS.md).

## Quantitative matching and completed multisets

The root-by-root induction follows the pattern of
[Ruitenburg, 3.10](https://ncatlab.org/nlab/files/Ruitenburg-Roots.pdf).
Our synthetic-division formulas give uniform coefficient estimates for the
quotient directly. This replaces the source's quotient estimates away from
selected roots. The native l1 norm controls evaluation and coefficient
errors; the multiplicative Euclidean modulus supplies the small-product
argument. All constants are deliberately generous, with no claim of an
optimal perturbation rate.

The finite proof first converts coefficient bounds into root bounds. It
then finds a nearby factor using located comparisons with a half-radius
margin, moves that factor to the front by an explicit permutation, and
controls both deflated polynomials by the synthetic-division modulus.
Degree induction finishes the matching. Generic ring proofs establish exact
coefficient invariance under permutations and exact removal of a supplied
linear factor. No root sequence, radius-indexed choice, or comparison with
another real carrier is introduced.

Stage 5 now inhabits the original `RootMultisetCompletion` and
`RootMultisetCorrespondence` specifications. The
[completion implementation](FundamentalTheorem/Completion/README.md) follows
this choice-free route:

1. Prove finite matching laws, quotient by matching at every radius, and
   apply the native sequential completion. Prove the insertion isometry,
   finite-configuration density, regular completeness, and sequential
   completeness.
2. Combine approximate FTA with finite rational density and quantitative
   factor continuity to approximate coefficients by Gaussian linear factors.
3. Use jointly approximable root/coefficient pairs to define the factor
   extension. One nearby finite configuration bounds a neighborhood and
   supplies a whole local modulus. Quantitative root matching proves the
   reverse modulus and uniqueness of the completed root object.
4. For rational coefficient vectors, enumerate finite Gaussian configurations
   and use a decidable coefficient-error test. A unique least successful
   index is obtained by finite search below an existing witness. This is a
   proved deterministic construction, not a choice assumption. Dyadic
   accuracies supply an actual coefficient Cauchy modulus.
5. Reflect coefficient Cauchy witnesses to root-multiset witnesses. Induction
   over each native real completion constructor extends root existence to
   every native coefficient vector. Unique graph fibers give both inverse
   laws and the final equivalence.

The last step is specific to Analysis's native sequential carrier. A limit
may contain already completed coordinates, so a global rational name is
neither supplied nor inferred. The rational search establishes existence,
with no efficiency or subrecursive complexity claim.

Stages 1–5 are complete and stage 6 is in progress. Continue with the general
separated-cluster construction, then weak FTA, presentation-sensitive exact
roots, and projective roots. The completed-multiset theorem does not itself
extract an ordered vector of native roots or settle unrestricted native
exact FTA.

## Stage 6: spectral geometry and finite nets

The [cluster construction notes](FundamentalTheorem/Clusters/README.md)
record the checked finite estimates and exact special cases. The catalogue's
diameter and separation predicates quantify over all sufficiently accurate
factorizations. A whole local matching modulus now turns one accurate
configuration with geometric slack into such a universal certificate.
Finite common margins suffice; radius-indexed selection is unnecessary.

The near-zero-net proof uses one sufficiently accurate Gaussian
factorization. For any point with residual below a fixed tolerance, synthetic
division and approximate FTA for its quotient give an approximate
factorization containing that point. Matching it to the Gaussian
factorization supplies a nearby center. Coercive root bounds and evaluation
perturbation control every center's residual. The proof constructs one net
per requested accuracy and makes no claim of a chosen compatible sequence
or a complexity bound.

The general cluster theorem still needs a persistent finite partition near
a Gaussian configuration, construction of the completed block factors, and
an exact coefficient reconstruction identity. Restriction of finite
matchings now preserves the block bijections, and `blockFactorModulus`
controls their coefficients. These are inputs to the missing local lifting
step, not a proof that density alone supplies the required factor limits.

The first cluster/net checkpoint passed `agda-codex` on all 18 new or edited
Agda files, the public complex facade, and both Analysis entry points with
exit code 0. All 213 affected-module snapshots are current and complete;
the import/source audit found no forbidden assumptions, missing modules,
or cycles. See [PROGRESS.md](../PROGRESS.md) for the full validation record.
