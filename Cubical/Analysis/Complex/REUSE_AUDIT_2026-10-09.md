# Complex: library reuse audit — 2026-10-09

The audit covers all **197 Agda modules** under `Cubical/Analysis/Complex`
and the [public facade](../Complex.agda). It inventories declarations and
imports throughout the directory, searches the rest of Cubical for matching
constructions, and compares the implementations of plausible replacements.
This is a source audit, not a mechanical proof that no further duplication
exists.

The criterion for reuse is a compatible carrier, hypotheses, computational
interface, and dependency boundary. In particular, Analysis uses native
sequential reals and follows the [choice-free policy](../AGENTS.md). A theorem
about the other real implementation is not automatically a theorem about
these reals.

## Replacements

Public declaration types are preserved. Small adapters remain where they
connect an existing library construction to the local representation.

| Local module and declarations | Existing library implementation now used |
| --- | --- |
| [Algebra/Identities](Algebra/Identities.agda), `shuffle`; [Modulus/DistanceAlgebra](Modulus/DistanceAlgebra.agda), `middle-first` | [Ring.Properties](../../Algebra/Ring/Properties.agda): `+ShufflePairs`, `+Assoc-comm1` |
| [Algebra/Conjugation](Algebra/Conjugation.agda), involution, preservation of addition and one | [Ring.Properties](../../Algebra/Ring/Properties.agda): `-Idempotent`, `-Dist`, `0Selfinverse` |
| [Inverse](Inverse.agda), `inverseℂ-unique` | [CommRing.Properties](../../Algebra/CommRing/Properties.agda): `Units.inverseUniqueness` |
| [Modulus/Base](Modulus/Base.agda), uniqueness, zero, one, negation, conjugation, real embedding, multiplication | Native [SquareRoot/Laws](../Real/Functions/SquareRoot/Laws.agda): `nonnegativeSqrtℝ-unique`, `-zero`, `-one`, `-squareOf`, `-mul`, with transport of the nonnegativity certificate |
| [Polynomial/MonicAlgebra](Polynomial/MonicAlgebra.agda), `productOfLinearFactors` | [Ring.BigOps](../../Algebra/Ring/BigOps.agda): `Product.∏`, indexed by vector lookup |
| [Polynomial/BinomialAlgebra](Polynomial/BinomialAlgebra.agda), `monomial` | [Vec](../../Data/Vec.agda): `replicate` |
| [Descent/FiniteIndices](FundamentalTheorem/Descent/FiniteIndices.agda), `twiceIndexBound` | [Nat](../../Data/Nat.agda): `doubleℕ` |
| [Descent/PrefixMaximum](FundamentalTheorem/Descent/PrefixMaximum.agda), prefix inclusion, restriction, index and inverse laws | [FinData](../../Data/FinData.agda): `fromℕ'`, `toFromId'`, `inj-toℕ` |
| [Matching/Finite](FundamentalTheorem/Matching/Finite.agda), `liftPermutation`, injectivity | [FinData](../../Data/FinData.agda): `finSucMaybeIso`; [Maybe](../../Data/Maybe.agda): `congMaybeEquiv`; [Isomorphism](../../Foundations/Isomorphism.agda): `isoFunInjective` |
| [Matching/FiniteOrder](FundamentalTheorem/Matching/FiniteOrder.agda), `finiteRealProduct` | [Ring.BigOps](../../Algebra/Ring/BigOps.agda): `Product.∏` |
| [Completion/Coefficients](FundamentalTheorem/Completion/Coefficients.agda), `coefficient-ext` | [Vec](../../Data/Vec.agda): `FinVecIsoVec`; [Isomorphism](../../Foundations/Isomorphism.agda): `isoInvInjective` |
| [Completion/Enumeration](FundamentalTheorem/Completion/Enumeration.agda), rational enumeration and surjectivity | [Rationals.NatIso](../../Data/Rationals/NatIso.agda): `ℚIsoℕ`, replacing the local signed-integer and quotient construction |
| [Completion/FiniteSearch](FundamentalTheorem/Completion/FiniteSearch.agda), `searchBelowWitness` | [Nat.Order.Recursive](../../Data/Nat/Order/Recursive.agda): `Minimal.→Least`; a private order adapter preserves the usual `Nat.Order` certificate |
| [Completion/RationalFactors](FundamentalTheorem/Completion/RationalFactors.agda), finite coefficient decidability | [FinData](../../Data/FinData.agda): `∀Dec`, with the existing Gaussian lookup lemma |
| [Clusters/BlockPermutation](FundamentalTheorem/Clusters/BlockPermutation.agda), restriction to the right block | [Sum.Properties](../../Data/Sum/Properties.agda): `Iso⊎→Iso`, using the constructed left-block isomorphism |

The rational enumeration order changes to the library's canonical enumeration.
Consumers require surjectivity and deterministic least search, not the old
coding order. Thus particular rational approximants chosen during search may
change. The new enumeration uses the existing constructive rational/natural
isomorphism; no computational speedup is claimed.

Other replacements remove independent recursion or specialize existing laws.
Their dependent proofs and downstream public imports are checked, rather than
assuming the old and new implementations have all the same definitional
equalities.

## Coverage and decisions

Counts below include every module in the directory exactly once; the facade
is checked separately.

| Area | Modules | Comparison and disposition |
| --- | ---: | --- |
| Top-level modules; Algebra, Inverse, Metric, Modulus, Norm, Sequence subdirectories | 32 | Generic ring/group laws, units, product premetrics, sequence limits, real square-root laws. Reuse the direct algebraic matches and square-root laws above; retain the native complex operations and estimates. |
| Polar, Roots, SquareRoot | 19 | Native trig, restricted inverses, real powers/roots, generic exponentiation; compare the other complex development only as a mathematical reference. Retain native carrier proofs and the direct quadratic square-root route. |
| Polynomial, including all nested subdirectories | 37 | Generic list polynomials, their universal property, ring sums/products, vectors and finite indices. Reuse products and replication; retain fixed-degree Horner data, quantitative bounds, translation, differential estimates, Newton and quadratic constructions. |
| FundamentalTheorem top level and Approximate | 12 | Existing algebra, metric and finite-accuracy interfaces. These modules assemble the native theorem and quantitative descent; no drop-in general FTA found elsewhere. |
| FundamentalTheorem/Descent | 32 | Finite orders, sums, powers, near-maximizers, geometric decay. Replace duplicate doubling and bounded index conversions; retain the quantitative selected-term argument. |
| FundamentalTheorem/Matching | 12 | Finite permutations, products, powers, finite search, finite multisets. Reuse the matching library primitives above; retain multiplicity-preserving root matching and quantitative moduli. |
| FundamentalTheorem/Completion | 20 | Rational enumeration, least witnesses, vector extensionality, decidability, sequential completion and lifting. Replace four generic helpers; retain the native target extension described below. |
| FundamentalTheorem/Separable | 9 | Generic polynomial algebra and units versus Bézout certificates, deflation and native Newton estimates. Existing generic formal polynomial bridge already reused; native quantitative proof remains necessary. |
| FundamentalTheorem/Clusters | 11 | Sum isomorphisms, finite block permutations and spectral margins. Replace the independent right-block inverse construction; retain block-specific estimates and spectral certificates. |
| FundamentalTheorem/Formulations | 13 | Existing topology, algebra, finite multisets and completion interfaces. Retain the commented statement catalogue and its distinctions between formulations. A statement type is not an established theorem. |
| **Total** | **197** | |

### Native complex numbers, metric and analytic laws

[Algebra/Cartesian](Algebra/Cartesian.agda) is already parameterized by a
commutative ring, and is instantiated for both native reals and Gaussian
rationals. The library's direct product ring multiplies coordinates separately;
it cannot replace `(a,b)*(c,d) = (ac-bd,ad+bc)`.

[Metric](Metric.agda) already uses the generic product premetric and its
coordinate maps. [Sequence](Sequence.agda) already builds on native real
sequence witnesses and completion. The geometric convergence estimates reuse
the native real sequence machinery. Reimplementing these generic layers would
be duplication; the coordinate adapters themselves are necessary.

The coordinate product premetric, the l1 `normℂ`, and Euclidean `modulusℂ`
have different roles. Only the last is exactly multiplicative. Their explicit
comparison constants are part of the quantitative development, so they are
not collapsed into one notion of distance.

The direct [SquareRoot](SquareRoot.agda) construction supports the quadratic
layer without polar form or trigonometry. Although the later arbitrary-degree
root theorem subsumes square-root existence mathematically, routing quadratics
through that theorem would lose this useful dependency boundary. The new
modulus refactor does reuse the already established native nonnegative real
square-root laws.

The real and complex carriers under `HITs/CauchyReals` are not imported. This
audit supplies no equivalence between those carriers and Analysis's sequential
completion.

### Polynomial representations

The local ordinary polynomial is a Horner list, including trailing zeros.
`MonicPolynomial n` stores exactly `n` coefficients in a vector, with an
implicit leading coefficient of one. Degree-indexed coefficient bounds,
matching and completion use that representation directly.

The library's [generic polynomial](../../Algebra/CommRing/Polynomials/UnivariatePolyList.agda)
is a HIT that identifies trailing zeros. The existing
[Polynomial/Formal](Polynomial/Formal.agda) bridge already uses its ring and
coefficient laws for formal Bézout calculations. Replacing fixed-size vectors
with that HIT would require recovering degree and coefficient data and would
change the public interfaces. The universal-property evaluation API is useful
on the generic polynomial representation, but does not directly replace all
local Horner equations or their quantitative estimates.

Finite sums already use generic big operations through
[Polynomial/FiniteSumAlgebra](Polynomial/FiniteSumAlgebra.agda). Generic ordered
sum monotonicity exists, but the selected-term bounds also track the omitted
index and the native rational embedding `realNatural n`. No existing combined
bound was found that eliminates those adapters.

### Matching, completion and finite choice

Matching uses finite bijections and retains multiplicity. Hausdorff closeness
of finite sets is too weak. The library's finite-multiset HIT supplies a
permutation quotient, but not the fixed-degree matching premetric and its
quantitative root/coefficient comparison. Here the separated matching quotient
identifies vectors that match at every positive radius. It is not introduced
as a quotient by a supplied exact permutation.

[Completion/Construction](FundamentalTheorem/Completion/Construction.agda)
already uses the sequential completion and the native choice-free completeness
API. Generic premetric lifting modules were compared with the local
[Completion/Extension](FundamentalTheorem/Completion/Extension.agda) layer.
Those generic extension APIs target the sequential completion of their target
premetric; the local graph targets native coefficient vectors themselves.
Using the generic extension directly would require another target-completion
comparison and compatibility proofs. Retaining the local, explicitly
controlled extension is preferable to adding that infrastructure solely to
replace it.

The local construction bundles a whole modulus before eliminating truncation.
Radiuswise truncated witnesses are not selected into a global sequence. Finite
minimum/maximum radius and tail constructions also retain the actual common
bound needed by their consumers. A generic finite-choice theorem alone does
not supply that quantitative bound.

### Small algebra helpers retained

The commutative-ring solver is itself an existing library implementation.
Direct named matches have been used above, while local coordinate identities
that are naturally one solver invocation remain small abstract lemmas. Some
similar real power or square-product helpers elsewhere are private; importing
private implementation details or widening their public APIs just to remove a
short proof would exceed this refactor's scope.

`finitePositivePower` remains a two-clause recursion. The library also has
`_ℚ₊^ⁿ_` and generic monoid folds, but direct substitutions made the dependent
real product-bound check run substantially longer without completing during
the trial. Those attempts were reverted. A future consolidation should add
a small computation-law interface that controls normalization, then recheck
the quantitative consumers; mathematical equivalence alone is insufficient
reason to keep an unvalidated substitution.

Some apparently relevant ordered-ring strict cancellation lemmas are commented
unfinished statements, not usable proofs. The native positive-scaling
reflection argument therefore remains in place. No theorem was replaced by a
weaker hypothesis or a statement-only interface.

## Validation

All 16 edited Agda modules were checked with `agda-codex` after their final
source edits; every final check returned **exit code 0**. The integration checks
also returned **0** for:

- [the Complex facade](../Complex.agda);
- [Analysis/Everything](../Everything.agda);
- [Cubical/Analysis](../../Analysis.agda).

The final source-hash audit has **213/213 current successful snapshots** across
Complex, its supporting real root modules and the checked entry points. None
has holes, unsolved metas, constraints or warnings. These snapshots supplement
the integration checks; source-hash agreement alone is not a dependency check.

The transitive import audit reaches **702 Analysis modules / 1101 total
modules**, with no missing imports, orphan Analysis modules, cycles, forbidden
carrier/choice imports, or source-assumption flags. No postulates, unsafe
options or theorem-premise changes were introduced. Changed sources have no
trailing whitespace, `git diff --check` passes, and the local links in this
report, the Complex README and Analysis progress document resolve.

This refactor does not change the status of any FTA formulation. In particular,
the open general exact-root and small-separated-factorization obligations
remain open.
