# Sequential real analysis development

This directory develops real analysis from the sequence-backed completion in
`Cubical.Relation.Premetric.Completion.Alternative.Sequential`.  Its organizing
principle is that operations are extensions of rational functions.  Proofs
should use the recently developed Cauchy-continuous, completion-centered, and
uniformly-continuous lifting APIs instead of recursively rebuilding operations
from the constructors of a particular real-number HIT.

## Native complex analysis — 2026-10-08

Constructed series primitives and their FTC (2026-10-12):
[complex formal primitives](Complex/Series/PowerSeries/Primitive.agda) now
reuse the real coefficient construction in both coordinates. Their formal
derivative recovers the original coefficients and their derivative majorant
is exactly the original majorant. Native convergence of the original
majorant at any nonnegative radius therefore constructs a convergent
primitive and a uniform derivative at that same radius.

[Domain values](Complex/Series/PowerSeries/Primitive/Domain.agda) are actual
functions on the closed convergence norm ball, normalized to the specified
constant at zero. The derivative is intrinsic to chords within that domain.
The [parameter-value FTC](Complex/Integration/LineIntegral/FundamentalTheorem/Along.agda)
generalizes the existing ambient theorem's chain-rule proof. The
[path application](Complex/Integration/LineIntegral/PowerSeries/Primitive.agda)
constructs integrability and endpoint values, using the existing interval
retraction for total parameter functions. It needs no ambient primitive,
separate derivative-majorant witness or strict radius gap.

[Finite contours](Complex/Integration/Piecewise/PowerSeries/Primitive.agda)
now have endpoint formulas, closed-path zero and path independence for a
common series, center and radius. Canonical values at the corners supply
the telescoping primitive. Only representations of the integrand along
each piece are required. The reusable real
[successor-series lemma](Real/Series/Successor.agda) shifts a native Cauchy
modulus explicitly, and all other finite bounds are eliminated into
propositions. No choice hypothesis is added.

Next: prove compatibility of the constructed primitives under Taylor
reexpansion, normalizing at the primitive's value at the new center; then
apply this to coherent differently centered local descriptions. Arbitrary
unrelated local primitives are not claimed to glue. Holomorphic Taylor
representation and Cauchy integral theory remain separate.

Constructed-primitive validation (2026-10-12): all 19 changed Agda files
(12 new modules, five facade updates and two reused integration modules)
and both Analysis entrypoints pass `agda-codex` with exit code 0 after their
final source edits. All 437 audited complex/support/root snapshots match
current sources and report zero holes, metas, constraints and warnings.
All 921 Analysis modules are reachable (1,322 transitive Cubical
modules), with no missing imports, cycles, orphans, choice dependencies,
alternate real carriers or source flags. All 379 audited local documentation
links resolve; whitespace checks pass.

Centered and piecewise power-series FTC (2026-10-11):
[Geometric path translation](Complex/Integration/Path/Translation.agda)
preserves the certified velocity and speed bound; its
[line-integral covariance](Complex/Integration/LineIntegral/Translation.agda)
reduces to equality of integrands. The
[centered theorem](Complex/Integration/LineIntegral/PowerSeries/Centered.agda)
reuses the strict-interior FTC for local series in `z-center`, with
`0 ≤ r`, `norm(γ(t)-center) ≤ r < R` and one original native majorant.
It derives the uniform primitive estimate, integrability, endpoint formula
and closed-path zero. Only along-path representations of the primitive and
its formal derivative are required.

[Derivative compatibility](Complex/Series/PowerSeries/Translation/Derivatives.agda)
identifies every reexpanded derivative with the original derivative at the
translated point. This uses intrinsic tower uniqueness, avoiding another
infinite-sum rearrangement. The
[canonical Taylor application](Complex/Integration/LineIntegral/PowerSeries/Reexpansion.agda)
uses the original majorant and `norm(center)+r<R`; one intermediate radius
is eliminated into propositional FTC conclusions.

The [finite piecewise theorem](Complex/Integration/Piecewise/PowerSeries.agda)
allows different centers, coefficients and radii on each piece. Certificates
may remain propositionally truncated, while a common primitive and derivative
make endpoint values telescope. Endpoint integrals, closed-path zero and
path independence are proved with the existing graph-path integration API.
This does not derive a primitive from holomorphicity or claim Cauchy's theorem.

Construction of primitives is completed in the 2026-10-12 continuation
above, reusing [real formal primitives](Real/Series/PowerSeries/Logarithm/Primitive.agda).
Pointwise C¹-to-uniform upgrades, holomorphic Taylor representation and Cauchy
integral theory remain separate obligations.

Centered FTC validation: all 12 changed Agda files (seven new modules and
five facade updates) and both Analysis entrypoints pass `agda-codex` with exit
code 0 after their final source edits. All 425 audited complex/support/root
snapshots match current source hashes and report zero holes, metas,
constraints and warnings. All 909 Analysis modules are reachable
(1,310 transitive Cubical modules), with no missing imports, cycles,
orphans, choice dependencies, alternate real carriers or source flags.
All 350 audited local documentation links resolve; whitespace checks pass.

General complex reexpansion (2026-10-11):
[the translation API](Complex/Series/PowerSeries/Translation.agda) now
constructs native Cauchy convergence for the canonical Taylor coefficients
at every interior center, on each specified `0 ≤ r` with
`norm(center) + r < R`. Exact finite binomial translation and coefficientwise
limits connect the original partial sums to the normalized derivative tower.
A coefficient bound at one larger radius gives a common geometric majorant
for all finite translated polynomials. The real
[weighted-bound theorem](Real/Series/PowerSeries/WeightedBound.agda) and
[limit-interchange theorem](Real/Series/PointwiseLimit.agda) preserve native
Cauchy witnesses without selecting a countable family of tails.

[Representation](Complex/Series/PowerSeries/Translation/Representation.agda)
identifies the reexpanded sum with every supplied original sum; the
[canonical specialization](Complex/Series/PowerSeries/Translation/Canonical.agda)
uses the already constructed original value without an additional sum premise.
[Uniform representation and remainder estimates](Complex/Series/PowerSeries/Translation/Uniform.agda)
hold on closed bounded families strictly inside the translated radius. The
remainder bound is the tail of the constructed translated majorant.

The centered line-integral and piecewise applications are completed in the
continuation above. Taylor representation from holomorphicity alone, the
pointwise C¹-to-uniform upgrade and Cauchy integral theory remain separate.

Reexpansion validation: all 25 changed Agda files (19 new modules, five
facade updates and one comment update) and both Analysis entrypoints pass
`agda-codex` with exit code 0 after their final edits. All 418 audited
complex/support/root snapshots match current sources and report zero holes,
metas, constraints and warnings. All 902 Analysis modules are reachable
(1,303 transitive Cubical modules), with no missing imports, orphans,
cycles, choice dependencies, alternate real carriers or source flags.
All 315 audited local documentation links resolve; whitespace checks pass.

Local uniqueness and expansion centers (2026-10-11):
[intrinsic derivative uniqueness](Complex/Calculus/Derivative/OpenSubspace/Uniqueness.agda)
and [tower uniqueness](Complex/Calculus/Derivative/Tower/OpenSubspace.agda)
now hold on open subspaces without supplied ambient extensions. Subtraction
reduces competing estimates to the ambient zero function. The existing
open-subspace adapter is generalized to arbitrary source coordinates and
single-point estimates, with its previous interfaces retained.

[Taylor coefficient uniqueness](Complex/Series/PowerSeries/Taylor/Uniqueness.agda)
identifies coefficients from any representing derivative tower. Two native
convergent series agreeing on a common positive open ball have equal
coefficients, even with different outer radii and convergence witnesses.

A [canonical derivative tower on the whole open convergence ball](Complex/Series/PowerSeries/RepeatedDerivative/Interior.agda)
now supplies every derivative and its formal-series sum at every interior
point. [Taylor coefficients at arbitrary centers](Complex/Series/PowerSeries/Taylor/Center.agda)
are constructed, have normalized derivative-series sums, are independent of
the outer radius/witness, and recover the original coefficients at zero.
[Reexpansion identification](Complex/Series/PowerSeries/Taylor/Reexpansion.agda)
proves that any supplied convergent translated representation has exactly
these coefficients. Translation uses the ordinary radius condition
`norm(center) + inner ≤ outer` and preserves derivative increments.

[Sine and cosine Taylor series](Complex/Series/PowerSeries/Taylor/Elementary/Translation.agda)
now represent the functions at every complex center and increment, joining
the existing exponential result. The proof uses derivative addition laws,
normalization at zero, and existing sum operations.

This checkpoint supplied the coefficients and uniqueness used by the
completed general reexpansion continuation above. No choice or alternate
real carrier is used.


Validation: all 16 changed Agda files (11 new modules, the generalized
open-subspace proof and four facade updates) and both Analysis entrypoints
pass `agda-codex` with exit code 0 after their final source edits. All 398
audited complex/support/root snapshots are current with zero holes, metas,
constraints and warnings. All 883 Analysis modules are reachable
(1,284 transitive Cubical modules), with no missing imports, orphan
modules, cycles, choice dependencies, alternate real carriers or source flags.
All 291 audited local documentation links resolve; whitespace checks pass.

Higher complex derivatives and Taylor continuation (2026-10-10): one native
original norm-majorant witness at an outer radius now constructs convergence
of every finite repeated formal derivative on smaller radii. The
[constructed derivative tower](Complex/Series/PowerSeries/RepeatedDerivative/Tower.agda)
has uniform series sums, successive complex derivatives and continuity;
uniform coordinates give uniform derivatives at every order.

The [Taylor theorem for represented series](Complex/Series/PowerSeries/Taylor/Interior.agda)
recovers the original coefficients from the derivative values at zero and
proves uniform representation on intrinsic open l1 balls, with a tail bound
from the original majorant. The proof reuses real repeated derivatives,
real exponential coefficients and the existing complex interior theorem.
Explicit elementary towers have the exponential fixed point and trigonometric
four-cycles; their repeated-series sums give Taylor representations at zero,
and the exponential's addition law gives representation at every center.
General reexpansion and Taylor representation from holomorphicity alone are
not claimed. No countable family of selected moduli is introduced.

Higher-derivative/Taylor validation: all 13 changed Agda files (ten new modules
and three facade updates) and both Analysis entrypoints pass `agda-codex`
with exit code 0. All 387 audited snapshots match current sources with zero
holes, metas, constraints and warnings. All 872 native Analysis modules are
reachable (1,273 transitive Cubical modules), without missing imports, cycles,
orphans, choice dependencies or alternate real carriers. Source,
documentation-link and whitespace audits are clean.

Elementary complex-series continuation (2026-10-10): the standard complex
exponential, sine and cosine series now sum to the existing functions, with
absolute native Cauchy convergence everywhere and uniform convergence on
bounded families. The coefficients are the embedded native real sequences;
the proofs reuse real factorial estimates, divided powers, finite binomial
algebra, complex Mertens, and termwise Euler identities. No elementary-function
definition or real carrier changes.

The [trigonometric FTC application](Complex/Integration/LineIntegral/Trigonometric.agda)
proves the sine/cosine endpoint integrals and closed-path zero for every
certified uniform path. Its radius margin is the existing path-image bound
plus one, so convergence, derivative bounds and integrability are conclusions.
The higher continuation above now supplies repeated derivatives and Taylor
representation for convergent series. The general C¹ compact-domain upgrade
and Cauchy integral theory remain later work. See the
[series notes](Complex/Series/README.md#elementary-complex-power-series).

Elementary-series validation: all 14 changed Agda files (12 new modules and
two facade updates) and both Analysis entrypoints pass `agda-codex` with
exit code 0. All 377 audited snapshots match current sources with zero holes,
metas, constraints and warnings. All 862 native Analysis modules are reachable
(1,263 transitive Cubical modules), without missing imports, cycles, orphans,
choice dependencies or alternate real carriers. Source, documentation-link
and whitespace audits are clean.

Local logarithm continuation (2026-10-10): the
[right-half-plane branch](Complex/Transcendental/Logarithm/README.md) is an
actual intrinsic function, constructed from the existing real logarithm and
polar restricted-arcsine argument. It is continuous, has complex derivative
`1/z` everywhere on its open domain, agrees with the positive real logarithm,
and is zero at one. The pointwise inverse derivative theorem shares the
previous uniform absorption estimate and needs no global bound.

For a certified path with a supplied positive rational lower bound on its
real part, the branch now constructs a logarithmic lift and proves the
native reciprocal endpoint formula and closed-path zero. This uses the
existing path-image bound and interval clamp. Supporting theorems establish
modulus continuity, positive reciprocal continuity and uniform continuity
of the real logarithm above a positive bound. Radiuswise witnesses remain
truncated; no general compactness upgrade is assumed.

Local-logarithm validation: all 26 changed Agda files (17 new modules and
nine updates) pass direct checks after their final edits, and both Analysis
entry points pass with exit code 0. All 343 audited snapshots match current
sources with no holes, metas, constraints or warnings. All 829 Analysis
modules are reachable (1,230 transitive Cubical modules), with no missing
imports, cycles, orphans, choice dependencies or other real carriers.
Source, documentation-link and whitespace audits are clean.

Complex contour continuation (2026-10-10): finite piecewise paths now reuse
library graph paths and have concatenation, reversal and a telescoping FTC.
Smooth real parameter changes construct actual reparameterized curves and
tangents; substitution under supplied standard uniform continuity proves
endpoint-preserving invariance and orientation reversal. Radiuswise
continuity supplies individual bounds under truncation, without choosing a
modulus.

The uniform divided-difference criterion, bounded uniform inverse theorem,
and exponential uniform derivative estimates extend the analytic tools.
Exponential endpoint formulas apply to every certified path and finite
contour. Supplied continuous logarithmic lifts acquire a derivative and give
the reciprocal integral as their endpoint change. A supplied single-valued
branch therefore gives closed-path zero; the explicit positive circle with
lift `(0,t)` instead has reciprocal integral `(0,2π)`, proved nonzero.
These statements use native coordinate Riemann integrals throughout.

This contour checkpoint used supplied logarithmic lifts; the continuation
below constructs an actual half-plane branch. Arbitrary pointwise C¹ data
are still not upgraded to uniform differentiation. Power-series
differentiation and Cauchy integral theory remain open. See the
[updated integration notes](Complex/Integration/README.md) for precise
hypotheses and module links.

Continuation validation: all 34 changed Agda files (28 new modules and six
updates) passed direct `agda-codex` checks after their final edits, followed
by both Analysis entry points with exit code 0. All 324 audited snapshots
match current sources with no holes, metas, constraints or warnings. The
import audit reaches all 812 native Analysis modules and 1,213 Cubical
modules transitively, with no missing imports, orphans, cycles or forbidden
real/choice dependencies. Source, documentation-link and whitespace checks
are clean.


Complex line-integral calculus (2026-10-09): the user-requested
[integration layer](Complex/Integration/README.md) defines complex Riemann
integrals coordinatewise from the native real tagged-partition integral and
line integrals as integrals of `f(γ(t))*γ′(t)`. A bounded uniform path package
certifies the velocity and its speed bound. Uniform complex derivative
estimates, their indexed chain rule and real-parameter coordinate bridges
prove the derivative of `F ∘ γ`; the existing real Newton–Leibniz theorem
then constructs the line integral with endpoint value `F(γ(b))-F(γ(a))`.
The primitive hypothesis is uniform only along the path, with a separate
bound on `f ∘ γ`. It is not inferred from pointwise holomorphicity.

The endpoint theorem gives closed-path vanishing and path independence.
The polynomial application proves the primitive estimate and derivative
bound from existing Newton/coefficients estimates and the derived path-image
bound; it integrates every existing formal polynomial derivative along any
certified path. Straight segments have proved velocity and endpoints, and
constant integrands have their displacement formula. No choice axiom, new
real carrier, division by the path velocity or separate integrability
hypothesis is introduced. The continuation above implements finite piecewise
paths, reversal/reparameterization and elementary primitive applications;
the general compact C¹ upgrade and Cauchy integral theory remain later work.

FTC validation completed on 2026-10-10: all 24 changed Agda files passed
direct checks after their final edits, followed by both Analysis entry points
with exit code 0. The 295 audited complex/supporting source and facade
snapshots match their current source hashes and report no holes, unsolved
metas, constraints or warnings. All 784 Analysis modules remain reachable;
the 1,183-module transitive import audit found no missing imports, cycles,
choice dependencies or `CauchyReals` imports.

Complex series products (2026-10-09): the [product layer](Complex/Series/Product.agda)
adds finite convolution algebra, coordinate formulas, scalar/conjugation and
singleton/unit laws. Native Mertens constructs the product sum with only one
absolutely convergent factor; two absolute native Cauchy witnesses yield an
absolute native Cauchy product. The sum of product norms is bounded by the
product of the two norm sums. The [power-series product](Complex/Series/PowerSeries/Product.agda)
identifies coefficient convolution with multiplication of summed values, and
[radius-majorant closure](Complex/Series/PowerSeries/Product/Bounds.agda)
preserves the full native Cauchy hypothesis at the same nonnegative radius.
Existing uniform convergence and continuity then apply to the product.
The geometric theorem is strengthened to absolute native Cauchy convergence
on the full Euclidean unit disk.
The proofs reuse real finite convolution, native Mertens, the sealed absolute
product theorem and real power-series multiplication. No choice principle or
conversion from radiuswise convergence to a global modulus is introduced.
The next milestone is power-series differentiation through continuous divided
differences, followed by identification of the elementary complex series.

Product validation: all ten new or edited Agda files (six new modules and
four updates), the Complex facade and both Analysis entry points pass
`agda-codex` with exit code 0 after final edits. All 274 audited complex/root
snapshots match current sources and report zero holes, metas, constraints
and warnings. The import audit reaches all 763 Analysis modules and 1162
Cubical modules transitively, with no missing imports, orphans, cycles or
Cauchy-real/choice dependencies. Source checks, all 142 local documentation
links and `git diff --check` are clean.

Complex series (2026-10-09): the [new series layer](Complex/Series/README.md)
constructs coordinate partial sums and unique sums, with algebra, conjugation,
tail removal and reconstruction, norm bounds and quantitative remainder
bounds. Native Cauchy majorants give absolute convergence and actual complex
sums; uniform majorants give uniform sums and continuity. The power-series
API supplies absolute and uniform convergence at a supplied l1 radius and
continuous values along bounded continuous coordinates. The geometric-series
theorem covers the full Euclidean unit disk and proves `(1-z) * sum = 1`.
The implementation reuses the real series APIs and the existing complex
sequence and modulus theorems. It does not select global moduli from
radiuswise truncated tail bounds. The subsequent product checkpoint above
adds Cauchy products and power-series multiplication.

Series validation: all 15 new or edited Agda files (14 new modules and the
Complex facade), `Everything.agda` and `Cubical/Analysis.agda` pass
`agda-codex` with exit code 0 after final edits. All 268 audited complex/root
snapshots are current, with zero holes, metas, constraints and warnings.
The import audit reaches all 757 native Analysis modules (1156 Cubical modules
transitively), with no missing imports, orphans, cycles or Cauchy-real/choice
dependencies. Source checks, all 133 local documentation links and
`git diff --check` are clean.

Elementary complex derivatives (2026-10-09): the
[exponential derivative](Complex/Transcendental/Exponential/Derivative.agda)
proves `expℂHasSelfDerivative`, and the
[trigonometric derivatives](Complex/Transcendental/Trigonometric/Derivative.agda)
prove `sinℂHasDerivative` and `cosℂHasDerivative`. The public facades also
export `expℂ-isEntire`, `sinℂ-isEntire` and `cosℂ-isEntire`. These are full
complex derivatives of the existing native functions. The exponential proof
combines the existing real derivative remainders and bounds coordinate
increments by the full complex displacement. Sine and cosine reuse the
complex chain and algebra rules on their exponential formulas. The
[proof notes](Complex/Calculus/README.md#elementary-complex-derivatives)
record the decomposition and constructive boundary. No new real functions,
power-series construction, choice assumptions or global radius selection are
introduced. Priorities 1 and 2 of the missing-layer plan are now complete;
the subsequent series checkpoint above supplies their first convergence
and continuity layer.

Elementary-derivative validation: all 10 new or edited Agda files (six new
modules and four updates), the Complex facade and both Analysis entry points
pass `agda-codex` with exit code 0 after the final edits. All 254 audited
complex/root source snapshots are current and have zero holes, metas,
constraints and warnings. The import audit reaches all 743 native Analysis
modules (1142 Cubical modules transitively), with no missing modules, orphan
Analysis modules, cycles or Cauchy-real/choice dependencies. The source and
whitespace checks are clean.

Differential calculus (2026-10-09): the [new layer](Complex/Calculus/README.md)
uses a division-free, complex-linear remainder bound with the existing l1
norm and radiuswise truncated neighbourhoods. It proves pointwise derivative
uniqueness by horizontal restriction and native real uniqueness; derivatives
imply continuity and a local linear bound. Constants, identity, linear maps,
sums, negation, subtraction, products and composition have derivative rules,
including coordinate versions. A continuous divided-difference criterion
certifies the existing list-polynomial and monic formal derivatives. The
holomorphic/entire interfaces prove polynomial examples and closure under
algebra and composition. No derivative continuity or choice axiom is assumed.
The elementary derivative extension above completes the
exponential/sine/cosine target. Intrinsic open-domain adapters remain future
work after the general complex series layer.

Calculus validation: all 17 new or edited Agda files and both Analysis entry
points pass `agda-codex` with exit code 0 after integration. All 248 source
snapshots in the complex/root audit match current files and report zero holes,
unsolved metas, constraints or warnings. The import audit reaches all 737
native Analysis modules (1136 Cubical modules transitively), with no missing
imports, cycles, orphan modules or Cauchy-real/choice dependencies.

Elementary functions (2026-10-09): the
[missing-layer plan](Complex/DEVELOPMENT_GAPS_2026-10-09.md) sets the order for
differentiation, general series, domain/reciprocal APIs and contour integration.
Its first milestone adds native complex exponential,
sine and cosine, their algebraic laws, real-axis compatibility, periods,
continuity and preservation of supplied sequence limits. The exponential has
modulus `expℝ (re z)` and positive apartness from zero. A polar witness gives
an actual logarithm, and positive apartness is interderivable with truncated
exact logarithm existence; no global argument/logarithm branch is selected.
The public `Complex.Transcendental` facade exports the new layer. Its
elementary complex derivatives are now proved by the extension described
above; the elementary-series continuation now proves their standard complex
power-series representations too.

Validation: all 21 new or edited Agda files and both Analysis entry points
pass `agda-codex` with exit code 0. All 232 source snapshots in the expanded
complex/root audit match the current files, with zero holes, unsolved metas,
constraints or warnings. The import audit reaches all 721 native Analysis
modules (1120 Cubical modules transitively), with no missing imports, cycles,
or Cauchy-real/choice dependencies.

Library reuse audit (2026-10-09): the [whole-folder review](Complex/REUSE_AUDIT_2026-10-09.md)
covers all 197 complex modules and the facade. Sixteen modules now reuse
existing ring/unit laws, real square-root laws, finite products, vector and
finite-index operations, rational enumeration, least-witness search, finite
decidability, and sum-isomorphism restriction. Public theorem types and the
choice-free native carrier are preserved. The report explains the polynomial,
matching, completion and quadratic dependency boundaries that remain necessary.

Reuse validation: all 16 edited Agda modules, the Complex facade,
`Everything.agda`, and `Cubical/Analysis.agda` returned exit code 0 after the
final source edits. All 213 checked-module snapshots are current and clean.
The import audit reaches 702 Analysis modules / 1101 total modules, with no
missing imports, orphans, cycles, forbidden carrier/choice imports, source
assumption flags, or trailing whitespace. The three updated documents have
no broken local links.

Update 2026-10-09: stage 6 now includes
[`nearZeroNet : NearZeroNetTheorem`](Complex/FundamentalTheorem/NearZeroNet.agda)
with the original catalogue type. The output is a finite Gaussian net with
small residual at its centers and coverage of every sufficiently
small-residual point. Synthetic division retains the queried point in an
approximate factorization; quantitative matching finds its nearby center.

The [cluster layer](Complex/FundamentalTheorem/Clusters/README.md) now proves
finite geometric margins, local matching of approximate factorizations,
universal spectral certificates, openness and nonvacuity, and a uniform gap
between actual roots of separated spectra. Finite matchings restrict to
separated blocks with their bijections intact, and a whole rational modulus
controls both block coefficient vectors. Exact cluster data are constructed
for the empty case, a supplied small single spectrum, and strongly separable
polynomials. General `SmallSeparatedFactorization` remains open: persistent
finite partitions, their local extension to exact completed block factors,
and coefficient reconstruction are the next obligations. No catalogue
statement was weakened and no choice or rational-presentation premise was
added.

Cluster/net validation (2026-10-09): all 18 new or edited Agda files checked
with `agda-codex` after their final source edits. The public complex facade,
`Everything.agda`, and `Cubical/Analysis.agda` also returned exit code 0.
The pass adds 15 modules. All 213 affected-module snapshots match the current
sources, with no holes, unsolved metas, constraints, or warnings. The
transitive audit reaches 702 Analysis modules / 1099 total modules, with no
missing imports, orphans, cycles, forbidden carrier/choice imports,
source-assumption flags, or trailing whitespace. Local links in all seven
updated construction, survey, and progress documents resolve.

The follow-up [FTA literature survey](Complex/FTA_SURVEY_2026-10-08.md) compares
exact separable, completed multiset, presented-coefficient, weak, clustered,
projective, and point-free formulations. At the user's request, their
[statements](Complex/FundamentalTheorem/Formulations/README.md) were formalized
before attempting their proofs. A checked statement type is distinct from
an inhabited theorem. Exact FTA under strong separability is now proved;
unrestricted native exact FTA is still open.

The statement-first checkpoint is complete: all statement modules and both
Analysis entry points checked with exit code 0, and 139 affected-module
snapshots matched their current sources with no holes, metas, constraints,
or warnings. The transitive audit reached 628 Analysis modules / 1019 total
modules and found no missing imports, orphans, cycles, forbidden carrier or
choice imports, or source assumption flags. Proof work resumes from the
positive Bézout certificate and local Newton interfaces.

After that checkpoint, [Separable/Certificate.agda](Complex/FundamentalTheorem/Separable/Certificate.agda)
proves the formal-to-evaluation bridge and an explicit derivative inverse at
each supplied root. [Polynomial/Newton.agda](Complex/Polynomial/Newton.agda)
inhabits `LocalNewtonRootTheorem`: its deterministic contraction constructs
an actual native root, a ball bound, and uniqueness under the stated inverse,
remainder, and correction inequalities. The subsequent proof pass derives
these premises from strong separability and preserves the formal certificate
through finite deflation.

The post-checkpoint proof pass also finished cleanly: all five new proof
modules, both changed complex facades, and both Analysis entry points checked
with exit code 0. That snapshot audit had 144/144 valid targets; its
import audit reached 633 Analysis modules / 1024 total modules, with the same
zero-error source/import checks. The earlier statement-only checkpoint counts
above are retained to record that it preceded this proof work.

**The first exact FTA milestone is now proved.**
[Separable/Root.agda](Complex/FundamentalTheorem/Separable/Root.agda) inhabits
`StronglySeparableRootExistence`, and
[Separable/Factorization.agda](Complex/FundamentalTheorem/Separable/Factorization.agda)
inhabits `StronglySeparableFundamentalTheorem`, including pairwise apart roots.
Both use the original positive formal Bézout hypothesis from the catalogue.

The new proof bounds all small-residual points by Horner coercivity, derives
uniform two-point Newton remainder estimates and a derivative inverse bound,
and chooses finitely many rational tolerances and one approximate center
inside truncation. Deterministic native contraction then produces the exact
root. `separableDeflation : SeparableDeflation` transports the formal
coefficient certificate through exact division, using the existing generic
polynomial ring to justify coefficient calculations. Finite induction gives
the exact factorization, and the derivative-unit identity proves positive
separation of every new root from the remaining roots. No choice principle
or extra convergence hypothesis is used. The subsequent quantitative
matching result is described below.

Separable-FTA validation (2026-10-08): all 21 new or edited Agda modules
and facades checked with `agda-codex` after their final source edits, and both
`Everything.agda` and `Cubical/Analysis.agda` returned exit code 0. The complete
affected-module snapshot audit at that checkpoint had 161/161 successful targets,
with no holes, metas, constraints, or warnings. The import audit reaches
650 Analysis modules / 1044 total modules, with no missing imports, orphans,
cycles, forbidden carrier/choice imports, or source-assumption flags.
The new proof pass adds 17 modules; historical checkpoint counts above remain
unchanged.

**Quantitative matching is now proved, completing stage 4.**
[Matching/RootMatching.agda](Complex/FundamentalTheorem/Matching/RootMatching.agda)
inhabits `QuantitativeRootMatching`, and
[Matching/FactorContinuity.agda](Complex/FundamentalTheorem/Matching/FactorContinuity.agda)
inhabits `QuantitativeFactorContinuity`. Both supply explicit rational
modulus functions with the catalogue's original types. Matching preserves
multiplicities, including repeated roots, without a separability hypothesis.

The proof converts coefficient bounds into a rational root bound, uses
finite located search to find one nearby factor, and controls the remaining
coefficients by synthetic division. Generic ring proofs justify coefficient
invariance under arbitrary finite permutations and exact removal of a
supplied factor. All choices stay finite and truncated at the requested
radius. Native coordinate closeness and the l1 norm are related with their
explicit factor-of-two estimates; the Euclidean modulus is used for
multiplicative lower bounds.

[Matching/ApproximateEquivalence.agda](Complex/FundamentalTheorem/Matching/ApproximateEquivalence.agda)
also supplies `approximateFormulationsInterderivable`. Its reverse implication
uses the assumed approximate factorization once, together with the new
uniform bounds, to produce a small residual. It does not simply appeal to
the independently proved approximate-root theorem.

Stages 1–5 of the [survey plan](Complex/FTA_SURVEY_2026-10-08.md) are complete.
[Completion.agda](Complex/FundamentalTheorem/Completion.agda) now supplies
`completedMultisetFundamentalTheorem` with the original catalogue type:
a constructed Gaussian-rational matching completion, an equivalence with all
native monic coefficient vectors, its finite-factor law, and whole local
moduli in both directions. The
[construction notes](Complex/FundamentalTheorem/Completion/README.md) explain
the choice boundary. Rational inputs use decidable least-witness search;
arbitrary native inputs use completion induction and reflected Cauchy
witnesses. No native coefficient is assumed to have a chosen rational name.
General separated clusters, weak FTA, presentation-sensitive exact roots, projective
roots, and unrestricted native exact FTA remain further work.

Matching validation (2026-10-08): all 21 new or edited Agda files checked
with `agda-codex` after their final source edits; the complex facade,
`Everything.agda`, and `Cubical/Analysis.agda` also returned exit code 0.
That pass added 16 modules. Its affected-module snapshot audit had
177/177 current successful targets, with no holes, metas, constraints,
or warnings. The transitive audit reaches 666 Analysis modules / 1060 total
modules, with no missing imports, orphans, cycles, forbidden carrier/choice
imports, source-assumption flags, or trailing whitespace. Local links in all
five updated progress/survey documents were checked.

Completed-multiset validation (2026-10-08): all 23 new or edited Agda files
checked with `agda-codex` after their final source edits. The public complex
facade and both Analysis entry points also returned exit code 0. This pass
adds 21 modules. The affected-module snapshot audit has 198/198 current
successful targets, with no holes, metas, constraints, or warnings. The
transitive import audit reaches 687 Analysis modules / 1084 total modules,
with no missing imports, orphans, cycles, forbidden carrier/choice imports,
source-assumption flags, or trailing whitespace. All local links in the six
updated construction, survey, and progress documents resolve. The original
completion and correspondence statement types are unchanged; only their
status comment was updated.

The user expanded the scope toward a constructive fundamental theorem of
algebra. [Complex/README.md](Complex/README.md) records the selected statement,
proofs, and remaining work. The new public `Cubical.Analysis.Complex` uses
pairs of native sequential reals, with no comparison to another real carrier.

Implemented: the complex ring and witnessed inverse, conjugation and squared
norm, product premetric and l1 estimates, multiplicative Euclidean modulus
with triangle inequality and norm comparison, arithmetic continuity, coordinatewise
native completeness, and deterministic contraction fixed points. Polynomial
support includes Horner algebra, exact synthetic division, norm/Lipschitz
majorants, degree-indexed monic coefficients, linear-factor reconstruction,
continuity of multiplication by a linear factor, and degree-preserving
translation representing `p(center + z)` without coefficient zero tests.

Positive real roots of every nonzero natural degree use native exp/log.
Nonnegative real square roots, including zero, are constructed from the
explicit sequence `√(x + (2⁻ⁿ)²)` with geometrically bounded increments;
uniqueness, monotonicity, and multiplication laws are proved. Finite vectors
have truncated near-maximizers at each requested accuracy.
Exact square roots on either open complex half-plane imply
radiuswise truncated approximate square roots everywhere. These prove
`approximateFundamentalTheorem-degreeTwo` for arbitrary monic quadratics:
the linear coefficient is exact and the constant coefficient meets the
requested tolerance. There is also an exact unique root of `z²-z+c` in the
quarter-radius l1 ball for `normℂ c ≤ 1/8`, and an exact factorization of that
family.

Native polar form now has addition and De Moivre laws, an actual argument
on the right half-plane, and truncated arguments on a finite rotated cover
away from zero. These give exact truncated nth roots for points of positive
modulus, unit nth roots, and approximate nth roots for every input. Every
binomial `X^(suc n) + a` consequently has approximate roots. Normalization
and unit roots also give optimal two-term cancellation: a unit nth power
can make the modulus of `a + b*u^(suc n)` equal to `abs (|a| - |b|)` when
both coefficients have positive modulus.

The finite coefficient-selection estimate is now constructed. Positive
weighted-power roots and located order give an initial balanced radius;
finite prefix near-maxima yield a nonincreasing index chain and a bounded
certificate of three adjacent equal indices. For `N` nonconstant
coefficients the shrink factor is `q = 4^(-N)`, with `N*q ≤ 1/4`.
`finitePowerRemainderScale` produces a positive radius and a selected term
`s` satisfying `L*t < s + ε`, `s < t + ε`, and
`sum(other terms) ≤ s/4 + N*ε/q^N`, where `L = (q^N)^(2N-1) > 0`.
Only a finite chain is constructed. Positive roots also now have uniqueness,
monotonicity, and strict monotonicity lemmas. Finite monomial expansion
isolates the selected complex term and bounds the remaining sum's modulus.

**The selected arbitrary-degree approximate FTA milestone is now proved.**
[Complex/FundamentalTheorem/Approximate.agda](Complex/FundamentalTheorem/Approximate.agda)
exports `approximatePolynomialRoots : ApproximateRootExistence` and
`approximateFundamentalTheorem : ApproximateFundamentalTheorem`. For every
degree, monic polynomial, and positive rational tolerance, the latter gives
a truncated finite vector of roots whose linear factors approximate all
coefficients. Neither theorem has a supplied-descent, apartness, or
root-separation premise.

The scale construction now applies to every monic polynomial. At the chosen
radius, a unit-power direction cancels the selected term against the constant
coefficient. A finite positive rational error choice absorbs the remaining
terms. For constant modulus `A > 0`, the new modulus is below `(1-L/8)*A`,
with `0 < 1-L/8 < 1` depending only on degree. Located order handles small
or zero constant coefficients without a zero test, giving
`uniformPolynomialDescent`. Finite translated iteration and geometric decay
prove approximate roots; `approximateRoots→factorization` then uses finite
induction, explicit remainders, and coefficient continuity to produce the
linear factors. No infinite descent path or tolerance-indexed witness family
is chosen. The completed-multiset equivalence is established by the later
stage 5 construction above; unrestricted native exact FTA remains open.

Validation (2026-10-08): all 121 affected Agda modules and entry points
passed `agda-codex` with exit code 0 after their final edits, including
`Everything.agda` and `Cubical/Analysis.agda`. The saved check hashes match
the final sources; there are no holes, unsolved metas, constraints, or
warnings. The 117 new Agda files contain 6,346 lines. The transitive audit
reaches all 610 Analysis modules (1,001 modules in total), with no orphan
Analysis modules, missing imports, cycles, other-real-carrier or choice
imports, postulates, added options, or source holes. The diff and new files
pass whitespace checks, and local documentation links resolve.

## Design decisions

Analysis is choice-free by project policy: see [AGENTS.md](AGENTS.md) and the
[2026-09-06 removal record](CHOICE_FREE_2026-09-06.md). Countable-choice
assumptions and adapters are not allowed here, even as explicit parameters.

The circle development is recorded in [Circle/README.md](Circle/README.md).
It constructs the native quotient circle `ℝ/ℤ`, its abelian group and
separated turn premetric, and a choice-free winding number for uniformly
continuous loops. Short displacements replace the reference implementation's
trigonometric charts. The API includes subdivision independence, uniqueness,
extensionality, the endpoint formula for supplied real lifts, and degree for
circle self-maps. Examples compute constants, the identity, and every integer
traversal. Identification with the Cartesian circle and homotopy
classification remain separate work.

Verification for the circle development (2026-10-08): all twelve new modules,
the updated `Real` facade, `Everything.agda`, and `Cubical/Analysis.agda`
passed `agda-codex` with exit code 0 and no holes, unsolved metas,
constraints, or warnings. The source/import audit found no added postulates,
choice assumptions, unsafe options, or dependencies on another real carrier.

The preceding expansion is recorded in
[Boundedness, derivative limits, and series — 2026-09-15](LIMITS_2026-09-15.md):
boundedness from radiuswise uniform continuity, automatic bounds for
substitution and Lipschitz integral functions, uniform convergence of
indefinite integrals, preservation of uniform derivatives under pointwise
function limits and uniform derivative limits, construction from convergence
at one endpoint, and termwise differentiation of series. The limit and
series theorems do not assume continuity of the limiting derivative. They
retain uniform derivative hypotheses on the approximants and distinguish
radiuswise preservation results from existence using a native modulus.

The preceding expansion is recorded in
[Integration and FTC consequences — 2026-09-15](INTEGRATION_2026-09-15.md):
integral order/error bounds, uniform-limit and series integration, oriented
integrals within a closed interval, antiderivative uniqueness and monotonicity,
integration by parts, and substitution with a primitive constructed from
uniform continuity. Exact constructive hypotheses are documented there.

Verification for this expansion: all affected Agda modules, then
`Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda`, passed
`agda-codex` with exit code 0 and no holes, unsolved metas, constraints, or
warnings. The source/import audit found no added postulates, unsafe options,
choice assumptions, or imports from other real implementations. The Analysis
diff passed `git diff --check`, and the new report's local links resolve.
The largest aggregate checks use `+RTS -c -RTS` for compacting garbage
collection, with the wrapper's memory guard unchanged. Dependency checks
were split into smaller invocations when a full rebuild exceeded the guard.

The preceding implementation results are recorded in
[Fundamental theorem of calculus — 2026-09-15](FTC_2026-09-15.md): integration
of a radiuswise uniform derivative, integrability from the standard uniform
continuity predicate on a closed interval, differentiation of its accumulation
function, and interval additivity for existing integrals. Integrability from
the weaker radiuswise uniform continuity predicate remains open. See also
[Logarithm and exponential — 2026-09-06](LOGARITHM_2026-09-06.md): exponential
algebra/order/continuity, a choice-free local logarithm series, a reusable
approximate IVT, and now an unconditional exponential equivalence and global
logarithm from deterministic geometric iteration. The choice-dependent
global inverse construction remains removed. Uniform local power-series
derivative estimates and a separate total series candidate are also checked. The
positive reals now have a multiplicative abelian group built directly from
real arithmetic, with exp/log group isomorphisms to the additive reals and
unit, inverse, subtraction, and quotient correspondence laws. The preceding
pass is recorded in
[Analysis improvements — 2026-09-05](IMPROVEMENTS_2026-09-05.md): shared additive
and continuity proofs, an ordered integration API, inverse-trigonometric
properties, an exact interval-local mean-value inequality, and finite
slack-bisection density. Exact restricted sine/cosine inverses are now
constructed by deterministic iteration with an explicit rational inverse
modulus; exponential inverse existence is also complete.

- The real carrier is the sequential completion of the ordinary rational
  premetric.  It is denoted `ℝ` and rationals enter through `rat`.
- Generic theorems remain generic.  In particular, extensionality for maps out
  of a sequential completion belongs under `Cubical.Analysis.Completion`, not
  in a rational-only module.
- Arithmetic is defined by lifting rational arithmetic.  The comparison with
  `Completion.Base` may be used to transfer an already generic theorem (for
  example density/extensionality), but not as a hidden definition of an
  arithmetic operation.
- Primitive lifted definitions retain visible computation on `rat` and use
  limit uniqueness for `lim` equations.  Witness-eliminating derived
  operations may be opaque when their public computation and law theorems are
  already exposed; this prevents proof witnesses from becoming a reduction
  interface.
- Non-expanding lifting is preferred whenever the base operation admits it.
  Ordinary addition is separately non-expanding, but its uncurried product map
  is only Lipschitz with constant two.  This distinction is represented in the
  API instead of weakening every operation to continuity.
- Multiplication is the important exception: it is not globally uniformly
  continuous, so its definition uses completion-centred continuity on the
  rational product and then curries through the completion/product map.

## Inventory and lessons

### Existing completion machinery

- `Sequential.Base` presents the completion with rationally indexed closeness,
  an injection, and limits of ordinary sequences carrying merely a Cauchy
  witness.
- `Sequential.Properties` proves density, roundedness, constructs the
  premetric structure, and identifies the `lim` constructor as a sequential
  limit.
- `Sequential.Lift.CauchyContinuous` gives the central universal property:
  base maps satisfying the graph-Cauchy condition extend canonically, preserve
  Cauchy sequences, compute definitionally on the base injection, and satisfy
  uniqueness/extensionality.  It also packages restriction and extension as an
  isomorphism of sigma types.
- `Sequential.Lift.UniformlyContinuous` turns ordinary uniform continuity into
  the graph-Cauchy condition and proves that the lifted map remains uniformly
  continuous.
- `Sequential.Lift.CompletionCentered` handles genuinely non-uniform maps.  A
  local modulus centred at every completion point is enough to construct a
  Cauchy-continuous extension, and the extension is continuous.
- `Sequential.Product` proves that completion commutes with binary products.
  This is the correct route for rational functions of several variables.
- `Sequential.Comparison.Regular` is an isometric isomorphism with
  `Completion.Base`, computing to the same base point in both directions.

### What transfers well from `CauchyRealsP`

- Dense extensionality is the main reusable proof pattern.  Algebraic laws can
  be reduced to rational laws once both sides have suitable continuity.
- Rational computation lemmas should be part of every lifted operation's
  public API.
- Bundled algebraic structures should be constructed only after the primitive
  operations and their quantitative behavior are available.

### What should not be copied

- Constructor-by-constructor definitions of uniformly continuous operations:
  the generic lift already provides them.
- Bound-selection machinery for multiplication when completion-centred
  continuity can lift the whole rational product map directly.
- Specialized copies of generic lifting or extensionality lemmas.

### New generic completion layer

- `Completion.Extensionality` transfers dense continuous extensionality once,
  generically, across the isometric comparison with `Completion.Base`.  It
  includes unary and iterated binary/ternary forms.
- `Completion.NonExpanding` constructs the sequential lift using the recent
  uniformly-continuous/Cauchy-continuous machinery, then proves the exact
  non-expanding estimate by comparison with the regular generic lift.  It
  computes on the base injection and has lift-specific extensionality.
- `Completion.BinaryNonExpanding` does the same for separately non-expanding
  binary operations.  The underlying function comes from lifting the product
  map with the half-radius modulus; only the quantitative proof is sharpened by
  comparison with the regular completion.
- `Completion.Limit` proves generic `map-lim` rules.  Non-expanding maps build
  their image Cauchy witness directly.
- `Completion.BinaryLimit` proves that a separately non-expanding binary map is
  jointly Lipschitz with constant two and therefore commutes with synchronized
  sequential limits, including construction of the image witness.
- `Completion.Completeness` proves generically that the sequence-backed
  completion is complete, using the non-expanding isometric retract to the
  already complete regular presentation.
- `Completion.Lipschitz` extends a base map at one fixed positive rational
  Lipschitz constant and proves that the exact constant survives completion.
  It is the quantitative engine for bounded reciprocal.

### Real-number layer now available

- `Real.Base` exposes `ℝ`, `rat`, closeness, sequence witnesses and limits,
  density, sethood, and injectivity of `rat`.
- `Real.UniversalProperty` exposes continuous extensionality and the existing
  Cauchy-continuous restriction/extension isomorphism.
- Negation, addition, absolute value, maximum, and minimum use non-expanding
  lifts (or composites of them).  Their rational computation and exact
  one-variable non-expansion laws are public.
- Multiplication uses the completion-centred lift of rational multiplication on
  `ℚ × ℚ`; its product and curried forms compute on rationals and preserve
  synchronized limits.
- Dense extensionality proves the additive-group, multiplication, lattice, and
  absolute-value laws.  The resulting reals are packaged as an `AbGroup` and a
  `CommRing` without importing either Cauchy-real implementation.
- The fixed points of absolute value form an explicitly closed nonnegative cone
  under addition and multiplication.  This predicate is equivalent to the
  order-theoretic statement `0 ≤ x` once the lifted-max order is introduced.
- `Real.Order` defines `x ≤ y` by `max x y = y`, packages a `Poset`, proves the
  exact rational-order equivalence, and proves addition preserves and reflects
  order.  Multiplication is monotone by a nonnegative factor.  Pointwise order
  is closed under sequential limits.
- `Real.Order.Strict` defines `x < y` by the mere existence of a positive
  rational gap `δ` with `x + δ ≤ y`.  It proves the exact rational-order
  equivalence, mixed and strict transitivity, weakening, irreflexivity,
  asymmetry, translation/cancellation laws, negation reversal, and the
  positive-difference characterization.  Rational density gives locatedness
  and weak linearity, so the relation is packaged both as a `Quoset` and as a
  `StrictOrder`.
- Closeness is equivalent to the strict order bound
  `abs (x - y) < rat ε`.  The difficult direction is proved directly from
  rational density and the non-expanding absolute-value lift.  It yields the
  arbitrarily-small-slack principle and the exact compatibility
  `x ≤ y ≃ ¬ (y < x)`.
- The symmetric closure of strict order is a cotransitive apartness relation.
  Its rational restriction, translation invariance, cancellation, and
  negation law are public, and it is packaged as the library's `Apartness`
  structure.
- The lifted `min` and `max` package the non-strict order as a
  `Pseudolattice`.  Together with the strict-order compatibility and the
  existing ring laws this gives a complete `ℝOrderedCommRing`; `rat` is
  packaged as an ordered-commutative-ring homomorphism.
- Positive real multiplication is now constructive at the gap level: positive
  rational lower bounds multiply to a positive rational lower bound.  This
  yields strict monotonicity of multiplication by a positive real.  The
  subtype `ℝ>0`, its rational embedding, and its addition/multiplication
  operations expose the positive cone independently of a still-pending total
  strict-order bundle.
- `Real.Metric.Distance` defines `|x - y|`; it is separately non-expanding,
  symmetric, continuous, and computes on rational points.
- `Real.Sequence` gives canonical witness-producing limit rules for negation,
  absolute value, addition, distance, maximum, and minimum.  Multiplication's
  rule retains an explicit image witness because it is not globally
  non-expanding.
- Closed intervals and closed absolute-radius balls are now inherited
  premetric subspaces with non-expanding inclusions and clamp retractions.
  Both are complete by generic retract completeness; the unit interval is
  exposed as a specialization.  Open lower/upper half-lines, intervals, and
  absolute-radius balls are inherited subspaces with checked openness
  witnesses.
- `Real.Functions.Powers` illustrates compositional analysis: powers and square
  are continuous because multiplication takes continuous pairs to a continuous
  product; no new completion recursion is needed.
- Every real lies merely in a rational interval of any requested positive
  radius.  Widening it gives strict rational bounds, and the rational floor
  theory upgrades these to strict natural upper, lower, absolute, and
  two-sided bounds.
- Reciprocal is constructed in layers: a globally Lipschitz rational
  reciprocal clamped away from zero, compatibility between bounds, elimination
  of a positive-gap witness, and finally the signed apartness split.  The API
  includes rational computation, positivity, two-sided laws, involution,
  product/negation laws, division, cancellation, and multiplicative-apartness
  reflection.
- Natural-number embedding, a rational module action, rational affine maps,
  Horner polynomial evaluation, and finite sums are available.  The scalar
  lift retains its exact positive Lipschitz bound and agrees with
  multiplication by an embedded rational.  Polynomials have nonnegative
  majorants, absolute evaluation bounds, and derivative-ready closed-ball
  Lipschitz estimates.  Finite sums preserve native sequence witnesses and
  ordinary limits and expose monotonicity and an absolute-value bound.
- `Real.Sequence` now distinguishes native `SeqWitness` data from ordinary
  convergence, packages unique sequence limits, and proves constant, shift,
  unary, additive, multiplicative, and subtractive limit preservation.  Its
  choice-free tail layer covers eventual equality, eventual non-strict/strict
  order, and radiuswise asymptotic closeness, including transport of limits.
  A stronger merely selected asymptotic modulus preserves and reflects native
  witnesses, and constructive pointwise/eventual squeeze theorems are public.
- `Real.Series` provides partial sums, summability, additive and scalar closure,
  proof-independent sums, and the necessary theorem that terms of a summable
  series tend to zero.  Tail dropping and finite modification preserve and
  reflect summability with exact correction formulas.  Partial-sum distance
  bounds support dominated native Cauchy series, absolute-Cauchy convergence,
  and the standard absolute bound on the resulting sum.
- Finite sums additionally expose extension, splitting, addition, negation,
  subtraction, scalar and multiplicative distribution, exchange, telescoping,
  reversal, anti-diagonal sums, and triangular reindexing.  Series expose
  monotonicity and arbitrary summable-majorant bounds.
- Geometric series have a division-free finite identity and an explicit
  block/binary decay modulus for every rational `|q| < 1`, yielding native
  Cauchy witnesses, summability, and the reciprocal sum formula.  A real ratio
  dominated by such a rational contraction inherits the same conclusions and
  reciprocal value.  Uniform series distinguish a selected point-independent
  modulus from its propositionally truncated interface.  Uniform convergence
  of continuous partial sums gives a continuous canonical sum.  A single
  geometric majorant therefore proves bounded-coefficient power-series
  convergence and continuity uniformly across every closed positive rational
  radius strictly below one.  More generally, coefficients satisfying
  `|a n| ≤ B G^n` converge absolutely and uniformly on every closed rational
  radius `R` with `G R < 1`; the corresponding canonical value is continuous
  and has the geometric-majorant absolute bound.  These growth certificates
  are closed under addition, subtraction, negation, and explicitly bounded
  real scaling.  Evaluation at zero is unconditionally summable with value
  equal to the constant coefficient.  Eventual coefficient equality transports
  Cauchy and summability witnesses, and explicit cutoffs give exact finite
  corrections to power-series values.  Zero-padded finite coefficient lists
  have the explicit Cauchy modulus `length coefficients` and evaluate exactly
  as Horner polynomials.  The same cutoff is a point-independent closed-radius
  uniform modulus; weighted tail coefficients identify the canonical formal
  derivative series with the Horner derivative, and the direct Horner source
  has that canonical derivative along every closed radius.  Coefficient
  rescaling by `c^n` transports Cauchy,
  absolute-Cauchy, summability, sums, and values along `x ↦ c x`.  The
  coefficient-level operations API also carries explicit absolute bounds and
  proof-independent values through negation and subtraction, in addition to
  its additive and scaling laws.  The constant-one coefficient series is
  identified with the quantitative geometric series, so every explicit
  rational contraction bound yields its Cauchy witness, summability, `HasSum`,
  and proof-independent positive-reciprocal value.  Its self-convolution has
  the exact coefficients `n + 1` and the squared reciprocal value, using the
  native Mertens path.
- Cauchy products expose bilinearity, commutativity, unit laws, triangular and
  rectangular partial-sum identities, an explicit remainder and its absolute
  majorant.  The quantitative Mertens theorem proves convergence and sum
  multiplication from native absolute/Cauchy witnesses plus explicit uniform
  partial-sum bounds, without asserting a choice-producing converse from mere
  summability.  Native Cauchy witnesses now construct merely existing rational
  partial-sum bounds; eliminating those only into propositions gives
  bound-free remainder, `HasSum`, summability, and product-value theorems.
  Cauchy multiplication of coefficient sequences evaluates exactly to the
  Cauchy product of the corresponding power-series terms, with both
  explicit-bound and native-Cauchy convergence wrappers.  Formal
  differentiation satisfies the exact coefficient-level Leibniz rule for
  Cauchy products independently of convergence assumptions.  Selected
  absolute-Cauchy witnesses are now closed under Cauchy products by an
  explicit rectangular-product/remainder modulus; the native theorem opens
  merely existing rational bounds only into its proposition-valued result.
- The first differential-calculus kernel uses a division-free first-order
  remainder.  It supports general premetric parameter spaces, continuous
  reparameterization, and continuous difference-factor proofs; constants and
  identity are differentiable, and derivative values and functions are unique
  without a choice principle.  Addition, negation, subtraction, arbitrary
  real scaling, rational scaling, multiplication, composition, natural powers,
  Horner polynomials, and finite sums preserve derivatives.  Differentiable
  maps are continuous, and open-predicate subspaces support restriction and
  pointwise ambient derivative adapters.  An indexed chain theorem also
  composes two derivatives living on the same parameter space.  Reciprocal
  derivatives are checked on explicit positive and negative rationally bounded
  domains, with transfer to proof-independent inverse values; arbitrary
  differentiable numerators and denominators have a quotient rule whenever a
  uniform positive rational bound separates the denominator from zero on
  either side.
- Formal power-series differentiation is available at the coefficient and
  term levels: it respects addition and scaling, computes on rational
  coefficients, and identifies every successor power term with its derivative
  term.  Iterated formal differentiation has zero/successor, composition,
  addition, scaling, and zero laws together with the closed coefficient
  formula `D^k a n = ((n+1)⋯(n+k)) · a (n+k)`.  Generic coefficient majorants
  are preserved by formal differentiation.  The finite divided-difference
  factor now has its power factorization, diagonal formal-derivative identity,
  continuity, closed-radius bound, and derivative-majorant domination.  The remaining
  family is uniformly Cauchy on a closed radius whenever the corresponding
  derivative-majorant series is native Cauchy, including by restriction from a
  larger radius.  The canonical factor sum now factors two power-series values
  and equals the formal-derivative value on the diagonal.  Its uniform-limit
  continuity feeds directly into the division-free kernel, proving that the
  canonical uniform sum has the canonical formal-derivative sum as its
  derivative along any closed absolute-radius domain.  A generic
  closed-radius-to-open-interior adapter now transfers that relative
  derivative to every explicitly agreeing ambient extension.  The
  power-series specialization also moves derivative-majorant convergence from
  an outer radius to an inner one and retains the derived uniform witness for
  reuse.  A radiuswise entire-series interface selects the concrete radius
  `|x| + 1`, gives a proof-independent global value, proves agreement with
  every closed-radius uniform value, and returns the local derivative together
  with its equality to the global formal-derivative value.  Radiuswise evidence
  for all repeated formal derivatives and divided-difference factors lifts this
  to every higher derivative, again pairing canonical-value equality with the
  local derivative proof instead of transporting one through the other.
- Iterated geometric coefficients are defined structurally by repeated Cauchy
  products.  Their checked algebra includes simplex and binomial closed forms,
  nonnegativity, a polynomial majorant, and
  `D I_k = (k + 1) I_(k+1)`.  A structural native-Mertens layer gives the
  successor sum law.  The selected absolute-product theorem constructs the
  required all-order family directly from a rational contraction bound, giving
  unconditional absolute/Cauchy convergence, summability, `HasSum`, and
  proof-independent reciprocal-power values at every finite order.  The
  exponential coefficient sequence is built from exact positive-rational
  factorial reciprocals; its formal derivative and every repeated formal
  derivative equal the original sequence without introducing a proof-indexed
  real inverse.  The explicit estimate
  `1/n! ≤ 2·(1/2)^n` already gives absolute, ordinary, and uniform convergence
  on every closed positive rational radius below two.  The parameterized bound
  `1/n! ≤ B^B·(1/B)^n` is now checked as well, yielding the same convergence
  APIs on every explicit rational radius below a supplied positive natural
  `B`.  Archimedean restriction now turns this into uniform convergence on
  every real closed radius.  The divided-difference factors and all repeated
  formal derivatives inherit the same entire package, giving a global
  exponential value whose every finite derivative is again that value,
  paired with the canonical local derivative evidence.
- Sine and cosine now have exact rational factorial coefficient sequences.
  Their absolute coefficients are majorized by the exponential sequence, so
  both series, their formal derivatives, and their divided-difference factors
  converge uniformly on every real closed radius.  Formal differentiation
  gives `D sin = cos`, `D cos = -sin`, and four-step coefficient cycles.  The
  global values `sinℝ` and `cosℝ` have the expected values at zero, global
  derivatives, continuity, odd/even identities, and second-order equations
  `sinℝ'' = -sinℝ` and `cosℝ'' = -cosℝ`.  Every finite formal derivative
  also has entire uniform and divided-difference convergence evidence.  Their
  absolute values are bounded by the global exponential at `|x|`.  Exact
  coefficient Cauchy products and native Mertens convergence prove the
  Pythagorean identity `sinℝ x · sinℝ x + cosℝ x · cosℝ x = 1`.  Solver-free
  sign algebra, divided-power/binomial identities, finite anti-diagonal
  reindexing, and native Mertens products also give the total sine and cosine
  addition formulas and their sine/cosine double-angle corollaries.  Located
  order and strict multiplication reflect the
  component square bounds to the sharp global estimates `|sinℝ x| ≤ 1` and
  `|cosℝ x| ≤ 1`.  Tangent and secant are now defined on the constructive
  subspace carrying evidence that cosine is apart from zero.  Their values are
  proof-irrelevant, respect negation with the expected odd/even laws, have the
  expected values at zero, and satisfy `tanℝ = sinℝ · secℝ`,
  `1 + tanℝ² = secℝ²`, and `secℝ² - tanℝ² = 1`.
  A pair whose sum also has cosine apart from zero now has a derived gap
  for `1 - tanℝ x · tanℝ y`; on this exact domain the cleared and
  quotient tangent and secant addition laws are available.  Conversely, an
  apart tangent denominator constructs the sum-domain point, yielding the
  tangent double-angle specialization under the sharp local denominator
  condition.
- `Real.Series.PowerSeries.Trigonometric.Pi` now states the constructive
  characterization of half-pi as the first positive cosine zero, proves that
  it implies the least nonnegative cosine-zero property, and proves
  uniqueness; the sigma type of characterized values is itself a proposition.
  The Bishop iteration from the HIT Cauchy-real development and the preferred
  damped half-step variant are identified with partial sums of their
  increments.  The damped iteration now has a constructed native Cauchy witness;
  the historical undamped route retains its conditional interface. Every
  resulting limit is proved to be a cosine zero.  Four-term power-series
  blocks establish `1 - x²/2 ≤ cos x`, hence `1/2 ≤ cos x` and strict
  cosine positivity on `[0,1]`.  Cosine zero implies sine-square one, while
  sine positivity selects the positive sign.  The resulting generic
  quarter-turn layer proves phase shifts, the values and shifts at a
  half-turn, and full-turn periodicity. The damped construction now
  supplies an unconditional characterized pi value for these laws. Sine is
  packaged as a continuous map from the
  closed symmetric quarter interval to `[-1,1]`; both intervals are complete
  and the endpoint values are checked.  The midpoint/half-difference identity
  `sin y - sin x = 2 cos((x+y)/2) sin((y-x)/2)`, symmetric cosine positivity,
  and positivity of the half-difference sine now prove strict increase on the
  whole quarter interval.  Consequently the restricted map is injective and
  an embedding without taking monotonicity as an extra hypothesis.
  Quantitative factor bounds now give an ordered sine-separation modulus and
  a converse metric modulus: sufficiently close sine values force the source
  points to be close.  A propositionally truncated intermediate-value
  statement is equivalent to surjectivity.  It is also equivalent to a new
  completion-compatible approximate formulation consisting of interval
  points with one native Cauchy witness whose sine values converge to the
  target.  Completeness, preservation of interval bounds, continuity of sine,
  and uniqueness of limits turn such an approximation into an exact
  preimage; this approximate statement now feeds the requested equivalence
  directly.  A second, Bishop-style route now reduces the same result to a
  rational-target construction.  `RationalSineInverseConstruction` asks for
  a map from rationals to quarter-interval points satisfying the exact
  clamped sine equation.  A chosen closeness-reflection modulus proves this
  rational graph Cauchy-continuous; sequential completion then extends it to
  all real targets, preserves its interval range, and proves
  `sin (G y) = clamp y`.  The bundled and merely bundled modulus variants feed
  the restricted-sine equivalence directly when that modulus is supplied.
  `SineQuarterApproximateImageDensity` asks only for a merely existing
  approximate preimage at each target and tolerance. Finite slack-bisection
  now proves this density, but it does not choose a coherent sequence or a
  bundled inverse modulus. The former countable-choice adapters were removed.
  Deterministic iteration now supplies native Cauchy data for exact inverse
  existence. Rational approximation-family adapters
  remain available when their actual Cauchy data are supplied; image-only
  convergence is not silently promoted to such data.
  Global uniform derivative estimates now follow from the addition formulas
  and the derivatives at zero. The uniform FTC gives the damped residual
  contraction `7/8` after the first step. Geometrically bounded increments
  supply the native Cauchy witness, and positivity on all finite prefixes
  proves the full first-zero characterization of the limit. `Pi.Value`
  exports unconditional `halfPiℝ`, `piℝ`, `twoPiℝ`, uniqueness, the least-zero
  properties, positivity of sine on `(0,piℝ)`, special values, phase shifts,
  and both `2π` periodicity laws.
- Exact restricted sine/cosine inverses are now constructed without choice.
  `Functions/Inverse/Iteration` proves the invariant and weighted residual
  estimate for `x(n+1)=x(n)+target-f(x(n))`. Sine's non-expanding bound makes
  this apply on `[-halfPiℝ,halfPiℝ]`. The small-angle bound `sin t >= t/2`
  supplies an explicit rational sine-closeness reflection modulus, hence a
  native Cauchy witness for the iterates. Existing completeness and inverse
  lemmas then give `sinℝ-restrictedEquiv`, `cosℝ-restrictedEquiv`, `arcSinℝ`,
  and `arcCosℝ`. Both inverse laws, endpoint and zero values, parity,
  continuity with an explicit uniform modulus, and weak/strict order laws
  are public through `Pi` and `Trigonometric`. General exact IVT and the
  Cartesian-circle bridge remain separate.
- The real trigonometric identity audit against HIT Cauchy reals is recorded
  in `Real/Series/PowerSeries/Trigonometric/README.md`. Existing parity,
  addition, Pythagorean, double-angle, tangent/secant, and sine-difference
  proofs are reused. `Identities.Products` adds the four product-to-sum
  formulas and the remaining sum/difference factorizations;
  `Identities.Squares` adds complementary squares, coefficient/power forms
  of double angles, power reduction, and squared half-angle formulas.
  `Pi.Reflection` adds negative shifts and cofunction/reflection identities;
  `Pi.IntegerPeriod` adds all integer periods and the turn-coordinate
  invariance used by the HIT circle. The global unit derivative bounds give
  sine/cosine difference bounds with constant one, native non-expanding maps,
  and `|sin x| ≤ |x|` in `Estimates.NonExpanding`. Native FTC constructs
  both definite trig integrals in `Integrals`, without separate integrability
  or chosen-modulus hypotheses. The public trigonometric facade exports these
  results together with the existing subtraction/displacement formulas.
- `Real.Integration` now exposes finite and tagged partitions, endpoint and
  monotonicity data, widths and telescoping total width, left/right sampling,
  mesh predicates, and quantitative resampling bounds.  Equal and dyadic
  partitions have exact widths and checked vanishing mesh.  Riemann sums have
  congruence, constant, additive, negative, subtractive, and arbitrary-real
  scaling laws.  Binary recursive dyadic sums expose midpoint-width and
  algebraic laws plus an oscillation-controlled refinement estimate.  A
  Riemann integral is defined by convergence over every sufficiently fine
  tagged partition; its value is unique, integrability is proposition-valued,
  and constants, addition, negation, subtraction, and scaling preserve
  integrability with exact value laws. Concatenation preserves fine meshes
  and adds Riemann sums, proving additivity for three existing integrals on
  adjacent ordered intervals. A radiuswise uniform derivative on an interval
  is now integrable with value `F b - F a`, without a separate continuity or
  integrability assumption on the derivative. Conversely, integral increments
  differentiate to the integrand: pointwise continuity on the closed interval
  gives a relative derivative, and radiuswise uniform continuity gives a
  uniform derivative. The actual accumulation function `x ↦ ∫[a,x] f` has both
  variants when integrability on ordered subintervals is supplied. Its value
  also equals `F x - F a` for any radiuswise uniform antiderivative `F`.
  Overlap lengths now compare arbitrary tagged partitions without deciding
  the order of their endpoints. Radiuswise uniform continuity gives the
  Riemann Cauchy condition; standard uniform continuity (mere existence of
  one modulus) gives integrability. An explicit dyadic mesh modulus constructs
  the native sequence witness, and comparison identifies its limit with the
  semantic integral. `UniformlyContinuousAccumulation` therefore constructs
  the subinterval integrals and proves both derivative variants directly.
  Integrability from only radiuswise uniform continuity remains open.
  The next layer now includes interval-local equality and order laws,
  quantitative difference estimates, uniform-limit integral convergence and
  existence from a supplied uniform convergence modulus, and termwise
  integration of uniformly Cauchy series. `IntervalIntegral.between` handles
  either endpoint order inside a fixed ambient interval, with reversal,
  additivity, signed endpoint derivatives, and Lipschitz primitives for
  bounded integrands. FTC gives monotonicity, derivative-bound increment
  estimates, constant differences of antiderivatives, and uniqueness with
  initial values. Bounded uniform derivatives support checked uniform product
  and chain rules, integration by parts, and substitution. The latter can
  construct its primitive from standard uniform continuity of the integrand.

## Work log

- [x] Surveyed the sequential completion, all three lifting interfaces, product
  comparison, and the foundational/additive parts of `CauchyRealsP`.
- [x] Selected a hierarchy separating generic completion principles from the
  rational real-number development.
- [x] Added generic sequential-completion extensionality, non-expanding lifts,
  synchronized limit rules, and completeness.
- [x] Added the sequential-real foundation and universal-property facade.
- [x] Defined negation and addition by lifting rational maps; exposed rational
  computation and continuity laws.
- [x] Defined multiplication as a lifted map from the rational product and curried
  it through the completion/product isomorphism.
- [x] Established algebraic laws by dense extensionality and packaged additive
  group and commutative-ring structures.
- [x] Added lifted absolute value, lattice operations, distance, powers, a
  partial order, monotonicity laws, completeness, and sequence-facing results.
- [x] Develop the positive-gap strict order, its rational characterization,
  additive laws, and multiplicative positivity/strict monotonicity.
- [x] Prove locatedness/cotransitivity, the metric/strict-order
  characterization, and package apartness and the standard ordered-ring
  interfaces.
- [x] Add inverses away from zero, natural embeddings, polynomial evaluation,
  and finite sums using quantitative lifts and finite recursion.
- [x] Establish the sequence/series baseline: ordinary limit combinators,
  partial sums, linear operations, and the summable-term test.
- [x] Add rational scalar/affine maps, polynomial majorants and local estimates,
  choice-free eventual sequence relations, finite-sum bounds, series tails,
  finite modifications, and native-witness absolute convergence comparison.
- [x] Add finite-sum algebra, selected asymptotic witnesses and squeeze,
  complete closed domains, rational half-contraction geometric series, series
  comparison, and the first bounded-coefficient power-series convergence
  layer.
- [x] Add signed half-contraction geometric series, point-independent uniform
  series moduli, uniform closed-radius power-series convergence, open
  intervals, and the definition/basic/uniqueness derivative kernel.
- [x] Add open absolute-radius domains, uniform-limit continuity and continuous
  closed-radius power-series values, derivative linear algebra and continuity,
  open-subspace derivative adapters, and arbitrary strict-rational geometric
  convergence.
- [x] Add real geometric convergence under rational contraction bounds,
  strict-interior rational-radius power-series convergence and continuity,
  product and chain rules, and convolution-oriented finite-sum reindexing.
- [x] Add natural-power, Horner-polynomial, and finite-sum derivative rules,
  controlled positive/negative reciprocal and quotient rules, finite
  Cauchy-product algebra, explicit remainder bounds, and a quantitative
  Mertens convergence theorem.
- [x] Add indexed derivative composition, arbitrary-denominator quotients on
  uniformly positive/negative domains, constructive native bounds and
  bound-free Mertens theorems, exponential coefficient-growth convergence and
  closure laws, exact zero/finite-modification formulas, power-series products,
  finite-polynomial, rescaling, and geometric bridges, generic majorants,
  repeated formal derivatives, summed uniform divided differences, and
  closed-radius/strict-interior termwise differentiation.
- [x] Add uniform Horner-polynomial calculus, radiuswise entire values and
  higher derivatives, selected absolute-Cauchy product closure, unconditional
  iterated-geometric reciprocal powers, and factorial-majorized exponential
  convergence on arbitrary explicitly natural-bounded rational radii.
- [x] Add the integration foundation: finite/tagged and equal/dyadic
  partitions, vanishing mesh, Riemann-sum algebra and resampling bounds, the
  unique mesh-limit integral, its constant/additive/negative/subtractive/
  scaling laws, and recursive dyadic refinement bounds.
- [x] Prove both FTC directions under explicit constructive hypotheses:
  uniform derivatives integrate to endpoint differences; continuous integrands
  differentiate their accumulation functions given subinterval integrability.
  Add interval-local integral bounds, partition concatenation, integral
  additivity, and the equivalence between uniform derivatives and integral
  increments for radiuswise uniformly continuous integrands.
- [x] Prove integrability from standard uniform continuity on a closed
  interval, using overlap-weighted partition comparisons and an explicit
  dyadic mesh modulus. Construct the accumulation function and its derivative
  without a separate subinterval-integrability hypothesis.
- [x] Expand integral comparison, interval-local equality, zero-length
  integrals, oriented endpoint laws, and Lipschitz accumulation estimates.
- [x] Prove uniform-limit integral convergence, construct limit integrals from
  a supplied uniform convergence modulus, and integrate uniformly Cauchy
  series term by term.
- [x] Derive FTC monotonicity and antiderivative uniqueness; add bounded uniform
  product/chain rules, integration by parts, and substitution, including
  construction of the substitution primitive from uniform continuity.
- [x] Prove boundedness from radiuswise uniform continuity on an ordered
  closed interval; obtain substitution bounds and Lipschitz integral functions
  automatically.
- [x] Prove uniform convergence of indefinite integrals, stability of uniform
  derivatives under limits, and construction from convergence at one endpoint.
  Add termwise differentiation of series, without requiring a separate
  continuity proof for the limiting derivative.
- [x] Add the first trigonometric tranche: exact sine/cosine coefficients,
  entire convergence, formal derivative cycles, global values and
  derivatives, continuity, odd/even laws, exponential absolute bounds, and
  entire higher-derivative convergence with second-derivative equations, plus
  the Pythagorean/addition/double-angle identities and sharp global bounds by
  one, plus partial tangent/secant values and their basic parity,
  cancellation, zero, and Pythagorean laws, constructive tangent/secant
  addition formulas, and the tangent double-angle specialization.
- [x] Add the constructive pi foundation: first-positive-cosine-zero and least
  nonnegative-zero characterizations with uniqueness, Bishop's recursive
  approximation and partial-sum equation, the explicit Cauchy/limit boundary,
  and the conditional theorem that every limit candidate is a cosine zero.
- [x] Add the damped Bishop recurrence and conditional cosine-zero limit
  theorem, prove the quadratic and half-unit cosine lower bounds on `[0,1]`,
  and derive conditional quarter-turn, half-turn, and periodicity laws from a
  characterized half-pi.
- [x] Package sine on the closed symmetric quarter interval, prove its
  continuity, endpoint values, and interval completeness, reduce injectivity
  to strict increase and surjectivity exactly to a truncated intermediate-
  value statement, and check the symmetric-cosine and midpoint geometry used
  by the constructive strict-monotonicity proof.
- [x] Prove the product-to-sum difference identity, positivity of both factors,
  strict monotonicity of sine on the closed quarter interval, and hence
  injectivity and embedding of the restricted map.
- [x] Prove `SineQuarterApproximateImageDensity` by finite located bisection
  with slack comparisons, without a choice assumption.
- [x] Construct coherent inverse approximations with native Cauchy data,
  exact restricted sine/cosine equivalences, and named closed-domain inverses
  with explicit uniform moduli; retain finite density as a separate result.
- [x] Prove uniform sine/cosine derivative estimates and the signed endpoint
  bounds needed for damped Bishop contraction; construct the native Cauchy
  witness, positivity before the limit, and unconditional `halfPiℝ`/`piℝ`
  with first-zero characterizations, special values, and periodicity.
- [x] Match the real sine/cosine equations in HIT `Trigonometry.Identities`,
  extend them with product/sum, power-reduction, squared half-angle, reflection,
  and integer-period formulas, and prove the sharp difference bounds and
  definite sine/cosine integrals through native Analysis calculus.
- [ ] Extend integrability to the weaker radiuswise uniform continuity or
  uniform convergence hypotheses without selecting a modulus; then generalize geometric and power-series
  convergence, extend domain-local continuity and calculus algebra, and add
  integration closure laws and elementary functions in the phases recorded in
  `SCOPE_ROADMAP.md`.

## Computational behavior

- Unary and separately non-expanding binary lifts compute on `ι` through the
  sequential lift's base computation equation.
- `rat p + rat q`, `rat p · rat q`, `max (rat p) (rat q)`, and the analogous
  operations all have checked public computation lemmas.
- Unary/binary `lim` rules are stated by uniqueness of sequential limits.  For
  non-expanding maps the target witness is constructed canonically from the
  source witnesses; multiplication exposes why a more general lift needs an
  explicit image witness.
- The comparison with `Completion.Base` is used for generic theorems and exact
  quantitative proofs, never as the hidden definition of a real operation.

## Performance observations

- A single module instantiating four fully generic non-expanding completion
  lifts exhausted the checker.  Lift extensionality therefore lives beside one
  lift instance; future identity/composition laws should use a lighter abstract
  interface rather than multiply instantiating the implementation.
- Bundling the nonnegative subtype as a `CommSemiring` forced the complete real
  `CommRing` proof through every subtype law and also exhausted the checker.
  The cone and its closed operations are retained; the redundant bundle is not.
- Unrestricted public opens in aggregate facades caused an accidental scope
  explosion.  Curating their exported names reduced `Algebra.Lattice` from
  roughly 36 seconds to 4 seconds and `Algebra` from more than 15 minutes to
  under 5 seconds; the top-level `Real` and `Analysis` facades then checked in
  roughly 8.5 and 7.3 seconds respectively.
- A dependent no-eta record whose field mentioned completed-real addition and
  order made the positivity checker expand the entire lifting implementation
  (over 9 GB without finishing).  The mathematically identical dependent-pair
  representation of a positive gap avoids that checker pathology.  Splitting
  strict order into base, rational, additive, and multiplicative modules keeps
  each focused check around 4--6 seconds.
- Leaving an endpoint as an unconstrained `refl` inside a transported strict
  inequality made Agda unfold the implementations of lifted `max` and
  addition and left several enormous constraints.  Replacing it with the
  one-sided `subst` whose endpoint was explicit removed all metas and restored
  a sub-five-second check.  Proof transports around lifted operations should
  identify their changing endpoint explicitly.
- The first open-interval proof inherited `width gap`, whose hidden real
  endpoints were harmless mathematically but disastrous for elaboration:
  checking reached roughly 13.4 GB without finishing.  Projecting the sigma
  witness as `fst gap`, pinning both endpoints of order transports, and using
  small generic transport helpers reduced the complete module to about 2.8
  seconds.  In dependent quantitative proofs, apparently redundant explicit
  endpoints are an important performance boundary.
- No ring/order solver is used anywhere under `Cubical.Analysis`; rational and
  real laws are proved from named algebraic lemmas and dense extensionality.
- Proof-bearing records for partitions caused the checker to expand the real
  order implementation.  Nested dependent pairs retain the same data while
  keeping focused partition checks near the usual few-second range.  In the
  equal-partition proofs, explicitly typed endpoints and named rational-ring
  identities similarly avoid large unconstrained comparison metas.
- Moving the max-based absolute triangle proof into `Real.Order.AbsoluteValue`
  removed duplicate proof terms from both polynomial-bound modules and gives
  finite sums and series one shared ordered-ring estimate.
- A direct attempt to synthesize multiplication's diagonal `SeqWitness`
  through the product-completion comparison ran for more than two minutes and
  was removed.  This confirms that witness plumbing across a large comparison
  should first be factored into a lightweight generic combinator.  The public
  ordinary-limit theorem for multiplication remains fast because it uses
  continuity instead.
- An inline proof-dependent reciprocal inside the geometric `HasSum` statement
  caused more than two minutes of normalization.  Factoring the positive
  denominator proof and the proof-dependent sum into named definitions reduced
  the complete rational geometric check to roughly 4.2 seconds.
- A redundant proof that the geometric majorant is nonnegative, phrased through
  the fully general four-variable multiplication monotonicity theorem, also
  pushed a focused check past thirty seconds.  It was removed because all
  consumers need only the sharper termwise domination theorem, which checks in
  about four seconds.
- Composing an arbitrary negative denominator through the proof-indexed signed
  inverse again made completion-level normalization run past forty seconds.
  Pulling back the already checked uniformly upper-bounded negative reciprocal
  gives the same inverse law and reduced the complete quotient module to about
  four seconds.  Bounded reciprocal representations should remain visible
  through derivative composition and be erased only at the convenience API.
- A decidable `<` split for the finite-prefix/tail cases in the native Cauchy
  bound theorem ran past a minute.  Replacing it by structural natural-number
  `≤` case induction, with the prefix ending at `suc cutoff`, made the complete
  module check in about five seconds.
- The exact coefficient-product theorem expressed through proof-indexed
  `powerSeriesValue` ran past fifty-eight seconds.  Its underlying `HasSum`
  theorem and summability wrapper each check in about five seconds, so the slow
  convenience theorem was removed and the proof-independent sum equation is
  the exported boundary.

## Refactoring and verification

- `Real.Series.PowerSeries.Entire.entirePowerSeriesValuePresPath` identifies
  values of equal coefficient sequences with independently supplied convergence
  witnesses.  Exponential fixed-point and trigonometric derivative-periodicity
  proofs now use this common theorem.
- `Real.FiniteSum.Bounds` exposes pointwise and nonnegative-weighted absolute
  bounds.  Riemann resampling, integral bounds, and the uniform mean-value
  estimate reuse these finite-sum proofs.
- `Real.Integration.RiemannIntegral.Base.riemannSumsConverge` connects an
  integral to any tagged partition sequence with vanishing mesh.  Uniqueness
  and the integral absolute bound now use existing sequence-limit theorems.
  `Integration` exports the absolute bound, and subtraction has both a
  `HasRiemannIntegralOn` theorem and an integrability wrapper.
- The uniform derivative predicate explicitly quantifies over positive
  rational error radii.  Its partition proof reconstructs the difference from
  the remainder in the correct direction, using a small local estimate.
- Trigonometric subtraction states the argument as `x + (- y)`, definitionally
  equal to `x - y`, to match the addition theorem without unfolding entire
  series values.  Generic local algebra lemmas shorten the displacement
  expansions.
- Run `agda-codex Cubical/Analysis/Everything.agda` to check both the public
  facade and the additional mean-value and trigonometric estimate modules.
  New developments that are not reachable from `Real` should be imported by
  this check entry point.

## Open technical questions

- Which completion-centred maps admit automatically generated image witnesses
  for `lim` equations?  Multiplication currently exposes the witness explicitly.
- A categorical identity/composition API for non-expanding lifts is desirable,
  but it needs an abstraction that does not instantiate the heavy construction
  several times in one generic module.
- `SeqWitness` is a truncation of a globally chosen modulus, whereas
  `isLimitSequence` has radiuswise truncated tails.  A convergent sequence does
  not automatically regain a native witness. The series API therefore treats
  `Summable` as primary and exposes only the sound native-Cauchy-to-summable
  direction. The former choice-based converse adapters were removed. Future
  inverse constructions must prove a suitable native witness constructively;
  adding a choice assumption is not an acceptable shortcut.
- Multiplication's completion-centred construction knows enough to preserve
  suitable Cauchy graphs, but its cheapest reusable binary witness interface
  is not yet exposed.  This should be solved generically before polynomial or
  series clients request multiplication witnesses.
- Termwise power-series differentiation now uses a uniformly summed
  divided-difference factor in both the real and complex layers. The complex
  proof reuses real uniform sums and estimates; its diagonal identity is
  finite commutative-ring algebra. Strict-interior convergence and
  holomorphicity and all repeated derivatives now follow from the original
  outer-radius witness. General reexpansion convergence, representation and
  centered FTC applications are now completed in the later checkpoints above.

## Complex power-series differentiation and FTC (2026-10-10)

The [complex series layer](Complex/Series/README.md) now constructs a
uniformly summed, division-free monomial difference factor from one supplied
native derivative-majorant witness. Its diagonal is the series with
coefficients `(n+1) * a[n+1]`. Supplied sums have the corresponding complex
derivative along bounded continuous coordinates; canonical original and
derivative sums are available from the two radius majorants, and the
derivative is continuous. Radiuswise uniformly continuous coordinates give
uniform derivative estimates. No compactness/choice upgrade is used.

The [power-series line-integral theorem](Complex/Integration/LineIntegral/PowerSeries.agda)
constructs the endpoint integral and proves closed-path zero for certified
paths contained in that l1 radius, with original and derivative sums supplied
along the path. The derivative-majorant sum supplies the integrand bound.
At this checkpoint elementary-function identification with complex series,
repeated-derivative APIs, general C¹ upgrades and Cauchy theory remained.
The elementary-series continuation above now supplies the first of these.
The strict-interior continuation is recorded below.

Validation: all 16 changed Agda files and both Analysis entrypoints pass
`agda-codex` with exit code 0. The 355 audited source snapshots are current
and clean. All 841 native Analysis modules are reachable, with no forbidden
imports, missing modules or cycles; source, local-link and whitespace audits
also pass.


## Complex power-series interiors (2026-10-10)

The [interior convergence theorem](Complex/Series/PowerSeries/InteriorConvergence.agda)
constructs the native derivative-majorant witness at each specified `0 ≤ r < R`
from the original norm-majorant witness at `R`. The reusable real proof uses
finite divided-difference monotonicity and `(R-r)(n+1)r^n ≤ R^(n+1)`, followed
by rational scaling of the outer tail. Truncated gaps are eliminated only
into propositions; no convergence-to-native-witness converse is used.

[Open norm-radius domains](Complex/Domain/Radius.agda) and the generic
[open-subspace derivative adapter](Complex/Calculus/Derivative/OpenSubspace.agda)
support ambient complex differentiation. The
[holomorphicity theorem](Complex/Series/PowerSeries/Interior/Holomorphic.agda)
constructs both the derivative and its formal-series sum from original sum
representations on the open outer radius. Ambient extensions are supplied,
not manufactured. The [interior path FTC](Complex/Integration/LineIntegral/PowerSeries/Interior.agda)
now derives derivative convergence, uniform primitive estimates, the
integrand bound and integral existence from the original outer witness when
a certified path has a supplied smaller norm-radius bound.

Validation: all 15 changed Agda files (nine new modules and six facade
updates) and both Analysis entrypoints pass `agda-codex` with exit code 0.
All 365 audited snapshots are current and clean. All 850 Analysis modules
are reachable (1,251 Cubical modules transitively), with no missing imports,
orphans, cycles, forbidden imports, source flags or whitespace issues.
All 240 audited local documentation links resolve.
