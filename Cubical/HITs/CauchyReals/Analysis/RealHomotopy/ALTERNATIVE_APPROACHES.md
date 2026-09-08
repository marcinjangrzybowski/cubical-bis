# Repair attempts and alternative comparisons

2026-09-07. Three read-only agents investigated repairs, sphere-specific
alternatives, and algebraic cubical models after the face-composition test
in [DIRECTION_TESTS.md](DIRECTION_TESTS.md). The main thread checked the
analytic constructions and the contractible-carrier lemmas. No complete
replacement for the missing comparison has been established.

Follow-up: [CARRIER_WEAKENING.md](CARRIER_WEAKENING.md) records seven
new checked modules pursuing the selected-face direction below. They
establish the fixed-corner weakening invariant and pairwise anchor
independence. The unresolved part is coherent normalization across
varying selections, followed by the finite approximation comparisons.

## 1. Repair using contractible cubical carriers

The most concrete narrower candidate is to interpret finite cubical
approximations into the existing synthetic cubical boundary, rather than
construct a realization of every real singular cube. A source grid cell
is assigned a target face/carrier into which its entire boundary lifts.

The local ingredient is now checked in
[ContractibleCarriers.agda](Realization/ContractibleCarriers.agda). For
contractible `C`, every complete cubical boundary has a contractible
extension space, uniformly in dimension. This retains the boundary
agreement as part of the extension, so uniqueness includes that data.
It excludes the arbitrary higher-loop choices that obstructed the
unrestricted evaluator-plus-composition record.

There is a tempting but invalid simplification: treat carriers as
proposition-valued subtypes of the synthetic sphere. Then a map with
carrier membership would have only propositional extra data, and the
grid recursion could avoid new coherence fields. However, such carriers
cannot describe the desired synthetic faces/stars. The checked lemma
`contractible-subtype-loops` proves

```text
(∀a, isProp(P a)) → isContr(Σ A P) → P a → isContr(a = a).
```

A contractible subtype would thus force the ambient loop space at every
included point to be contractible. Actual synthetic cell maps `C → A`
need not be embeddings. A chosen lift into them carries more information
than a membership proposition.

### Checked actual carriers

[SelectedFaceCarriers.agda](Realization/SelectedFaceCarriers.agda) now
implements a restricted geometric construction uniformly in dimension.
For each coordinate choose either no face or one signed face. Replace
that coordinate's endpoint type by `Empty` or `Unit`, respectively, and
apply the same iterated pushout-product recursion as `CubeBoundary`.
This is the HIT (homotopy) union of the selected coordinate faces and
their intersections. At most one sign per coordinate ensures the
selected faces have a common corner.

For every nonempty selection, `carrier-contractible` is checked: the
pushout-product/join equivalence reduces it to a join containing a
contractible factor. `carrierBoundaryMap` gives an actual map to the
synthetic cubical boundary. On one family of faces it uses the selected
endpoint label; on the others it uses the previous carrier map. On an
intersection it uses the boundary's pushout path, preceded by the
previous commuting path in the disk. That latter disk is contractible,
so the required commuting path is available uniformly.

This first module constructs carrier types, their contractibility, and
maps into the boundary. The later `CarrierCorners`,
`PointedCarrierMaps`, and `CornerWeakening` modules construct coherent
transitions between carriers sharing one corner. Their invariant is
the contractible space of pointed maps over the pointed boundary.
Uniqueness of paths in the ambient disk is not used to infer uniqueness
of arbitrary homotopies in its noncontractible boundary.

### Weakening: the checked part and the remaining invariant

Use genuine face maps of `CubeBoundary (m+1)`, with their lift data. A
successor on source grid dimension needs a type of **complete carried
maps** and, for carrier inclusions, an operation

```text
weaken : CarriedMap n C → CarriedMap n D
```

that preserves the underlying ambient map and is compatible with
composition. `CarriedMaps` and `CornerCarriedMaps` now prove these
operations and laws for carriers sharing a fixed corner. Restriction to
an arbitrary domain map commutes with weakening, and supplied relative
extensions can be transported. All remaining source coordinates are
retained together.

A correction to the earlier proposed successor invariant is necessary:
the full carried-map space over a fixed ambient map need not be
contractible. Its fibers can retain the ambient loop space even when the
carrier itself is a point. Contractibility supplies extensions of
boundaries already valued in a carrier; it does not automatically supply
lifts of a prescribed sphere-valued extension.

`CarrierAnchors` and `AnchoredCarrierWeakening` additionally prove full
anchor independence for each fixed nested pair. A grid whose selections
vary still needs coherent normalization between these local pointed
presentations. The exact endpoint square and the obstruction to
deducing all higher coherence from an isolated triangle are recorded in
[CARRIER_WEAKENING.md](CARRIER_WEAKENING.md). Adding an assumed
normalization field would not solve this remaining problem.

### Domain grids have a simpler independent construction

A subdivided synthetic interval can be a finite graph HIT with `N+1`
vertices and consecutive edges, hence contractible. Its endpoint arrow
is equivalent to that of the ordinary synthetic interval. Relative
inverse/refinement coherence is controlled by contractible extension
spaces. Products and pushout products then give grid disks and boundaries
in arbitrary dimension. This proposed construction uses cubical grids,
not synthetic real-number coordinates or general finite-poset realization.
It does not supply the target-carrier interpreter.

## 2. A sphere-specific relative finite approximation bridge

A common finite description could consist of a cubical subdivision,
target face/carrier labels, and compatible incidence data. Interpret it
on both sides and prove **relative approximation** separately:

1. Every based real cube is, merely, real-homotopic to an interpretation
   of such finite data; prescribed finite endpoint cubes of homotopies
   must be retained after a common refinement.
2. Every based synthetic cube has the analogous finite representative,
   and synthetic homotopies with prescribed finite ends have finite
   representatives after common refinement.

For homotopy degree `k`, the statements in dimensions `k` and `k+1`
give surjectivity and injectivity of the common quotient comparison.
They avoid choosing canonical representatives globally. Concatenation
must be compatible with common refinement as well.

This is narrower than realizing arbitrary real singular objects, but
both its interpreter and its synthetic approximation theorem are
substantial. The existing [CW approximation](../../../../CW/Approximation.agda)
returns maps between synthetic skeleta (`finCellMap` is a
`FinSequenceMap`); it does not return finite grid labels. Likewise,
`approxSphereMap∙` in [CW spheres](../../../../CW/Instances/Sn.agda)
only factors through a target skeleton. Once that skeleton contains the
entire target sphere, the arbitrary synthetic map data remains.

On the real side, the checked uniform interpolation and operator lifts
are useful ingredients. Compatible target carrier assignment still
requires geometric work. One cannot assert that arbitrary intersections
of cubical vertex stars are contractible: on a square boundary, the closed
stars of opposite vertices intersect in two vertices. Nested carrier
assignments or a proved suitable subdivision cover are needed.

## 3. Algebraic cubical loop spaces and formal cubes

For a set-valued cubical diagram with faces, degeneracies, connections,
and horn filling, the following invariant admits ordinary internal
natural-number iteration:

```text
(Ω□ K)ᵣ = {σ : Kᵣ₊₁ | both first-coordinate faces are constant}.
```

Take components by quotienting vertices along edges. Group laws use
fixed two- and three-dimensional horn patterns in the iterated object.
This is the combinatorial method of Carranza–Kapulkin, §3. Their
comparison with topological groups uses geometric realization, so it
does not provide our internal synthetic bridge.
[Primary source](https://arxiv.org/pdf/2202.03511).

Chosen horn fillers form straightforward set-valued data. Merely existing
fillers might suffice after proving independence of the resulting group
class; elimination into a quotient set cannot simply assume that
independence. For real input, explicit positive collars are promising.
An exact ray-to-horn retraction can otherwise need a chosen maximizing
coordinate, which constructive real order does not automatically supply.

The obvious synthetic-side set-valued model fails:

```text
Kᵣ(A) = setTrunc(Cube r A).
```

[Cubes.Base.cubeEquiv](../../../../Foundations/Cubes/Base.agda) proves
`A ≃ Cube r A`. For a connected synthetic sphere every displayed set
truncation is therefore contractible. The proposed diagram loses the
sphere's homotopy. Keeping untruncated cubes retains higher types and
the higher-diagram problem.

A free Kan completion of a finite combinatorial sphere is another
possible model. Its missing theorem is soundness and completeness of
finite formal representatives and formal homotopies for the synthetic
sphere. Inductive syntax alone does not prove that every synthetic class
or equality has a formal representative. This remains a restricted
comparison problem, not an established bypass.

## 4. James construction as a sphere-specific alternative

The library's [James loop-suspension theorem](../../../James/LoopSuspEquiv.agda)
provides `Ω(Susp X) ≃∙ James X` for connected `X`. Its
[finite-stage connectivity theorem](../../../James/Inductive/PushoutFormula.agda)
can bound the word stage relevant to a requested homotopy degree.
This is a uniform synthetic result already available.

For coordinate spheres one could try decomposing real loop families into
finite words of equatorial data. The required comparison must preserve
parameter-dependent letters, deletion of basepoint letters, and relative
homotopies in finite word stages. An isomorphism of equator homotopy
groups alone does not supply this stronger information. Applying James
to the set carrier of the real equator would also use the wrong input.

The connected-input hypothesis leaves the real/synthetic circle as a
separate initial case. No real James family-comparison theorem was found.
This direction exchanges general realization for a finite-stage family
comparison, whose constructive proof is still missing.

## Current judgment

The analytic interpolation and loop-iteration route is productive and
checked. The algebraic cubical loop construction has a closed invariant
for its own set-valued theory. Neither currently proves the full goal.

The cubical-boundary carrier direction now has checked carrier shapes,
maps, coherent weakening at a common corner, and pairwise anchor
independence. It remains the most concrete narrower research target.
The next meaningful test is a normalization operation on complete
comparison frames when selections vary. Separate triangle comparisons
do not establish this invariant. Even a successful grid interpreter
would leave the relative synthetic finite approximation theorem explicit.
