# Cubical realization experiments, 2026-09-07

## Assessment

**Planning revision:** [SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md)
requires an all-dimensional constructive realization argument before
further implementation. The degree-two result below does not establish
that argument. The former plan to keep solving successive overlaps is
withdrawn; direct latching may later be a backend of a general theorem.

The investigation first pursued **finite cubical latching attachments**:
glue the degenerate cubes along their actual overlaps, and attach all
cube interiors relative to that glued object and the ordinary boundary.
This avoids deciding whether an arbitrary UC cube is degenerate.

The initial three modules established a corrected first-stage prototype,
the actual degeneracy union for UC squares, and cancellation of fully
degenerate attachments. Five further modules now construct the actual
coherent attaching map in degree two and prove its cancellation for
propositional carriers. These checked results concern the first two
dimensions. The full all-dimensional construction, prism theorem, and
relative real/synthetic representative comparison remain open.

## Directions examined

| Direction | Finding | Assessment |
| --- | --- | --- |
| Keep all cubes and attach only faces | The terminal diagram retains a spurious loop. | Fails the first acceptance test. |
| Add a separate relation for every degeneracy presentation | One chosen identity relation works in the first-stage prototype. Higher overlapping presentations require further compatibility; independent fillers can create new higher spheres. | Useful prototype, insufficient as a complete recipe. |
| Use the existing graph colimit on the category of cubes/elements | The graph colimit has no identity or composition coherence. The available presheaf coend instead uses a set quotient. | Neither is the required realization unchanged. |
| Replace singular cubes by a cubical nerve of their category of elements | May move degeneracy tests to decidable finite combinatorial cube maps. Needs identity reflection and a new internal classifying-space comparison. | Promising fallback, more infrastructure than the current prototype. |
| Glue degeneracies along finite overlaps before attaching interiors | The actual degree-two attaching map and cancellation for propositional carriers now check. | Useful checked prototype; all-dimensional synthetic coherence is not established. |

The relevant inspected modules are
[graph colimits](../../../Colimit/Base.agda),
[categories of elements](../../../../Categories/Instances/Elements.agda),
and [presheaf Kan extension](../../../../Categories/Presheaf/KanExtension.agda).
The graph colimit's constructors provide object inclusions and edge
paths; categorical laws in the index are not automatically extra HIT
constructors. A set quotient would discard the higher information sought
in this project.

## Checked first-stage correction

[Realization/ReflexiveGraph.agda](Realization/ReflexiveGraph.agda) defines
an untruncated HIT from vertices `A`, edges `R x y`, and designated
identity edges `ρ x`:

```text
vertex x,
edge r : vertex x = vertex y,
refl-edge x : edge(ρ x) = refl.
```

Its eliminator permits arbitrary higher target types. It does not test
whether some other edge equals `ρ x` and does not impose a set or groupoid
truncation.

Two complete control results are checked:

- `isContrTerminalRealization`: one vertex, one designated identity
  edge, and its identity disk form a contractible type.
- `loopRealizationIsoCircle`: one vertex and two edges, only one of them
  designated as the identity, realize the library's synthetic circle.
  Thus the correction preserves the additional loop.

These tests concern the reflexive graph prototype, not the still
unconstructed realization of the entire singular cubical diagram.

Adding higher relations independently is dangerous. In the terminal
example, after contracting this disk, an unconstrained constant square
would give a two-sphere. Two independent fillings of that square can
then give a three-sphere. This is the cellular reason to retain the
intersection of degeneracy presentations, rather than add unrelated
fillers. These higher-sphere descriptions are diagnostic mathematical
arguments, not further Agda equivalences proved by this prototype.

## Checked union of actual UC-square degeneracies

For any premetric space `X`,
[Realization/SquareDegeneracies.agda](Realization/SquareDegeneracies.agda)
uses

```text
C₀ = carrier X,
C₁ = UC(I_real, X),
C₂ = UC(I_real × I_real, X),
horizontal(p)(t,s) = p(t),
vertical(q)(t,s) = q(s).
```

`intersection` proves

```text
horizontal(p) = vertical(q)
  ⇒ Σ x : X. constant(x) = p  and  constant(x) = q.
```

The witness is `p(0)`. Evaluate the assumed square equality at `(t,0)`,
`(0,0)`, and `(0,s)` to obtain both constant-path equalities. This uses
neither excluded middle nor a chosen nondegenerate presentation.

The module then constructs

```text
Latching₂ = Pushout(C₀ --constant--> C₁,
                    C₀ --constant--> C₁),
latchingMap : Latching₂ → C₂.
```

`isSetLatching₂` proves setness from the embedding of constant paths,
using the existing pushout theorem. It is not a truncation constructor.
`isEmbeddingLatching₂` proves that the resulting map into squares is an
embedding. The same-family cases use evaluation to recover the original
path; the cross-family case uses `intersection` and the pushout path.

Thus this pushout is a checked union of the two degeneracy images with
their actual intersection. Its HIT eliminator still specifies the
overlap path when defining maps to arbitrary higher types.

## Checked cancellation for latching attachments

Let `b : B → D` be a synthetic boundary map, `d : L → C` a latching
map, and `R` the previous realization stage. With factors ordered as in
the implementation, define

```text
A = (B × C) ∪[B × L] (D × L),
A → D × C = b ×̂ d,
next stage = Pushout(A → D × C, A --attach--> R).
```

[Realization/LatchingAttachment.agda](Realization/LatchingAttachment.agda)
uses the existing `PushProd` and `_×̂_`. It proves:

- `isEquivLatchingProduct`: if `d` is an equivalence, then `b ×̂ d`
  is an equivalence, for any boundary map.
- `degenerateAttachmentIso`: under that hypothesis the next stage is
  isomorphic to `R`, for any attaching map.
- `terminalLatchingIso`: the degree-two terminal latching object
  `Pushout(Unit ← Unit → Unit)` is isomorphic to `Unit`.
- `terminalAttachmentIso`: this concrete terminal latching map therefore
  gives a stage isomorphic to `R`.

The boundary and interior types share a universe in these lemmas, as
they do for the intended finite synthetic cubes. The previous stage
`R` is an arbitrary type, with no truncation assumption. In particular,
the cancellation theorem also applies when `R` has nontrivial higher
homotopy.

This initial result proves a structural terminal-stage test. The later
`SquareCancellation` result below applies it to the actual UC-square
attaching map. Neither result constructs every stage of the terminal
singular diagram or identifies the full realization's universal property.

## Checked construction: the degree-two attaching map

[SquareBoundary.agda](Realization/SquareBoundary.agda) uses the existing
synthetic [HIT interval](../../../Interval/Base.agda), here called `J`:

```text
D₂ = J × J,
B₂ = PushProd endpoints endpoints,
b₂ = endpoints ×̂ endpoints : B₂ → D₂.
```

The boundary keeps the corner overlaps as pushout paths. A synthetic
square in an arbitrary type gives an interior map `D₂ → A` together
with its entire boundary agreement. An explicit equivalence `B₂ ≃ S¹`
has not been added; no sphere identification is assumed in defining it.

[DegenerateSquares.agda](Realization/DegenerateSquares.agda) fills
horizontal and vertical degenerate squares using the specified endpoint
identity contractions. At a constant square, all four boundary edges
are a loop `u` with a specified `u = refl`. Path induction in that loop
type reduces equality of the two fillers to the reflexive case. This
produces a **relative equality of squares**, fixing all four edges.
`constantSquare-coherence-refl` records its propositional computation
law using `JRefl`. This direct argument superseded the proposed detour
through the universal terminal disk; it imposes no truncation on `A`.

[SquareFrames.agda](Realization/SquareFrames.agda) handles the remaining
UC-witness transports before entering the synthetic target. A frame
contains four real vertices and four real UC paths between them. Its
setness identifies the face-normalization paths across the constant
overlap. It does not assert that the realized boundary or its fillers
form a set.

[SquareAttachment.agda](Realization/SquareAttachment.agda) combines
these two coherences by dependent transport of the relative square
filler. Over `L₂`, each resulting filler gives an interior together with
its restriction proof. This defines

```text
attach₂ : PushProd b₂ latchingMap → R₁,
R₂ = Pushout (b₂ ×̂ latchingMap) attach₂.
```

On the ordinary-boundary branch, `attach₂` interprets the four actual
restricted UC paths. On the degenerate-interior branch it uses the
chosen extension. On their overlap it uses the reversed restriction
proof, with the orientation required by `PushProd`. The inner latching
pushout uses the checked constant-square coherence. No unspecified
attaching-map coherence remains.

`square-boundary` and `square-degenerate` give the corresponding
identifications in `R₂`. This constructs an actual second stage. It
does not yet package an arbitrary real homotopy as a synthetic square
with the exact first-stage edge boundary, nor compare this stage with a
standard all-dimensional singular realization.

[SquareCancellation.agda](Realization/SquareCancellation.agda) adds a
test with the actual UC coefficients. If the carrier of `X` is a
proposition, every UC square agrees with the horizontal constant square
at its value at `(0,0)`. The latching embedding therefore has inhabited
propositional fibers and is an equivalence. The generic cancellation
theorem yields

```text
Iso R₂ R₁,
isEquiv (include₁ : R₁ → R₂).
```

The hypothesis here is `isProp(carrier X)`, not merely the setness
shared by every premetric carrier. This applies to a terminal premetric
space and proves that this actual attachment adds no homotopy in that
case. It is not an all-dimensional terminal contraction.

## Higher dimensions: unresolved coherence, revised priority

For higher dimensions, index degeneracy intersections by nonempty sets
of deleted coordinates. Intersections correspond to unions of deleted
sets: coordinate resets to zero commute, so simultaneous independence
of two sets of coordinates implies independence of their union. The
resulting punctured cube of intersections can be assembled by finite
pushouts. This only addresses the set-valued degeneracy union. It does
not generate the higher synthetic coherence of its attaching map.
The all-dimensional attaching maps and their naturality still need
proof. The present implementation covers ordinary coordinate deletions,
not a full package of connections or symmetries. Further work now follows
the general-construction gate in [SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md),
rather than another fixed-dimensional overlap experiment.

This organization follows the Reedy latching and pushout-product
framework described by
[Riehl–Verity, *The theory and practice of Reedy categories*](https://arxiv.org/abs/1304.6871).
That framework motivates the proposed induction; it is not an imported
internal theorem about these Cauchy-real UC maps.

## Classifying-space candidate and remaining comparison obligations

A cubical nerve of the category of elements is the candidate being
audited for a uniform construction:

```text
K ↦ ∫K ↦ N□(∫K),
N□(C)ₙ = Fun([1]ⁿ, C).
```

The proposed advantage is that a direction of such a finite diagram is
degenerate when its arrows are identities. For the element category,
identity tests can be based on its finite combinatorial cube maps,
using the element-arrow equation to supply equality of the UC labels.
The scalability audit gives an all-dimensional normalization proof
strategy and prism formulas, including the exact remaining obligations.
None of these tests or the replacement comparison is implemented here.

Antolini develops cubical classifying spaces and compares them with
the usual classifying spaces. This motivates the candidate, but does
not establish our constructive internal implementation. The scalability
audit also records a 2026 source's qualification of the older proof for
collapsing connection cells; an abstract-level citation is insufficient
evidence that every comparison step is proved in all dimensions.
[Antolini, *Geometric Realisations of Cubical Sets with Connections, and Classifying Spaces of Categories*](https://research.manchester.ac.uk/en/publications/geometric-realisations-of-cubical-sets-with-connections-and-class/).

Carranza–Kapulkin give combinatorial cubical homotopy-group definitions
and compare them with topological realization. This is a useful model
for the later comparison obligation, not a theorem already available for
our UC construction.
[Carranza–Kapulkin, *Homotopy groups of cubical sets*](https://arxiv.org/abs/2202.03511).

Also, recursively realizing fixed-endpoint real path spaces with units
alone does not supply compatibility with path concatenation. A full
cubical construction retains the squares needed for that compatibility;
the recursive path-space shortcut would need additional composition
and prism coherence.

After constructing a suitable realization, finite regularization,
relative real/synthetic representatives, cubical cover descent, and the
two-cap sphere comparison all remain necessary. The group definition
and the intended comparison target have not changed.

## Verification and resource use

The five new modules all returned exit **0** after their last edits,
with zero holes, unsolved metas, constraints, and warnings:

```text
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/DegenerateSquares.agda
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/SquareBoundary.agda
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/SquareFrames.agda
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/SquareAttachment.agda
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/SquareCancellation.agda
```

Two intermediate frame checks had unsolved implicit arguments. An
explicit `Path Frame` and explicit path endpoints resolved them. There
were no memory-guard stops or manual cancellations in this continuation.
All compiler runs were sequential in the main thread. No Agda source
was changed after the user required the scalability audit.

In the preceding checkpoint, all three final commands returned exit **0**, with zero holes, unsolved
metas, constraints, and warnings:

```text
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/ReflexiveGraph.agda
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/LatchingAttachment.agda
agda-codex Cubical/HITs/CauchyReals/Analysis/RealHomotopy/Realization/SquareDegeneracies.agda
```

The reviewing agents used no compiler and edited no files. Checks were
run in the main thread. Some early square-embedding checks were manually
terminated after substantial memory growth (observed RSS about 14 GiB
and, in a later run, 20 GiB). A cancellation initially remained active
briefly during a replacement launch; it was then terminated explicitly.
No memory-guard exit occurred. Prefix checks exposed an unresolved
h-level index and isolated the expensive embedding proof. The final
version fixes the index explicitly, keeps the setness proof opaque,
and supplies typed inclusion maps, a small joining lemma, and explicit
elimination motives. No options, postulates, or prior Agda modules were
changed.
