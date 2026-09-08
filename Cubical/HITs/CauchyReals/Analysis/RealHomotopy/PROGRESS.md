# Real/synthetic sphere comparison: progress

## Paused checkpoint: local normalization completed, 2026-09-07

**Start with [CHECKPOINT.md](CHECKPOINT.md) when resuming.** The user
requested a pause after this continuation. Three new modules check
with exit 0: `CarrierCornerNormalization` proves the exact endpoint
square; `CarrierNormalizationFamilies` extends it over the entire
common anchor face with a contractible space of extensions retaining
the seed; `CarrierTransitionComparison` identifies the actual anchored
and fixed-corner weakening maps, including their sphere-valued commuting
homotopies. All three are uniform in dimension and have no holes,
unsolved metas, constraints, or warnings.

The independent audit finds real convergence of the local carrier
theory, but not yet demonstrated convergence to the final comparison.
A variable-carrier finite-grid interpreter and relative approximation
on both sides remain. The checkpoint states a bounded feasibility gate:
the next invariant must generate entire comparison frames with their
prescribed restrictions from independent finite incidence data. Do not
resume by adding separate higher coherence fields. No investigation or
compiler process is pending.

## Carrier weakening and anchor independence, 2026-09-07

[CARRIER_WEAKENING.md](CARRIER_WEAKENING.md) records seven new checked
modules. The selected-face route now has actual corner points, pointed
maps into the synthetic boundary, and a contractible space of complete
pointed transitions between any carriers sharing a corner. Identity,
composition, and higher comparison coherence follow within that fixed
space, uniformly in dimension.

The transitions act on complete carried maps, preserving their ambient
map and commuting with restriction along any boundary/face map.
Identity and composition laws and transport of supplied relative
extensions are checked. These results retain the full commuting
homotopy in the synthetic boundary; disk contractibility is not used to
discard that information.

For each nested pair of nonempty selections, a further construction
uses their whole common coordinate face as a contractible parameter
space. It gives transitions independent of the anchor, including their
unpointed commuting homotopy. This is pairwise independence, not yet a
coherent diagram for changing selections throughout a grid.

The next obstacle is normalization between these local pointed
presentations. A triangle comparing three selections is not enough by
itself: independently transporting comparisons into contractible
pointed spaces can leave nontrivial higher paths after forgetting the
basepoints. The new note states the exact endpoint square and explains
why a proof must normalize complete comparison frames, rather than add
one coherence field at a time. Finite approximation on both sides also
remains unproved; the final group comparison remains conditional.

All seven modules returned exit 0 after their final edits, without holes,
unsolved metas, constraints, or warnings. No postulates or options were
added. Compiler checks were sequential; agents performed read-only
reviews without calling Agda.

## Interpolation, loop iteration, and alternative routes, 2026-09-07

[DIRECTION_TESTS.md](DIRECTION_TESTS.md) records five new checked modules:
the universal sphere interpolation with quantitative control, a general
operator lift through arbitrary iterated real loop spaces, its sphere
specialization, and contractibility of complete cubical extensions in
contractible carriers. The final module constructs actual HIT unions of
selected coordinate faces, proves them contractible when the selection
is nonempty and consistent, and maps them into the synthetic boundary.
All five returned exit 0 after their last edits,
with no holes, unsolved metas, constraints, or warnings.

The proposed face-evaluator-plus-composition invariant failed its closure
test: compatibility on triples is additional data. Independent reviews
explored repairs and alternatives, documented in
[ALTERNATIVE_APPROACHES.md](ALTERNATIVE_APPROACHES.md). In particular,
the checked `contractible-subtype-loops` lemma prevents treating synthetic
target faces as contractible propositional subtypes. Actual carrier maps
must retain their lift data.

The selected-face carrier construction is concrete progress toward a
repair. Coherent weakening between complete carried-map spaces and
relative finite approximation on the synthetic side remain unresolved.

The analytic progress is uniform in both sphere dimension and loop depth.
It does not yet prove finite approximation or the general group comparison.
An expensive specialization check was resolved by making the universal
interpolation opaque and exposing its proved laws. Agents ran no Agda.

## Explicit missing statements and viability assessment, 2026-09-07

[MISSING_STATEMENTS.md](MISSING_STATEMENTS.md) identifies the local
side-coherence type and gives the exact sufficient representative-level
statement for the final sphere group comparison. Three new modules check
with **exit 0**: `Realization/BoundaryObligation.agda`,
`ComparisonObligations.agda`, and `Spheres/ComparisonObligations.agda`.
The last proves the desired group isomorphism conditionally, uniformly
in both dimensions, and separately spells out the realization route's
pointed sphere-recognition assumption. No missing theorem is postulated.

[VIABILITY.md](VIABILITY.md) assesses the remaining mathematics.
Finite approximation at a fixed tolerance with positive-width cubical
collars has a concrete constructive strategy. Exact uncurrying has a
modulus-selection issue. Uniform realization, finite synthetic
representatives, and relative cubical descent remain unproved; truncating
to a requested degree reduces coherence depth but does not establish an
internal recursion for variable degree. The full route is not yet
certified viable end to end.

The compiler check of an initial concrete obligation record grew to
about 13 GiB sampled RSS and was stopped manually. A small abstract
record, specialized afterwards to the real loops and synthetic group,
resolved the checking issue. Detailed verification is in the missing
statements note. Agents performed read-only reviews without Agda.

## Current direction, 2026-09-07 — certify scaling before implementation

The user requires the plan to scale inherently to arbitrary dimension
before pursuing more construction. The audit in
[SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md) supersedes the earlier
recommendation to try the degree-three overlap next.

The square attachment below is checked, but it does not justify an
all-dimensional coherent tower. Direct latching is now a possible
backend to derive from a general theorem, not the next implementation
task. The revised candidate is a cubical classifying realization of the
category of real singular cubes, with explicit finite normalization and
dimension-independent prism formulas. Its internal realization theorem
has not passed the feasibility gate. Further realization implementation
is paused until the general recursion and its coherent universal property
have an actual constructive proof.

The follow-up in [UNIFORM_CONSTRUCTIONS.md](UNIFORM_CONSTRUCTIONS.md)
proves independent uniform ingredients without implementing another
realization stage. `CubicalShapes.agda` identifies every recursive
synthetic cube boundary and boundary cofiber with the library's spheres.
`FiberCorrection.agda` proves a general correction of homotopies to paths
in a homotopy fiber, retaining the necessary projection coherence.
`CylinderBoundary.agda` supplies a general cylinder-boundary comparison.
`CubeMapping.agda` now identifies maps from disks and boundaries with
the library's `Cube` and `∂Cube` for all dimensions, proves compatibility
with restriction, and identifies relative extensions with `CubeRel`.
The induction retains a complete restriction arrow and applies one
fixed successor operation, so its coherence data does not grow by
adding independently chosen fillers.

All four modules checked with **exit 0**, no holes, unsolved metas,
constraints, or warnings, after their last edits. Compiler runs were
sequential; agents used no Agda.

The new notes assess normalization by the fiber of a raw realization's
augmentation as an alternative to separate degeneracy contractions.
They document its exact remaining coherence obligations, a limitation
on generalizing the classical comparison, and compiler evidence against
two proposed direct HIT shortcuts. No internal realization or sphere
group comparison is claimed.

## Latest checked construction, 2026-09-07 — the actual square attachment

The degree-two attaching map is now constructed for every premetric
space. It includes all four real edge restrictions, fillings of both
degeneracy families, their constant-square overlap, and compatibility
with the ordinary boundary. No attaching-map coherence is left as an
input. This gives an explicit, untruncated second realization stage.

The decisive finding was a smaller proof of the constant overlap:
**path induction on the specified identity-edge contraction gives a
relative equality of the two square fillings**. It does not require
contractibility or setness of the realization. This resolves the
concrete obstacle at the preceding checkpoint.

### New checked modules

- [DegenerateSquares.agda](Realization/DegenerateSquares.agda) constructs
  horizontal and vertical fillers in an arbitrary higher type. When
  their four edges are the same contracted identity, it identifies the
  fillers while fixing those edges. The reflexive computation law is
  also proved using `JRefl`.
- [SquareBoundary.agda](Realization/SquareBoundary.agda) builds the
  synthetic square boundary as a pushout-product of the endpoint maps
  into the HIT interval. A synthetic square yields an interior map
  together with its boundary agreement.
- [SquareFrames.agda](Realization/SquareFrames.agda) packages four real
  vertices and four real UC paths as a frame. Frames form a set. This
  supplies coherence between face-normalization paths, before mapping
  them into the untruncated realization.
- [SquareAttachment.agda](Realization/SquareAttachment.agda) defines
  `attach₂`, `Realization₂`, and the paths identifying each square's
  boundary and each degenerate interior with their first-stage images.
- [SquareCancellation.agda](Realization/SquareCancellation.agda) proves
  that, when the carrier of `X` is a proposition, its actual latching
  map is an equivalence and `include₁ : Realization₁ → Realization₂`
  is an equivalence. Thus the actual square attachment adds no homotopy
  in this case, including for a terminal premetric space. This is
  stronger than the earlier test with abstract `Unit` coefficients.

All five modules returned **exit 0** from `agda-codex` after their last
edits: zero holes, unsolved metas, constraints, and warnings. Two early
frame checks exposed implicit-argument metas; an explicit `Path Frame`
and explicit endpoints for `path-ext` resolved them. There were no
memory-guard stops or manually terminated checks in this continuation.
Compiler runs were sequential in the main thread; both agents performed
read-only reviews without Agda. No earlier Agda files or options changed.

### Next step and remaining scope

The initial suggestion was to test the three-dimensional degeneracy
overlap next. That suggestion is withdrawn by the scalability review
above. The checked reflexive computation law may serve a future general
proof, but it does not establish such a proof. In particular, one cannot
treat arbitrary fixed-boundary fillers as unique.

Higher stages, their functoriality and degeneracy/connection coherence,
the prism theorem, finite regularization, and the sphere comparison
remain open. In particular, `Realization₂` has not been proved equivalent
to a standard cubical singular realization. The new equivalence for
propositional carriers does not establish contraction of the full
all-dimensional terminal realization.

Detailed proof design is in
[REALIZATION_EXPERIMENTS.md](REALIZATION_EXPERIMENTS.md). The next work
is the general feasibility argument in
[SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md).

## Earlier checkpoint, 2026-09-07 — cubical latching prototypes

The follow-up investigation found a promising route past the degeneracy
obstacle: retain all cubes, but glue degenerate cubes along their actual
intersections before attaching interiors. The first two-dimensional
ingredients now check. Detailed findings, alternatives, source links,
and limitations are in
[REALIZATION_EXPERIMENTS.md](REALIZATION_EXPERIMENTS.md).

### New checked modules

- [ReflexiveGraph.agda](Realization/ReflexiveGraph.agda) defines a first-stage
  untruncated realization with designated identity edges identified with
  reflexivity. Its terminal instance is contractible, and adding one
  additional loop gives an isomorphism with the synthetic circle.
- [SquareDegeneracies.agda](Realization/SquareDegeneracies.agda) works with
  actual UC maps into any premetric space. It proves that the horizontal
  and vertical degeneracy images intersect exactly at constant squares.
  Their pushout over the constant paths is a set, by proof rather than
  truncation, and its map into all UC squares is an embedding.
- [LatchingAttachment.agda](Realization/LatchingAttachment.agda) proves
  that an equivalence of latching data induces an equivalence of the
  corresponding pushout-product. Attaching along it preserves the
  previous stage up to isomorphism, for arbitrary higher target types.
  The terminal degree-two overlap pushout is a checked instance.

All three modules returned **exit 0** from `agda-codex` after their last
edits, with zero holes, unsolved metas, constraints, and warnings. The
agents performed read-only reviews without Agda. Memory-heavy early
square-embedding checks were stopped; explicit types, an explicit
h-level index, and smaller opaque/helper proofs resolved the elaboration
problem. The experiment notes record the resource details. No previous
Agda module, options, or group definitions were changed.

### Viability and the next proof obligation

The latching route now has stronger evidence than a merely proposed
coherence interface: its actual UC-square overlap and embedding are
checked, and the terminal attachment cannot introduce spurious homotopy
when its latching map is an equivalence.

The next open task is constructing the actual degree-two attaching map
into the first realization stage. It must agree on genuine square
boundaries, horizontal degeneracies, vertical degeneracies, and their
constant-square overlap. The checked contractible identity disk may
supply that overlap coherence before mapping it into the general stage.
This is a concrete proposal, not a completed proof.

For higher dimensions, finite pushouts indexed by deleted-coordinate
subsets may retain all intersections. The induction, connections,
functoriality, and prism theorem remain open. A cubical category-of-elements
replacement remains a larger fallback. Neither finite regularization nor
the general real/synthetic sphere comparison is proved yet.

Work stops at this new construction checkpoint: the recommended route
has passed its initial compiler tests, and the remaining coherence task
is now localized to an explicit attaching map.

## Earlier checkpoint, 2026-09-07 — a common metric radius and cubical audit

The common-radius theorem is now checked. Two agents also completed
read-only code surveys while the main thread alone ran Agda. Work is
paused at an important architectural checkpoint from that survey:
the cubical singular realization needs an explicit treatment of
degeneracies and their coherences. The full real/synthetic sphere
comparison and finite regularization remain unproved.

### New checked result

[MetricCloseness.agda](../../Spheres/MetricCloseness.agda) proves, for
every sphere dimension `m`,

```text
∥ Σ δ : positive rationals.
    ∀ x y : S_real^m.
      x ≈[δ] y ⇒ squaredDistance(x,y) ≤ 2 ∥.
```

Here `≈` is the existing maximum-coordinate subspace premetric. The
radius is uniform over the entire sphere. It is merely existing; the
theorem does not select an explicit numerical radius.

`SphereCloseness.squaredDistanceUC` first establishes a global UC map on
the product of two spheres, using bounded coordinate multiplication and
the checked identity `squaredDistance(x,y) = 2 - 2 dot(x,y)`.
`squaredDistance-diagonal` proves that this value is zero at `(x,x)`.
For one modulus `μ` of the global scalar map, use `δ = μ(1)` and compare
`(x,y)` with `(x,x)`. The output is within one of zero, hence below one
and at most two. `safeRadius` packages this argument under propositional
truncation. Only one value of one existing modulus is used; no additional
choice principle is introduced.

Applying this radius pointwise supplies the hypothesis of the previously
checked `NearbyMaps`, `NearbyPaths`, and `NearbyCubes` constructions.
It does not yet lift interpolation through iterated rounded uniform
mapping spaces or regularize an arbitrary nested loop.

### Resource-conscious checking

The final command was

```text
agda-codex Cubical/HITs/CauchyReals/Spheres/MetricCloseness.agda
```

It returned **exit 0**, with zero holes, unsolved metas, constraints, and
warnings, after the last Agda edit. No other Agda file was edited in this
checkpoint, and the agents ran no compilers.

Early versions caused substantial elaboration growth. The first check
was manually interrupted after an observed RSS of about 22 GiB; later
slow checks were also interrupted rather than allowed to grow unchecked.
These interruptions returned 130, not memory-guard exit 75. Prefix
checks isolated the costly final proof portions. The successful version
uses small opaque scalar lemmas, transports the existing UC proposition
instead of rebuilding its modulus record in an untyped lambda, and
derives the radius directly from the opaque scalar-map witness with
explicit continuity-projection parameters. All changes were local to
the new module. No postulates, option changes, or API rewrites were added.

### Important finding and next decision

[CUBICAL_AUDIT.md](CUBICAL_AUDIT.md) records the surveys and their source
links. A faces-only attachment of all singular cubes fails even for
`Unit`: the constant interval gives a loop that the constant square does
not kill. Using just nondegenerate cubes would instead require a
decomposition and coverage theorem not provided by the current data;
decidable degeneracy cannot be assumed. Before building a
large singular skeleton, settle the coherent degeneracy construction
and prove the acceptance test `Rᵤ(Unit)` contractible.

The audit also gives constructive mesh and clipped-weight proposals,
identifies existing connectivity lemmas that may establish a dimension
cutoff, and proposes stereographic cap contractions with uniformly
bounded denominators. These remain unimplemented recommendations.
Finite dimension still does not establish finite support of synthetic
representatives. The [comparison plan](COMPARISON_PLAN.md) now records
these distinctions and makes the `Unit` test an explicit checkpoint.

The analytic continuation can independently tackle UC postcomposition
on rounded mapping spaces, the nearby-interpolation lift, and the first
relative square regularization. The recommended architectural next step
is the coherent cubical realization prototype and its `Unit` test.

## Earlier checkpoint — cubical nearby-map homotopies

The nearby-map deformation is now checked, including its relative
conditions. Work is paused at a new comparison idea prompted by the
user's request to keep the development **cubical**: two thick caps and
their overlap may give a direct synthetic suspension pushout. That
comparison is a proposal; the new checked results are listed below.

Real cubes, cube faces, and products with the real interval remain the
working shapes. The planned singular model now uses cubical cells and
their face, degeneracy, and connection structure. Triangulation into
simplexes is not a planned step.

### New checked results

- [CoordinateBounds.agda](../../Spheres/CoordinateBounds.agda) proves
  that a vector with squared norm at most one has every coordinate
  bounded in absolute value by one. It specializes this to sphere
  points and proves that real convex interpolation preserves the bound.
- [UniformInterpolation.agda](../../Spheres/UniformInterpolation.agda)
  defines a jointly UC normalized interpolation when the pointwise dot
  product of the two sphere-valued inputs is nonnegative. Its start,
  end, and equal-input laws are exact equalities.
- [NearbyHomotopy.agda](../../Spheres/NearbyHomotopy.agda) constructs
  the corresponding real deformation under the pointwise squared-distance
  condition below, packages it as the existing `PathHomotopy` for paths,
  and proves full boundary preservation for based cubes of every degree.

The mathematical contract is:

```text
f,g : UC(M, S_real^m),
∀ u. squaredDistance(f(u),g(u)) ≤ 2
    ⇒ H : UC(I_real × M, S_real^m),
       H(0,u) = f(u),  H(1,u) = g(u),
       f(u) = g(u) ⇒ H(t,u) = f(u) for every t.
```

`M` is an arbitrary premetric space. In `NearbyPaths.homotopy`, the two
paths have the same endpoints, so the agreement law proves that both
endpoints remain fixed throughout. In `NearbyCubes.Deformation`, both
cube maps send the boundary to the same point, so the same law fixes
every spatial boundary face, including their intersections. No decision
procedure for boundary membership is used.

All three new files checked with `agda-codex` after their last edits:
exit **0**, zero holes, unsolved metas, constraints, and warnings. A local
name collision with `Lift.lower` and a missing real numeral instance
were corrected during the edit/check loop. No memory-guard exit occurred.
The earlier four normalization modules were not edited in this checkpoint.

### New comparison insight: use two caps instead of a simplicial nerve

For a real sphere of positive dimension, write points as `(h,y)`. Cover it
by `h > -1/2` and `h < 1/2`. The proposed proof contracts each cap to its
pole and identifies their overlap with
`(-1/2,1/2) × S_real^(m-1)`. The latter retracts onto the equatorial sphere
by contracting the interval factor.

This suggests a **binary cubical cover-descent theorem** whose synthetic
output is a pushout. Contracting its two cap terms would give a suspension
of the overlap realization. The library already has `pushoutEquiv`,
`PushoutSuspIsoSusp`, and the synthetic sphere/suspension equivalences.
The detailed formulas and obligations are in
[COMPARISON_PLAN.md, section 4](COMPARISON_PLAN.md#4-preferred-cubical-route-two-caps-and-suspension).

This would remove the need to build the original simplicial nerve for
the sphere comparison. It does **not** remove the internal real-to-synthetic
theorem. We still need cubical realization, relative rectangular
subdivision/gluing, and a proof that the resulting comparison covers all
synthetic homotopy classes in the required degrees.

The cap contractions also require additional analytic proofs. The
relevant dot product can be negative, down to `-1/2`, whereas the current
checked interpolation uses a nonnegative dot product. The proposed
replacement squared-norm bound is `1/4`; cap preservation and both UC
directions of the overlap identification must be proved as well. None
of those new cap statements is claimed checked yet.

### Next work identified at that checkpoint

The first item below was subsequently completed in the current checkpoint.

1. Connect the squared-distance hypothesis to a single small positive
   radius in the existing maximum premetric, uniform over all sphere
   points. At that point the radius theorem had not yet been implemented.
   The proposed route was to prove squared distance UC on the bounded product of two spheres
   and use its modulus around the diagonal, where squared distance is
   zero. Only a merely existing common radius is needed initially.
2. Obtain quantitative approximation control near the sphere and lift
   the interpolation operation through rounded uniform mapping spaces.
   Then prove finite square regularization and the relative
   three-parameter version. A homotopy for already jointly UC maps does
   not yet regularize an arbitrary nested loop.
3. Prove the two-cap geometry and the cubical descent theorem. Induction
   would be on sphere dimension at the level of realizations; it would
   not assert an unrestricted dimension-shift isomorphism of homotopy
   groups.

### Verification commands for the new files

```text
agda-codex Cubical/HITs/CauchyReals/Spheres/CoordinateBounds.agda
agda-codex Cubical/HITs/CauchyReals/Spheres/UniformInterpolation.agda
agda-codex Cubical/HITs/CauchyReals/Spheres/NearbyHomotopy.agda
```

Each final result was exit 0. No postulates, option changes, barrel export
changes, or changes to the definition of `realπGr` were introduced.

## Earlier checkpoint, 2026-09-07 — bounded normalization

Following [COMPARISON_PLAN.md](COMPARISON_PLAN.md). The target remains
`GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m))`.
The general comparison has not been proved.

### Initial audit

- The sphere coordinate type and squared norm already exist in
  [Spheres/Base.agda](../../Spheres/Base.agda), but vector addition,
  scalar multiplication, and their squared-norm identities need local
  lemmas before normalization can be implemented.
- [Positive roots](../../Transcendental/Roots/Base.agda) provide `root`
  and `nth-pow-root-iso`; [reciprocals](../../Algebra/Inverse.agda) provide
  `invℝ₊` and `x·invℝ₊[x]`. Normalization away from zero can use these
  directly, without first constructing a norm at zero.
- [PathGroupoid/Real.agda](../PathGroupoid/Real.agda) already supplies
  uniformly continuous real addition and multiplication with explicit
  bounds. These are useful for bounded coordinate interpolation.
- `PathHomotopy` in [PathGroupoid/Base.agda](../PathGroupoid/Base.agda)
  requires a jointly UC square into the target. For an iterated-loop
  target, a proposed homotopy must therefore be jointly UC in its two
  outer parameters into that rounded uniform mapping space. Merely
  producing a real path between loops is insufficient without the
  corresponding joint-modulus proof.

### Status at the first pause

The finite-coordinate algebra, normalization identities, interpolation
nonvanishing estimate, and **uniform continuity of bounded normalization**
are now checked. Work is paused at this finding, as requested. No new
axioms or changes to `realπGr` were introduced. Finite regularization and
the real-to-synthetic comparison remain open.

### Checked algebraic results

- [Coordinates.agda](../../Spheres/Coordinates.agda): scalar multiplication,
  linear combinations, dot product, nonnegativity of `norm²`, its scaling
  law, and the full quadratic expansion of a linear combination. Endpoint
  and equal-input laws for coordinate interpolation are included.
- [Normalization.agda](../../Spheres/Normalization.agda): normalize any
  vector with positive squared norm; the result has squared norm exactly
  one, and normalization fixes existing sphere points.
- [Interpolation.agda](../../Spheres/Interpolation.agda): for unit vectors
  with nonnegative dot product and every real `t ∈ [0,1]`, the squared
  norm of `(1-t)x + ty` is at least `1/2`. Squared distance at most `2`
  implies the required nonnegative dot product.
- [UniformNormalization.agda](../../Spheres/UniformNormalization.agda):
  `BoundedNormalization.normalizeUC` packages normalization as a UC map
  into the real sphere, for an arbitrary premetric source, a common
  positive coordinate bound, and a positive lower bound on squared norm.
  The normalized map is definitionally the earlier pointwise `normalize`.
  The module also supplies bounded UC squared norm and scalar
  multiplication, with their pointwise computation lemmas.

All four modules checked with `agda-codex`: exit 0, no holes, unsolved
metas, constraints, or warnings. Routine import/instance issues and
missing type annotations on two local opaque definitions were corrected
before reaching this status.

### Insight: start with squared norms

The nonvanishing proof can use
`squaredDistance(x,y) = 2 - 2 dot(x,y)` and
`(1-t)² + t² ≥ 1/2`. This avoids needing the Euclidean triangle inequality
or Cauchy–Schwarz at this stage. The same `1/2` lower bound handles nearby
points and the later hemisphere contractions. These statements concern
coordinates and inequalities; a uniformly continuous deformation still
needs to be packaged before it counts as a real homotopy.

The continuity audit also located `invℝ₊UC` in
[ArcSin/Positive/Core.agda](../../ArcSin/Positive/Core.agda), supplying
uniform continuity of reciprocals on a positive lower-bounded ray, and
`uContRoot` in
[Exponentiation/RationalPower/Core.agda](../../Exponentiation/RationalPower/Core.agda).
These now give a checked compositional normalization proof on bounded
inputs without first establishing the sharp Euclidean Lipschitz estimate
in the original plan.

### Main finding: bounded normalization is already UC

The proved contract, in mathematical notation, is:

```text
f : UC(M, R^(m+1)),   B > 0,   c > 0,
∀ u i. |f(u)_i| ≤ B,
∀ u. c ≤ norm²(f(u))
    ⇒ (u ↦ f(u) / √norm²(f(u))) : UC(M, S_real^m).
```

The proof composes five operations with bounds independent of the input:

1. Finite sums of bounded coordinate products give the UC squared norm.
2. The existing positive square root is UC.
3. Monotonicity gives the lower length bound `√c`.
4. Reciprocation on that positive ray is UC, and its value is bounded
   above by `1/√c`.
5. Bounded coordinate multiplication gives the normalized vector. The
   already checked squared-norm identity puts it in the sphere subspace.

The source premetric space is arbitrary and need not be compact or
complete. Truncated UC witnesses are combined by finite truncation
elimination; no selection of infinitely many witnesses is used.

This changes the implementation order: the full Euclidean norm metric,
its triangle inequality, and the sharp `2/c` normalization estimate need
not precede a UC normalized interpolation. In particular, the checked
`1/2` squared-norm bound is suitable for applying this construction to
nearby sphere points and later cover contractions.

This is **not yet** the finite-regularization theorem. A UC witness by
itself does not give the approximation error bound required by that
induction, nor does it uncurry an arbitrary nested family. At that first
checkpoint the results did not yet package normalized interpolation as a
`PathHomotopy`, prove that cover intersections are preserved, or identify
any new homotopy group.

### Exact next work

1. Prove common coordinate bounds for sphere-valued maps and their finite
   convex interpolations. Relate a small radius in the existing maximum
   premetric to the squared-distance condition used above.
2. Combine `normalizeUC` with the interpolation estimate and exact
   endpoint/equal-input laws to construct the nearby-map real homotopy,
   fixing every part of the domain where the two maps agree.
3. Obtain quantitative approximation control near the sphere, lift the
   construction through rounded uniform mapping spaces, and test square
   regularization plus a relative three-parameter homotopy.
4. Continue to finite hemisphere covers and the internal singular bridge
   only after that representative-and-homotopy comparison is established.

The reciprocal UC lemma currently lives in `ArcSin/Positive/Core`, so the
new module imports that existing result directly. This avoids duplicating
its proof, though it brings a substantial transitive analysis dependency.
The check completed; no memory-guard exit occurred. Moving the scalar
lemma to a smaller shared module is a possible later maintenance task,
not a change made during this work.

### Final verification for this checkpoint

| Changed Agda file | Final command | Result |
| --- | --- | --- |
| `Spheres/Coordinates.agda` | `agda-codex Cubical/HITs/CauchyReals/Spheres/Coordinates.agda` | Exit 0 |
| `Spheres/Normalization.agda` | `agda-codex Cubical/HITs/CauchyReals/Spheres/Normalization.agda` | Exit 0 |
| `Spheres/Interpolation.agda` | `agda-codex Cubical/HITs/CauchyReals/Spheres/Interpolation.agda` | Exit 0 |
| `Spheres/UniformNormalization.agda` | `agda-codex Cubical/HITs/CauchyReals/Spheres/UniformNormalization.agda` | Exit 0 |

Each command ran after the last edit to its file. Every final check had
zero holes, unsolved metas, constraints, and warnings. The new modules
can be imported directly; no existing barrel exports or earlier proof
definitions were changed.
