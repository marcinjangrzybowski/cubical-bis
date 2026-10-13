# Real homotopy and the synthetic homotopy library

[CHECKPOINT.md](CHECKPOINT.md) records the latest checked work and exact
next statement. The 2026-09-11 [finite approximation](FINITE_APPROXIMATION.md)
continuation constructs actual joint real loops from finite sample lists
and proves their rounded error bound. Finite sample existence and window
estimates remain. The 2026-09-09 restart selected analytic regularization;
[ANALYTIC_REGULARIZATION.md](ANALYTIC_REGULARIZATION.md) documents the
new nested-loop interpolation, actual real group consequences, finite
gluing, and convergence assessment.

Here **real homotopy** means homotopy through uniformly continuous maps
defined on the Cauchy-real interval. **Synthetic homotopy** means homotopy
using Agda paths, as in `Cubical.Homotopy`.

The intended comparison throughout this development is

```agda
GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m))
```

The left side is the real-homotopy group of the real coordinate m-sphere.
The right side is the synthetic homotopy group of the library's synthetic
HIT m-sphere. Both groups have homotopy degree n+1. The existing
[SphereComparison](../../Spheres/Comparison.agda) interface has precisely
these two inputs.

[COMPARISON_PLAN.md](COMPARISON_PLAN.md) documents a proposed proof through
finite regularization, a real cubical singular realization, and a two-cap
cover leading to synthetic suspension. It gives quantitative geometric arguments,
the required new lemmas, and the main formalization risks. This is a
documentation-only proposal; the general comparison remains unproved.
[CUBICAL_AUDIT.md](CUBICAL_AUDIT.md) records the degeneracy-coherence
obstacle found by the code survey.
[REALIZATION_EXPERIMENTS.md](REALIZATION_EXPERIMENTS.md) documents the
follow-up: checked first-stage tests, the actual coherent degree-two
attaching map for UC squares, and cancellation of that attachment for
propositional carriers.
[SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md) supersedes the plan to extend
this prototype dimension by dimension. Further realization implementation
requires a constructive all-dimensional recursion and coherent universal
property. A cubical classifying-space route is being assessed against
that requirement; it is not yet certified internally.
[UNIFORM_CONSTRUCTIONS.md](UNIFORM_CONSTRUCTIONS.md) adds checked
all-dimensional synthetic cubical sphere equivalences, mapping and
relative extension equivalences with the existing cube types, and a
general fiber-homotopy correction. It assesses an alternative normalization
through the augmentation of a raw singular realization.
[MISSING_STATEMENTS.md](MISSING_STATEMENTS.md) exposes the exact
sufficient obligations and the checked conditional final theorem.
[VIABILITY.md](VIABILITY.md) assesses their feasibility in the current
constructive setting, including the modulus-selection issue and the
remaining uniform realization risk.
[DIRECTION_TESTS.md](DIRECTION_TESTS.md) records the checked universal
interpolation/error-control lemma and arbitrary loop-depth operator lift,
and explains why the proposed face-restriction invariant does not close.

[PROGRESS.md](PROGRESS.md) records the implementation begun from that
proposal. The first checkpoint proves bounded normalization uniformly
continuous and establishes the squared-norm lower bound for interpolation
between nearby sphere points. The next checkpoint constructs a jointly UC
nearby-map homotopy, packages it for the existing real paths, and proves
boundary preservation for based cubes.
[MetricCloseness.agda](../../Spheres/MetricCloseness.agda) supplies a
merely existing positive radius in the maximum premetric, uniform over
the entire sphere, that guarantees the required squared-distance bound
of at most two. [InterpolationControl.agda](../../Spheres/InterpolationControl.agda)
now gives a universal interpolation operator and a whole modulus for
closeness to both endpoints. [MappingLifts.agda](MappingLifts.agda) lifts
parameterized operators through mapping spaces and arbitrary iterated
based loop spaces. [NestedInterpolation.agda](../../Spheres/NestedInterpolation.agda)
now supplies binary interpolation on actual nested loop pairs through a
direct packing map. Its quantitative and nearby-homotopy theorems imply
equality of sufficiently close `realπGr` representatives. Finite
regularization remains pending as the explicit `JointDensity` statement.

[ALTERNATIVE_APPROACHES.md](ALTERNATIVE_APPROACHES.md) tracks the subsequent
search for a repaired realization invariant and alternative comparisons.
[CARRIER_WEAKENING.md](CARRIER_WEAKENING.md) develops the selected-face
route: checked coherent transitions at a common corner, their action on
complete carried maps and relative extensions, and anchor independence
for each nested pair of selections. It identifies the remaining
normalization problem for a whole grid with varying carriers.

## Construction for a premetric space

[LoopSpace.agda](LoopSpace.agda) defines a pointed premetric space as a
premetric space together with a chosen point. Its `realΩ` consists of
uniformly continuous real interval loops at that point, with the rounded
uniform premetric inherited from the library's
[function-space construction](../../../../Relation/Premetric/Instances/FunctionSpace.agda).
Two loops are close when a single smaller positive rational radius bounds
their pointwise distance throughout the interval. The basepoint is the
constant loop.

[Groups.agda](Groups.agda) iterates this construction **before** taking any
homotopy quotient:

```agda
realΩ^ zero X = X
realΩ^ (suc n) X = realΩ (realΩ^ n X)

realπGr n X = Loops.loopGroup (fst (realΩ^ n X)) (snd (realΩ^ n X))
```

Thus `realπGr n X` denotes the **(n+1)st** real-homotopy group, matching the
index convention of synthetic `πGr`. It is the existing real fundamental
group of the nth iterated uniform loop space. Group multiplication,
inverses, and all group laws come from the previously checked
[path groupoid](../PathGroupoid/README.md). In degree one this uses exactly
the previous construction when `realπGr` is unfolded. The group definition
is opaque to prevent Agda from expanding large path-groupoid laws during
routine use; `realπGr-loopGroup` exposes its defining group isomorphism.

`realπ n X` uses the ordinary degree convention: zero is the set quotient
by existence of a real path, and positive degrees are the carriers of
`realπGr`. A basepoint is required for groups; degree zero need not be a
group. No completeness or choice assumption is needed.

[Invariance.agda](Invariance.agda) proves that pointed isometries induce
group isomorphisms in every positive degree.

The complete comparison with jointly uniformly continuous n-cubes and the
higher-dimensional commutativity theorem remain to be proved. The checked
currying results below identify the relevant uniformity condition.

## Cubes and currying

[Cubes.agda](Cubes.agda) defines `CubeSpace n = [0,1]^n`, its boundary
predicate `OnBoundary`, and the space `BasedCubes.BasedCube n` of jointly
uniformly continuous maps sending the whole boundary to the chosen point.
`intervalCubeIsoLoop` identifies based 1-cubes with the earlier real loops.
Based cubes themselves carry the rounded uniform premetric.

[Currying.agda](Currying.agda) proves `uniformCurryingIso`, including both
inverse laws:

```text
UC(A × B, X)
  ≅ { g : UC(A, UC(B,X)) | g has a common modulus for all B-slices }.
```

The mapping space uses the rounded uniform premetric. Currying a joint
modulus `mu` uses `epsilon ↦ mu(epsilon/2)` for the outer parameter;
uncurrying uses the minimum of the outer and slice moduli at half the
requested output radius. Triangle inequalities complete the estimate.

[CubeCurrying.agda](CubeCurrying.agda) restricts this isomorphism to boundary
conditions. For every `n`, `basedCubeCurryingIso` identifies based
`(n+2)`-cubes with based real loops in the space of based `(n+1)`-cubes,
equipped with `EquiuniformCubeLoop`. Fixing the first coordinate at either
endpoint gives the constant cube; the remaining faces give each slice's
boundary condition. Both inverse laws are proved.

The common slice modulus has not been proved automatic for the existing
iterated real-loop spaces. This is a substantive remaining step: the
library's `UC` predicate is `∥ Σ mu . IsUniformlyContinuousWith mu ∥`,
so separately obtaining truncated moduli for slices does not by itself
provide one common modulus. Finite subdivisions suggest a route to uniform
estimates on real cubes, but the required witness construction must be
checked without silently selecting countably many truncated witnesses.

For sphere targets, the [comparison plan](COMPARISON_PLAN.md) suggests
regularizing representatives and relative homotopies by finite normalized
interpolation. This could suffice at the level of homotopy classes even
without proving a common slice modulus for every original iterated loop.
That regularization theorem is not yet proved.

## Real spheres

[Spheres/Base.agda](../../Spheres/Base.agda) defines finite real coordinate
spaces with the maximum-coordinate premetric and

```text
RealSphere n = { x in R^(n+1) | sum_i x_i^2 = 1 }.
```

`RealSphereSpace n` supplies the subspace premetric, and `RealSphere∙ n`
chooses `(1,0,...,0)` as basepoint. These definitions include dimension
zero. The one-dimensional sphere has the same coordinates and equation as
the existing Cartesian real circle.

[Spheres/Ball.agda](../../Spheres/Ball.agda) defines the closed Euclidean
unit `RealBallSpace n` by `norm² n v ≤ 1`, and proves
`sphereBallBoundaryIso`: the real n-sphere is the boundary of the real
(n+1)-ball. The inclusion into that ball is nonexpanding.

The geometric route suggested by the cube model has the dimension shifts

```text
(I^n, boundary I^n)  ≅  (B^n, S^(n-1)),
I^n / boundary I^n  ≅  B^n / S^(n-1)  ≅  S^n.
```

For a centered cube, the usual radial ball-to-cube formula away from zero
is `v ↦ (norm_2(v) / norm_infinity(v)) v`; its inverse exchanges the two
norms. The origin maps to the origin. Translating and scaling identifies
the centered cube with `[0,1]^n`. These formulas describe the next geometric
proof, including extension at zero and uniform continuity; the general
ball–cube isomorphism and boundary-collapse sphere comparison are **not yet
formalized** in these modules.

## Library survey

| Existing module or folder | What it provides and how it applies |
| --- | --- |
| [Homotopy/Base](../../../../Homotopy/Base.agda) | Homotopy as pointwise Agda equality. This is synthetic homotopy. |
| [Foundations/Pointed](../../../../Foundations/Pointed/Base.agda) | Pointed types and pointed maps; neighboring modules treat their synthetic homotopies. |
| [Homotopy/Loopspace](../../../../Homotopy/Loopspace.agda) | Iterated synthetic identity-type loop spaces and the Eckmann–Hilton argument. These are different from spaces of real interval maps. |
| [Homotopy/Group/Base](../../../../Homotopy/Group/Base.agda) | `π n A` is the set truncation of the nth synthetic loop space. `πGr n A` packages degree n+1 as a group. `π'Gr≅πGr` compares the sphere-map and loop-space definitions. |
| [HITs/Sn/Base](../../../Sn/Base.agda) | Synthetic spheres `S₊`: `Bool` in dimension zero, the circle HIT in dimension one, then iterated suspension. `S₊∙` chooses basepoints. |
| [HITs/S1](../../../S1/Base.agda) | The synthetic circle's loop-to-integer isomorphism and additivity of winding. Used in the checked degree-one comparison below. |
| [Homotopy/Group/PinSn](../../../../Homotopy/Group/PinSn.agda) | `πₙSⁿ≅ℤ n : GroupIso (πGr n (S₊∙ (suc n))) ℤGroup`. This concerns synthetic spheres. |
| [Homotopy/Group/Pi3S2](../../../../Homotopy/Group/Pi3S2.agda) | `π₃S²≅ℤ`, stated using `π'Gr 2 (S₊∙ 2)`. |
| [Homotopy/Group/Pi4S3](../../../../Homotopy/Group/Pi4S3/Summary.agda) | Several synthetic proofs of π₄(S³) = ℤ/2ℤ. Its local `π` notation shifts the index back to the ordinary degree. |
| [Freudenthal](../../../../Homotopy/Freudenthal.agda), [Hopf](../../../../Homotopy/Hopf.agda), [LES](../../../../Homotopy/Group/LES.agda), [Whitehead](../../../../Homotopy/Whitehead.agda) | Synthetic suspension, fibrations, exact sequences, and comparison results. Useful after an analytic-to-synthetic bridge has been proved. |
| [CW/Base](../../../../CW/Base.agda), [CW/Approximation](../../../../CW/Approximation.agda), [CW/Instances/Sn](../../../../CW/Instances/Sn.agda) | Synthetic CW realizations and approximation. Their realizations are HIT colimits; they do not supply a real singular realization of a premetric space. |

The survey found no existing bridge from uniformly continuous real cubes
or real spheres to these synthetic constructions.

## Checked comparison and the remaining gap

[CircleComparison.agda](CircleComparison.agda) proves the unconditional
group isomorphism

```text
real fundamental group of the previous real circle
    ≅ synthetic π₁ of the circle HIT.
```

It composes the two winding-number classifications through the integer
group, including a proof identifying the standard and fast integer
additions. `circle-comparison-winding` states that the comparison preserves
winding numbers.

[Spheres/Circle.agda](../../Spheres/Circle.agda) proves a pointed isometry
between the previous real circle and `RealSphere∙ 1`, and the induced
isomorphism `circle-sphere-π₁` between their real fundamental groups. The
circle comparison and this geometric identification are kept as separate
checked results.

The general comparison stated at the start has **not been proved in
general** here. For homotopy degree d = n+1, a sphere-map presentation
divides it into these steps:

1. Express real iterated loops in the real m-sphere as boundary-fixed real
   d-cube maps, modulo real homotopy.
2. Use the real ball–cube correspondence and boundary collapse to express
   these classes as based maps from the real d-sphere to the real m-sphere,
   modulo real homotopy.
3. Compare these real sphere-map classes, including their group operation,
   with synthetic pointed maps from `S₊∙ d` to `S₊∙ m`, modulo synthetic
   homotopy. This is the real-to-synthetic step still to construct.
4. Apply the library's `π'Gr≅πGr` to identify the synthetic sphere-map group
   with `Synthetic.πGr n (S₊∙ m)`.

The [detailed comparison plan](COMPARISON_PLAN.md) proposes a concrete
bridge using a real cubical singular realization and a two-cap cover
of the real target sphere. The preferred route keeps the shapes cubical
and uses a synthetic suspension pushout. It works directly with cube classes,
without first completing the ball quotient in step 2.

[Comparison.agda](Comparison.agda) supplies a checked sufficient criterion,
`Comparison.FromRepresentatives`: a realization map from real loop
representatives into the synthetic group must respect endpoint-fixed real
homotopies, preserve concatenation, detect real homotopy when images agree,
and represent every synthetic class. The quotient then yields a group
isomorphism. These hypotheses are explicit parameters, with no postulates
or selected representatives from propositional truncations.

A general sphere comparison still requires constructing such realization
and approximation data, or another proof identifying the two sphere-map
groups in step 3. The earlier real-circle/synthetic-circle comparison is
the checked degree-one example of the intended relationship.

Once a comparison is supplied in higher dimensions, the existing synthetic
sphere calculations can be transported along it. This development does
not claim those higher real-sphere calculations without that missing proof.
