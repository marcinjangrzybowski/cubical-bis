# Viability in the current constructive Cubical Agda setting

Latest state: [CHECKPOINT.md](CHECKPOINT.md). The 2026-09-09 restart
selected [analytic regularization](ANALYTIC_REGULARIZATION.md) and
proved nested interpolation, nearby real class equality, and the
density-to-representatives implication. `JointDensity` remains the
absolute analytic target; finite pasting and coverage are checked.
The 2026-09-11 [finite constructor](FINITE_APPROXIMATION.md) now produces
joint real loops and their rounded approximation bounds from suitable
finite samples. Mesh selection and endpoint recovery are checked;
finite sample existence and window estimates remain.
The local endpoint
normalization, its complete family over a fixed common anchor face,
and the comparison of the actual weakening APIs are now checked. An
independent audit still requires a closed variable-carrier interpreter
and relative finite approximation before certifying the full route.

Assessment, 2026-09-07. This concerns the present code and proposed route,
not an impossibility claim about the final theorem. The requirements
remain: arbitrary internal natural-number dimensions, cubical shapes,
the existing UC definitions, and no new choice axioms, postulates,
truncation of the entire target to a set, or compiler/foundation changes.

The sufficient statements and conditional final theorem are in
[MISSING_STATEMENTS.md](MISSING_STATEMENTS.md).

[DIRECTION_TESTS.md](DIRECTION_TESTS.md) records the follow-up: checked
interpolation error control and arbitrary loop-depth operator lifts, plus
the failure of the proposed evaluator-plus-composition invariant to close.
The subsequent [alternative reviews](ALTERNATIVE_APPROACHES.md) produced
checked selected-face carriers and identified the remaining coherent
weakening and synthetic relative-approximation obligations.
[CARRIER_WEAKENING.md](CARRIER_WEAKENING.md) now proves coherent
weakening at a fixed common corner and full anchor independence for
each nested pair. Normalization across varying selections remains a
separate coherence problem; a triangle law alone would not close it.

## Assessment by missing piece

| Piece | Assessment in our settings |
| --- | --- |
| Quotient descent and final group transport | Already available; the explicit conditional theorem packages these checked arguments. |
| Synthetic cubical shapes and complete boundary representation | Checked uniformly in dimension, including relative extensions. |
| Selected-face carriers and local weakening | Checked: full pointed transition spaces at a common corner are contractible; their actions preserve ambient maps, restrictions, and supplied extensions. |
| Changing carrier anchors across a grid | Pairwise anchor independence is checked. A normalization of complete comparison frames, retaining their boundary homotopies, remains unproved. |
| Nearby sphere interpolation and relative boundary preservation | Checked uniformly in sphere dimension. |
| Universal interpolation error control and based-family loop iteration | Checked in `InterpolationControl` and `MappingLifts`. Actual pair packing and recursive control are now checked below; the full presentation isomorphism is unnecessary for this route. |
| Binary interpolation of actual nested loops and nearby real class equality | Now checked uniformly in both dimensions; a direct pair-packing map suffices without the full presentation isomorphism. |
| Jointly UC representatives from metric density | Checked conditional on the explicit `JointDensity` statement, using an unconditional uniform class radius. The density construction remains. |
| Finite positive-overlap gluing and coverage | Checked, including finite sample interpolation, joint loop construction, and rounded error control. Mesh selection is checked; finite sample existence and window estimates remain. |
| Sphere-specific finite approximation at a requested tolerance | Credible constructive proof strategy, with substantial implementation remaining. |
| Exact uncurrying of every iterated real loop | The usual argument has an unresolved modulus-selection step; it is stronger than the comparison needs. |
| Uniform coherent singular realization | Principal research risk. No complete internal recursion has been established. |
| Relative prism correction in an existing realization | A definite local proof obligation, conditional on a coherent prism and its constant computation law. |
| Finite synthetic representatives, relative excision, and cap descent | Substantial independent comparison theorems; they do not follow from geometric approximation alone. |
| Recognition of spheres after cap descent | Plausible ordinary induction on sphere dimension, conditional on the preceding descent theorem. |

The full route is therefore **not yet certified viable end to end**.
The uncertainty is concentrated in realization and its comparison
properties, rather than in the final group algebra.

## The analytic route can avoid two unjustified principles

The actual UC definition in
[Mappings.agda](../../../../Relation/Premetric/Mappings.agda) requires

```text
∥ Σ μ : ℚ₊ → ℚ₊. IsUniformlyContinuousWith μ ∥₁.
```

Choosing a suitable radius separately at each tolerance proves only
`∀ ε, ∥ Σ δ, ... ∥₁`. Moving from that statement to one merely existing
complete modulus is a countable-choice-shaped step. Neither interval
total boundedness nor finite choice by itself justifies that move.
Accordingly, the exact exponential law for every curried real loop is
not established by the ordinary finite-net argument. This confirms the
warning already in [CUBICAL_AUDIT.md](CUBICAL_AUDIT.md), rather than
proving that the exponential law is impossible here.

For the group comparison, regularize at one requested tolerance instead.
There are then finitely many sampled lower-dimensional loops. The
existing [finite choice theorem](../../../../HITs/PropositionalTruncation/FiniteChoice.agda)
extracts their finitely many complete moduli inside one truncation.
Finite minima and composition yield a complete modulus for the resulting
approximation. No simultaneous choice over all tolerances is needed.

There is a second distinction: do not assume a real point belongs to a
chosen closed grid cell. Already the two-cell case at `1/2` asks for a
zero-gap weak-order alternative. The available real dichotomy uses a
strict positive gap. Positive-width overlaps and cubical collars avoid
that assumption; truncating a containing-cell choice would not by itself
justify it.

### A concrete finite construction worth implementing

The checked [sphere interpolation](../../Spheres/UniformInterpolation.agda)
can be instantiated on the subspace

```text
Oₘ = {(x,y) : Sₘ × Sₘ | 0 ≤ dot(x,y)}
Fₘ : UC(I_real × Oₘ, Sₘ).
```

Its diagonal law `Fₘ(t,x,x)=x` and its single modulus give uniform error
control: compare `(t,x,y)` with `(t,x,x)`. Restrict the permitted radius
also by [SphereCloseness.safeRadius](../../Spheres/MetricCloseness.agda)
so that close pairs lie in `Oₘ`. This operator and its error control are now
checked in [InterpolationControl.agda](../../Spheres/InterpolationControl.agda).
They need no compactness or new sharp normalization estimate.

Given jointly UC approximations `qⱼ` to slices at `j/N`, interpolate in
one coordinate using branches

```text
Fⱼ(t,u) = Fₘ(clip(2Nt − 2j − 1/2), qⱼ(u), qⱼ₊₁(u)).
```

The branch is constant at its left sample before `(j+1/4)/N` and at its
right sample after `(j+3/4)/N`. Adjacent branches agree exactly on the
positive-width interval `((j+3/4)/N, (j+5/4)/N)`. An affine rescaling
lets the existing [Stitch.stitchedUC](../PathGroupoid/Stitching.agda)
glue these by finite induction. Its extra parameter space is arbitrary,
so the same gluing operation handles every remaining cube dimension.

The inductive invariant must retain the approximation error, the
prescribed constant boundary, and agreement with the last branch on
the next overlap. Choose the mesh from the outer modulus at a fixed
error, with enough slack for the errors of the sampled approximations.
Do not claim these estimates have already been implemented.

The lift through rounded uniform mapping spaces is now checked in
[MappingLifts.agda](MappingLifts.agda). Pointwise estimates at `ε/2`
provide a strict output rounding witness at `ε`. Retaining the basepoint
law gives `iterateBasedFamily` by structural induction on loop depth.
The new [NestedInterpolation](../../Spheres/NestedInterpolation.agda)
uses a direct based packing map to handle pairs of actual nested sphere
loops. [NestedInterpolationControl](../../Spheres/NestedInterpolationControl.agda)
proves the recursive quantitative invariant. The full product/subspace
presentation isomorphism is no longer needed by this construction.

For relative homotopies, perform the construction with one additional
coordinate and restore prescribed jointly UC endpoint cubes using
nearby-map collars and parameterized pasting. The existing
[NearbyCubes.Deformation.fixes-boundary](../../Spheres/NearbyHomotopy.agda)
already supplies the pointwise boundary-preservation ingredient.

This justification is specific to the sphere target's bounded coordinate
interpolation and normalization. It does not establish regularization
for arbitrary premetric targets.

## Realization remains a separate foundational risk

`CubeMapping` tells us how to interpret a **complete** coherent boundary.
It does not produce that boundary from separately interpreted faces.
The successful induction on restriction arrows is encouraging, but
does not establish an analogous invariant for the entire singular diagram.

The evaluator-plus-composition proposal failed the decisive test detailed
in [DIRECTION_TESTS.md](DIRECTION_TESTS.md): binary compatibility witnesses
require an additional law on triples, which does not follow for arbitrary
choices of those witnesses. Decidable equality of masks handles source
bookkeeping only. A replacement invariant must generate all target
compatibilities together, rather than add another independent field.

There is relevant evidence that this is not routine packaging. Sato's
realization construction identifies a dependency on successively higher
functoriality and is explicitly parametrized at the meta level.
[Sato, 2018 abstract](https://hott-uf.github.io/2018/abstracts/HoTTUF18_paper_13.pdf).
This is not a theorem excluding a special Cubical Agda construction.

### Truncating to the requested degree helps, but is not a solution yet

The checked library theorem `πTruncGroupIso n` allows a target of
h-level `3+n` when comparing homotopy degree `n+1`. In such a target,
extension over a cell of dimension at least `n+3` has contractible
extension type; nonautomatic coherence remains through dimension `n+2`.

This reduces the required depth. It does not construct those lower
stages uniformly for variable `n`. The difference between a construction
for each fixed numeral and one indexed internally by `ℕ` is already
central to the semisimplicial-type problem discussed by
[Altenkirch–Capriotti–Kraus, Section 1](https://people.cs.nott.ac.uk/psztxa/publ/csl16.pdf).
That paper supplies a stronger two-level setting, which is not being
silently adopted here. The analogy identifies a risk, not an
impossibility proof for our particular cubical source.

## Relative correction and sphere recognition

The raw-augmentation-fiber alternative removes separate degeneracy
contractions, but still needs a raw realization and a coherent prism.
The relative correction has a concrete next lemma: on a constant real
homotopy, the projection witness must be the canonical cancellation
witness, and `correctedFiberPath` must then be reflexivity. Equality of
the first-coordinate loop alone is insufficient. This looks like a
local identity-elimination/path-algebra argument once that computation
law of the prism is available.

For sphere recognition in positive sphere dimension, use two overlapping
caps with fixed margins. Bounded normalization supports cap contractions
and an equatorial retraction of their overlap. A relative cubical
cover-descent theorem would identify their realization with a suspension,
permitting induction on sphere dimension with a separate `S⁰` base case.
A disjoint sign split would introduce an unjustified real-order decision,
and cap contractibility alone does not prove descent.

Geometric finite approximation is also distinct from proving that every
synthetic class in the future realization has a finite singular
representative, or that equality of two such classes gives a relative
real homotopy. Those are the substantive `represents` and `complete`
obligations. They must remain explicit even after the analytic work.

## Recommended order

1. Build on the checked interpolation/error-control lemma and loop-family
   lift: compare the admissible-pair presentations and establish the
   parameterized strip-gluing and approximation invariants.
2. Repair or replace the realization invariant in light of the failed
   face-mask composition test. Do not extend it by an independent
   triple-composition field.
3. Only after that gate is passed, implement realization, relative prisms,
   finite synthetic representatives, and cubical cover descent.
4. Derive sphere recognition by induction and apply the checked
   conditional group comparison theorem.

No probability or completion-time estimate is assigned: the realization
gate is an unresolved mathematical construction, not a measured coding
task. The finite analytic plan is promising, but does not remove that gate.
