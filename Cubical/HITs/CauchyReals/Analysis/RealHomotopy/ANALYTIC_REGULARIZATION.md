# Analytic restart: nested interpolation and dense representatives

**2026-09-11 continuation:** [FINITE_APPROXIMATION.md](FINITE_APPROXIMATION.md)
adds checked finite sample interpolation, actual joint loop construction,
the rounded approximation estimate, rational mesh selection, and inverse
clocks. It supersedes the implementation-status list below. The finite
sampling/window induction and `JointDensity` remain unproved.

2026-09-09. The restart compared the carrier, finite-recipe, James,
and analytic routes. The selected concrete direction is **finite real
regularization**, retaining the existing iterated real loop spaces.
It has a fixed quantitative induction invariant and now reaches actual
`realπGr` classes. The full real/synthetic sphere comparison is still
unproved.

## Why this direction was selected

The previous checkpoint completed a valid local carrier theory. The
independent reviews did not find a closed successor for a whole grid
with varying target carrier labels. A subdivision tree alone does not
solve the overlap problem. A restricted finite program with literally
shared interface programs could admit structural interpretation, but
would still need an independent synthetic completeness theorem.

The analytic route has a different successor: finitely sample the outer
real parameter, approximate the lower loops, and paste controlled
interpolations across positive overlaps. The same continuity, error,
and boundary conditions recur at every depth. The new work proves
supporting operations and an actual reduction of representative
existence to metric density, rather than adding another synthetic
coherence field.

## 1. Packing related pairs of nested loops

[RelatedLoops.agda](RelatedLoops.agda) starts with a reflexive
proposition-valued relation `R` on a pointed premetric space. It defines

```text
Rel 0 p q = R p q
Rel (n+1) p q = (t : realInterval) → Rel n (p(t)) (q(t))
Pairs n = {(p,q) : Ω_real^n X × Ω_real^n X | Rel n p q}.
```

`Step.packUC` maps `Pairs (n+1)` into `realΩ (Pairs n)` by evaluating
both loops at the same real time. The two supplied loop moduli give
slice continuity; the map on pairs has modulus `ε ↦ ε/2`, using an
explicit rounding witness in the uniform function-space premetric.
The map preserves the basepoint.

The predicate lives on real premetric carriers, which are sets. This
does not use proposition-valued carriers inside a higher synthetic
sphere. No common modulus for the original nested loops is assumed.
No inverse to the packing map is needed by the interpolation proof.

## 2. A closed interpolation induction

[PackedLoopFamilies.agda](PackedLoopFamilies.agda) checks the successor
with abstract spaces and exposes a computation law. It combines a based
packing map `A → realΩ B` with a based parameterized operator
`P × B → Y` to obtain `P × A → realΩ Y`.

[NestedInterpolation.agda](../../Spheres/NestedInterpolation.agda)
specializes this to admissible sphere pairs and constructs

```text
H_n : UC(realInterval × Pairs n, realΩ^n sphere).
```

Unlike the earlier `IteratedInterpolation`, its input is an actual
pair of nested sphere loops. `interpolate-successor` proves pointwise
evaluation agrees with the lower operator. The file proves start, end,
diagonal, agreement-preservation, and basepoint laws in every dimension.

The operator is opaque; clients use its checked laws. This matters for
compiler memory as well as proof organization.

[JointInterpolation.agda](../../Spheres/JointInterpolation.agda) proves
that evaluating this nested interpolation agrees with the base sphere
interpolation, uniformly in depth. If the two supplied loops have
jointly UC cube evaluations, `Between.familyUC` gives a single jointly
UC map on `Interval × CubeSpace n`, including interpolation time.
The proof composes the base operator with the two known joint maps; it
does not infer jointness for an arbitrary nested loop.

## 3. Quantitative control at every depth

[NestedInterpolationControl.agda](../../Spheres/NestedInterpolationControl.agda)
proves that a sufficient sphere radius remains sufficient at **every**
loop depth. Repeated evaluation preserves a given closeness radius, so
the same `SphereCloseness.SafeRadius δ` implies pointwise admissibility
throughout all loop coordinates.

The interpolation error modulus is lifted by

```text
liftModulus 0 μ ε = μ ε
liftModulus (n+1) μ ε = liftModulus n μ (ε/2).
```

The successor obtains error `ε/2` on every slice and introduces that
strictly smaller radius as an output rounding witness. The proof
controls closeness to both endpoints throughout the entire homotopy.
Each requested depth is obtained by mapping an already merely existing
whole base modulus; there is no per-tolerance selection principle.

## 4. Actual homotopies and real group classes

[NestedNearbyHomotopy.agda](../../Spheres/NestedNearbyHomotopy.agda)
constructs interpolation families over arbitrary additional premetric
parameter spaces. They fix every parameter value where the two maps
agree and inherit the quantitative bounds.

For `p,q : realΩ^(n+1) sphere`, `nearby-homotopy` constructs the existing

```text
Paths(realΩ^n sphere).PathHomotopy p q.
```

Its deformation is jointly UC on the real square and fixes both
endpoints. This is constructed by composing the known operator with
the two supplied paths. It does not uncurry an arbitrary path in a
mapping space.

`nearby-class` proves equality in the actual `realπGr n` group.
`classRadius` gives a merely existing positive radius that works over
the entire representative space. The same underlying sphere radius
can be used at every loop depth.

## 5. The precise remaining absolute density statement

[JointLoops.agda](JointLoops.agda) defines raw cube evaluation of an
existing nested loop and the independent predicate

```text
Joint n p = isUniformlyContinuous(evaluate n p).
```

It proves boundary constancy, evaluation injectivity, and preservation
of pointwise closeness. `asBasedCube` turns a `Joint` witness into a
based real cube. Constants are joint in all dimensions; every existing
one-loop is joint. No theorem asserts that every higher nested loop is
already joint.

[DenseRepresentatives.agda](../../Spheres/DenseRepresentatives.agda)
proves that any metrically dense predicate on the existing
representatives has a representative in every real-homotopy class.
It uses the proved class radius and eliminates its truncation only
into the proposition of representative existence.

The named remaining statement `JointDensity` is:

```text
(δ : positiveRational) (p : realΩ^(n+1) sphere) →
  ∥ Σ q : realΩ^(n+1) sphere.
      Joint (n+1) q × (p ≈[δ] q) ∥.
```

`joint-representatives` derives jointly UC cube representatives for
every `realπGr n` class from this statement. `JointDensity` itself
remains unproved. This is an analytic density obligation, not an
assumed final real/synthetic comparison.

## 6. Finite gluing and constructive coverage

[FiniteStitching.agda](FiniteStitching.agda) defines a finite `Chain` of
jointly UC real branches with adjacent overlap equations. `paste`
constructs the whole jointly UC map. `paste-property` carries an
arbitrary pointwise proposition through the finite construction, using
the correct branch regions. This can retain approximation bounds and
constant boundary conditions simultaneously.

[FiniteEvaluation.agda](FiniteEvaluation.agda) closes the generic
evaluation comparison for a finite paste. For any function
`evaluate : A → Y → X`, it compares a supplied chain into `A` with
a chain into `X`, retaining an arbitrary extra parameter space `B`.
`jointPaste` needs only joint continuity of the finitely many evaluated
branches: it constructs the second chain and all its overlap equations,
then transports the resulting UC proof to evaluation of the original
paste. No continuity assumption on the global evaluation function is
used. This is the required jointness successor once the geometric
branches have been supplied.

The overlap cuts are `0,2,4,...`, each of width one. An audit caught
that consecutive width-one overlaps would leave no open interval in
which to interpolate between distinct samples. The separated cuts
leave a transition interval between plateaus; this correction is
included in the final checked source.

[FiniteIntervalCover.agda](FiniteIntervalCover.agda) proves
`openChainCover`: finitely many successively overlapping open intervals
cover between their outer endpoints. Each successor uses the existing
positive-gap real dichotomy. It neither assigns a real point to a closed
cell nor uses rational approximation, floor, or a real-order decision.
The finite index type is the library's `FinData.Fin`.

The proposed geometric specialization is still to be implemented. For
`N` cells, let `h=1/N`, `s_j=jh`, and

```text
U_j = ((j−1/4)h, (j+5/4)h)
F_j(t,u) = H(clip(2t/h−2j−1/2), q_j(u), q_(j+1)(u)).
```

Adjacent branches agree on
`((j+3/4)h, (j+5/4)h)` by their endpoint laws. Under
`z=2t/h−3/2`, these become the checked overlaps `(2j,2j+1)`.
The first and last branches attain their endpoint samples with slack.
Inside `U_j`, both samples are within `5h/4` of the parameter. The
library's [rational inverse bound](../../../../Data/Rationals/Inverse.agda)
`lowerBoundℕ⁻¹` chooses a sufficiently fine mesh constructively.

## Remaining induction and relative work

To prove `JointDensity`, the next implementation must:

1. Define the finite rational samples and open windows, verify their
   interval bounds, and prove the two-sample distance estimate.
2. Apply the lower-depth density hypothesis to finitely many samples,
   keeping the two outer endpoint samples exactly constant. Combine
   their witnesses and whole moduli within one truncation by finite
   choice.
3. Build the branches, prove adjacent admissibility and overlap laws,
   and instantiate `FiniteStitching` with the approximation/boundary
   invariant.
4. Instantiate `JointInterpolation.Between.familyUC` on the sample
   pairs and `FiniteEvaluation.jointPaste` on their finite chain, then
   restrict the affine real parameter to the interval. The generic
   evaluation comparison is now proved; its geometric instantiation
   supplies `Joint` for the result. UC into a nested loop space alone
   is insufficient.
5. Reserve strict error slack before introducing the outer rounded
   function-space witness. Pointwise closeness at the final radius
   does not by itself give uniform closeness at that same radius.

That would prove absolute representative regularization. Approximation
of homotopies relative to prescribed jointly UC endpoint cubes remains
separate: use a common finite mesh over their real cube parameters and
endpoint collars. An arbitrary extra parameter in a pasting theorem
does not license independently choosing approximations at infinitely
many parameter values.

### Reviewed possible simplification: one flat mesh

The follow-up review again rejected the inference that total boundedness
automatically gives `Joint` for every nested loop. Finite nets at each
tolerance give `∀ ε, ∥ Σ δ, estimate ∥`, not the required
`∥ Σ μ, ∀ ε, estimate at μ ε ∥`. The sample set depends on the tolerance;
finite choice does not exchange these quantifiers.

The library already calls the weaker property
`IsRadiuswiseUniformlyContinuous` in
[UniformContinuity.agda](../../../../Relation/Premetric/Completion/CauchySequence/Reals/Analysis/Integration/UniformContinuity.agda).
That module supplies full UC to radiuswise UC, not the converse.
For a deterministic finite interval net, the review identified
`floor-fracℚ₊` in [Floor.agda](../../../../Data/Rationals/Order/Floor.agda):
bound the reciprocal radius by an integer and apply `openChainCover`
to positive-overlap neighborhoods of the resulting rational grid.

The weaker radiuswise statement nevertheless has a plausible closed
dimension induction: choose an outer finite net from the outer modulus,
apply the lower radiuswise result at its finitely many samples, and
combine three small error terms using `evaluate-close`. This would give
one mesh for the flattened cube at a fixed requested tolerance. A
direct finite interpolation of sphere-valued grid samples could then
avoid recursively approximating lower loop representatives.

Neither the radiuswise lemma nor this alternate flat-grid interpolation
was implemented. Its finite nets, full boundary laws, and comparison to
a curried representative still need proofs. The current nested-sample
route remains selected because its interpolation and joint-pasting
successors are now checked. Switch only if the flat-grid construction
removes more work than it introduces.

## Alternative synthetic reduction retained for later

The James review found a useful finite-stage reduction from existing
connectivity theorems. A 2-connected map `F : A → B` has merely existing
lifts of points and of each specified path `F a₀ = F a₁`, with an
equation identifying the image of the lifted path with that specified
path. `isConnectedCong` and `isConnectedSuc→isSurjection` in
[Connected.agda](../../../../Homotopy/Connected.agda) supply these
implications.

The [James finite-stage connectivity theorem](../../../James/Inductive/PushoutFormula.agda)
and [loop-suspension equivalence](../../../James/LoopSuspEquiv.agda)
therefore suggest reducing a requested sphere-loop degree to a bounded
James stage. This specialization was reviewed but not implemented in
this continuation. Finite stages still contain arbitrary higher values
as letters. They do not supply finite cubical labels; a real/finite-
James family comparison, including deletions and relative homotopies,
would remain a substantial new theorem.

## Convergence assessment and verification

The independent audit now finds progress toward a specific analytic
deliverable: the new results concern the intended left-hand homotopy
groups and reduce their regular representatives to a precise density
statement. The finite successors retain fixed invariants. This is
stronger evidence of convergence than adding local carrier comparisons.

The full comparison is still not certified viable end to end. Neither
the variable-carrier synthetic interpreter nor relative synthetic
finite representability is established by these analytic results.

All eleven new Agda modules listed above checked with `agda-codex`, exit
0, after their final source edits: no holes, unsolved metas, constraints,
or warnings. No postulates or compiler-option changes were added.
Checks ran sequentially; agents performed read-only reviews without Agda.
The final source hashes of all eleven files match successful compiler
snapshots. Local Markdown links and whitespace checks also passed.

One concrete interpolation check was stopped manually after growing to
about 4.6 GiB sampled RSS. Moving its successor into the abstract
`PackedLoopFamilies` module resolved the checking cost. There were no
memory-guard stops. Other diagnostics were resolved by explicit universe
levels, explicit opaque signatures, and repackaging continuity witnesses
when changing a subspace's carrier type. Unrelated working-tree files
were preserved.
