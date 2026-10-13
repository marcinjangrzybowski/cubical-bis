# Finite interpolation and the remaining sampling induction

2026-09-11. This continuation implements the finite interpolation
constructor needed by the [analytic regularization route](ANALYTIC_REGULARIZATION.md).
The intended final comparison is still between the real-homotopy groups
of real coordinate spheres and the synthetic homotopy groups of the
library's synthetic HIT spheres. `JointDensity` and that full comparison
remain unproved.

## Checked finite constructor

[FiniteInterpolation.agda](../../Spheres/FiniteInterpolation.agda)
defines `SpherePolygons m x n`. A `Polygon k` is a finite list of
`k+2` actual points of the existing nested loop space `realΩ^n sphere`,
together with admissibility of adjacent points. It is built by appending
one endpoint at a time. It contains no supplied pasting equations.

The module generates those equations and the whole finite path:

- `chain` constructs the existing finite UC paste from the samples.
- `paste-at-start` and `paste-at-finish` prove its endpoint laws.
- `JointVertices` requires joint cube evaluation of the finitely many
  supplied samples. `chain-joint` and `paste-joint` derive jointness of
  the evaluated paste using `JointInterpolation` and `FiniteEvaluation`.
- `loop` restricts the path to the real interval and produces an actual
  element of `Space (suc n)` when its two outer samples are the basepoint.
- `loop-joint` proves that this loop satisfies the existing `Joint`
  predicate. `JointLoops.joint-successor` accounts for the zero-cube
  convention; every higher case uses the same cube-product definition.

There is no new loop representation and no assumption that arbitrary
nested loops already have jointly UC evaluations. The number of samples,
loop depth, and sphere dimension are independent internal naturals.

## Checked clocks and arbitrarily fine rational mesh

[InterpolationClocks.agda](InterpolationClocks.agda) gives branch clocks

```text
clock j z = clip(z + 1 − 2j).
```

Branch `j` moves between its samples on `(2j−1,2j)` and is constant
on the positive-width overlaps `(2j,2j+1)`. These are exactly the
overlaps of `FiniteStitching`. The endpoint samples sit at

```text
node j   = 2j − 3/2
start    = −3/2
finish k = 2k + 1/2.
```

`stretchUC k` maps the real interval affinely from `start` to `finish k`.
Its endpoint equations, lower bound, upper bound, and strict inclusion
below the last pasting cutoff are proved.

[RationalMesh.agda](RationalMesh.agda) constructs a positive width and
its reciprocal, with checked computation equations:

```text
width k      = 2(k+1)
meshRadius k = 3 / width k
fineMesh η   : Σ k : ℕ. meshRadius k < η.
```

The last result uses the existing rational reciprocal bound. This is a
constructive choice of a finite natural number for a supplied tolerance;
it is not a choice of infinitely many witnesses from truncations. The
normalized radius three leaves slack beyond the maximum distance `5/2`
from a branch point to either endpoint sample.

[MeshInterval.agda](MeshInterval.agda) constructs `unscaleUC`, the
clipped inverse affine clock. `unscale-stretch` recovers every real
interval point exactly. `sample k j` applies it to `node j`;
`sample-start` and `sample-finish` recover the two interval endpoints.
Clipping makes the samples valid interval points without separate
membership proofs or a real-order decision.

The public, opaque `clipped-affine-close` proves the quantitative bound
for arbitrary positive rational slope `a` and real offset `b`:

```text
z ≈[ε] w  ⇒  clip(a z+b) ≈[ε a] clip(a w+b).
```

The convenience specialization to `unscaleUC k` was expensive to check
and is not retained. Its generic mathematical bound is checked; the
remaining window proof must consume it through an economical interface.

## Checked approximation estimate and its actual output

[FiniteInterpolationControl.agda](../../Spheres/FiniteInterpolationControl.agda)
connects the finite path to the intended density witness. Given target
tolerance `ε` and interpolation input radius `δ`, set

```text
η = sampleRadius ε δ = min(δ/2, ε/4).
```

`local-error` proves: if both endpoints of an admissible interpolation
are `η`-close to the same reference point, and the nested interpolation
is controlled at output error `ε/4` and input radius `δ`, then every
point of that interpolation is `ε/2`-close to the reference point.
The two input bounds imply the diameter bound `δ` by the triangle law.
The output estimate adds interpolation error `ε/4` and sample error
`ε/4`.

For a reference function `f : ℝ → Space n`, `Against.Accuracy` requires
these two sample estimates only on the actual branch regions, also
restricting to `start ≤ z`:

```text
first branch: start ≤ z < 1
branch j+1:  start ≤ z, 2j < z < 2j+3.
```

The lower restriction is intentional: points arbitrarily far below
`start` are outside the normalized interval and need no error estimate.
`branchwise` transports this predicate through finite gluing;
`path-error` specializes it along `stretchUC`.

`loop-error` proves closeness in the ACTUAL rounded loop premetric. It
uses the strict smaller witness `ε/2 < ε`; it does not infer uniform
`ε`-closeness from pointwise estimates at `ε`.

Finally, `Against.approximant` constructs

```text
Σ q : Space(n+1). Joint(n+1,q) × Close(n+1,ε,p,q)
```

from the finite polygon, its two basepoint equations, `JointVertices`,
`Accuracy`, and recovery of the original path by `f ∘ stretchUC`.
This is exactly the witness required under the truncation in
[JointDensity](../../Spheres/DenseRepresentatives.agda). The finite
constructor, its jointness, and its rounded error estimate are now
proved; existence of the appropriate samples remains.

## Exact next implementation

For the density successor at `p : Space(n+1)` and requested `ε`:

1. Open the already merely existing whole interpolation-control modulus
   and the outer path's whole modulus `μ`, under the final truncation.
   Obtain control at `ε/4`, with input radius `δ`, and let
   `η = min(δ/2,ε/4)`, `β = η/2`.
2. Use `fineMesh (μ β)` and the associated samples. Define
   `f z = p(unscaleUC k z)`. Recovery of `p` along `stretchUC` follows
   immediately from the checked `unscale-stretch`.
3. Prove the finite window estimates. Each of the two normalized sample
   nodes is at distance strictly less than three from a point in its
   branch region. Apply `clipped-affine-close` and `fineMesh` to put the
   parameter distance below `μ β`. The outer modulus then gives output
   error `β`. Adjacent normalized sample nodes are distance two, so the
   same bound controls adjacent samples.
4. Apply lower-depth density at tolerance `β` to the finitely many
   interior sample loops. Keep the two outer samples exactly constant,
   using `sample-start`, `sample-finish`, and the given loop's endpoints.
   A recursion over the finite sample list combines witnesses under one
   truncation; no simultaneous choice for infinitely many indices is
   needed. Sample error `β` plus parameter variation `β` gives `η`.
5. Derive adjacent admissibility using the safe radius and the same
   triangle estimates, construct `Accuracy` and `JointVertices`, and
   call `Against.approximant`. This closes the density successor with
   the same invariant in every dimension.

The existing `FiniteStitching.Property` already supplies coverage for
the error proof through positive-gap dichotomy. This route does not
require an additional choice assigning every real point to a closed
grid cell. `FiniteIntervalCover` remains available for the separately
reviewed finite-net route.

Relative approximation of homotopies with prescribed endpoint cubes
still requires its own finite-sampling/collar argument. The variable
synthetic carrier interpreter and relative synthetic representability
also remain separate, substantial obligations. These analytic results
do not prove the final real/synthetic sphere comparison.

## Compiler findings and verification

Five new modules are retained, together with the small
`JointLoops.joint-successor` addition. Their final sources check with
`agda-codex`, exit 0, with no holes, unsolved metas, constraints, or
warnings. No postulates or weakened options were introduced. Final
checks ran sequentially; no agents were started in this continuation.

Compiler cost remains a practical issue. An arithmetic call with
underspecified endpoint arguments expanded heavily; giving every
rational endpoint explicitly fixed it. The largest manually sampled RSS
before termination was about 22.7 GiB. Several later expensive checks
were stopped sooner. These were manual stops, not exit-75 memory-guard
stops.

Sealing the reciprocal-bound theorem made the finite mesh selection
check quickly. Widths and reciprocals are also opaque with computation
laws. Nevertheless, a direct convenience specialization of the generic
clipped-affine estimate to `unscaleUC k` still caused expensive
conversion checking. Explicit arguments, scalar endpoint paths, and
sealing did not resolve that final specialization. It was removed;
the generic estimate and all other retained results check. Temporary
diagnostic versions are not part of the construction.
