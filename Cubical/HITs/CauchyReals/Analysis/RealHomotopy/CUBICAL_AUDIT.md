# Cubical comparison audit, 2026-09-07

Current revision: [SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md) requires
a constructive all-dimensional realization theorem before more
dimension-specific implementation. The degree-two success below does
not by itself meet that requirement.

Follow-up: [REALIZATION_EXPERIMENTS.md](REALIZATION_EXPERIMENTS.md) records
the subsequent investigation and checked prototypes. That prototype
glues degeneracies along finite overlaps. The actual degree-two
attaching map, its relative overlap coherence, and cancellation for
propositional carriers are checked. Higher stages remain unconstructed.
The audit below records the findings that prompted that work.

This records two read-only code surveys performed alongside the main
thread's Agda work. The reviewing agents ran no compiler and edited no
files. Statements described as proposals below are not checked theorems.
The target remains real homotopy of real coordinate spheres versus
synthetic homotopy of the library's HIT spheres.

## Realization must handle degenerate cubes

The main new architectural checkpoint is the treatment of degeneracies
in the proposed cubical singular realization `Rᵤ(X)`.

Using only nondegenerate singular cubes is not an established shortcut.
Their subtype can be defined without deciding degeneracy, but one must
still prove that it, together with degeneracies, presents every singular
cube with the required compatibility. Deciding whether a UC function
factors through deletion of a coordinate would require additional
information about equality of functions. Neither such a decision
procedure nor the requisite decomposition theorem has been constructed
here; the usual cell-selection argument cannot simply be assumed.

Attaching every singular cube using only its faces also gives the wrong
model. For `X = Unit`, there is one vertex, one loop `p`, and a square
whose boundary word is `p · p · p⁻¹ · p⁻¹`. That square does not kill `p`;
higher-dimensional cell attachments cannot repair this fundamental-group
defect. The constant interval must be identified with the degenerate
vertex cell, with compatible higher identifications.

Consequently the first acceptance test for a candidate realization is

```text
Rᵤ(Unit) is contractible.
```

Choose a construction incorporating degeneracies and their coherences,
or a replacement resolution with a proved comparison, before building a
large singular skeleton. No implementation of either has been found in
the library. This is an unresolved construction problem, not a proof
that a cubical comparison is impossible. Adding a few low-dimensional
relations alone would not establish the needed coherence in every degree.

## A dimension cutoff is easier than finite support

Once a correct realization with suitable skeletal attachments exists,
some required synthetic arguments have close library precedents:

- [CW/Properties.agda](../../../../CW/Properties.agda),
  `isConnected-CW↪`, derives connectivity of a skeleton transition from
  `inlConnected` and the sphere fibers of the attaching-boundary
  projection. Its argument can be reproduced locally for an arbitrary
  cell index type; the finite index in the current CW interface is not
  used by that connectivity argument.
- [SequentialColimit/Properties.agda](../../../SequentialColimit/Properties.agda),
  `isConnectedIncl∞`, promotes connected transitions after a specified
  stage to connectivity of that stage's inclusion in the colimit.
- [Homotopy/Group/Properties.agda](../../../../Homotopy/Group/Properties.agda),
  `connectedFun→πEquiv n f`, uses connectivity `3 + n` to give an
  equivalence on `πGr n`, whose ordinary degree is `n + 1`.

With CW's indexing, these are ingredients for a cutoff through dimension
`k + 1` when computing `π_k`. They are conditional on the proposed
realization having the requisite attachments and connectivity proofs.
They do not construct that realization.

Crucially, finite dimension does not imply finite support among the
possibly infinitely many singular cells in a dimension. The relative
real/synthetic representative comparison is still a separate obligation.
The existing synthetic CW approximation theorem does not supply it.

[Connected.agda](../../../../Homotopy/Connected.agda),
`isConnectedPushout→`, could propagate a cubical cover comparison known
only to a prescribed connectivity: connectivity `r` on the intersection
and `r + 1` on both sides gives connectivity `r + 1` on the induced
pushout map. It does not itself prove cubical cover descent.

## Stereographic cap contractions

There is a simpler proposed contraction for the positive thick cap
`U+ = { (h,y) : S_real^m | -1/2 < h }`:

```text
p = y / (1 + h),
norm²(p) = (1 - h) / (1 + h) < 3.

Inverse, with q = norm²(p):
h = (1 - q) / (1 + q),
y = 2p / (1 + q).
```

Contract by replacing `p` with `(1-t)p`. Its squared norm remains below
three, so the inverse remains in the same cap. The denominators satisfy
`1 + h > 1/2` and `1 + q ≥ 1`. These uniform lower bounds, the coordinate
bounds, and the existing bounded multiplication and reciprocal UC lemmas
suggest a UC proof without a new square-root estimate. At `t = 0` the
contraction is the identity; at `t = 1` it is the positive pole; it fixes
that pole throughout. Reflection gives the negative cap.

The inverse laws, inequalities, joint UC, and endpoint laws must all be
proved. These formulas are a recommendation, not checked Agda code. They
replace the earlier plan to prove cap preservation for normalized blends
having possibly negative dot product. The overlap product identification
and the cubical descent theorem remain necessary.

## Finite meshes without choosing a real cell index

A proposed elementary interval-net lemma is

```text
h > 0, -h < t < (N+1)h
  ⇒ ∥ Σ j : Fin(N+1). |t - jh| < h ∥.
```

Induct on `N`. In the successor step, the overlapping strict comparison
`Dichotomyℝ' (Nh) t ((N+1)h)` either puts `t` in the previous cover or
within `h` of the new endpoint. The base case is the center zero.
For `[0,1]`, take `h = 1/N` with positive `N`. A sufficiently fine mesh
can be obtained from `ℚ.ceilℚ₊` or `ℚ.1/2ⁿ<ε`; both are exported by
[Foundation/Rationals.agda](../../Foundation/Rationals.agda).
Import the dichotomy directly from
[Algebra/Order/Properties.agda](../../Algebra/Order/Properties.agda).
The covering witness stays truncated: no exact cell index for an
arbitrary real number is selected.

For interpolation, clipped affine ramps yield convenient hat weights:

```text
r_j(t) = clip(Nt - j),       0 ≤ j < N,
w_0(t) = 1 - r_0(t),
w_j(t) = r_(j-1)(t) - r_j(t),  0 < j < N,
w_N(t) = r_(N-1)(t).
```

Clipping is monotone, so the weights are nonnegative. Their sum is one
by telescoping, and the clipping laws give exact endpoint weights. Each
weight has UC from the existing affine, clipping, and subtraction maps.
Products give cubical weights in higher dimensions. Still to prove are
support estimates, weighted error bounds, and normalization bounds.

Relevant existing tools are `clamp-monotone-≤ᵣ` in
[Continuity/Clamp.agda](../Continuity/Clamp.agda), `clip-below`,
`clip-above`, and `clip-fixes` in
[PathGroupoid/Interval.agda](../PathGroupoid/Interval.agda), and
`Sum.∑Telescoping` in
[Ring/BigOps.agda](../../../../Algebra/Ring/BigOps.agda).

## Fixed-tolerance estimates and the first square

Finite nets could establish the following for `g : UC(A,UC(B,X))` when
`A` is totally bounded:

```text
∀ ε → ∥ Σ δ . ∀ a b b'. b ≈[δ] b' ⇒ g(a)(b) ≈[ε] g(a)(b') ∥.
```

Use an outer net at the modulus value for `ε/4`, choose only the finitely
many sampled slice moduli with
[`finChoice`](../../../PropositionalTruncation/FiniteChoice.agda), take
their finite minimum at `ε/4`, and use three triangle estimates.
This remains a proposed argument; interval total boundedness has not yet
been implemented here.

This conclusion is weaker than
`EquiuniformSlices = ∥ Σ ν . ∀ ε … ∥`. Moving truncation past every
tolerance would require an additional selection theorem. Thus finite
choice can support approximation at a fixed error, but does not by
itself discharge the current exact uncurrying hypothesis.

For the first square regularization, a smaller route may avoid hat
weights initially. Sample finitely many outer times of the nested loop;
each sampled slice already is a UC interval path. Join adjacent slices
using nearby interpolation and concatenate the resulting joint strips.
[`Pasting.Paste`](../PathGroupoid/Pasting.agda) already handles arbitrary
additional premetric parameters. The clock lemmas `factor-homotopy` and
`concat-factor` in [Factorization.agda](../PathGroupoid/Factorization.agda)
may compare the original loop to the subdivided construction with the
same concatenated parameterization.

The essential missing ingredient is still lifting nearby interpolation
to rounded uniform loop mapping spaces with a joint modulus. Applying
the existing nearby-map homotopy directly to an arbitrary nested family
would assume the joint continuity that regularization is meant to prove.

A useful first lifting lemma would be UC postcomposition on rounded
uniform mapping spaces. If `F : UC(Y,Z)` has modulus `μ`, the induced
map `f ↦ F ∘ f` should have modulus `ε ↦ μ(ε/2)`: convert input rounded
closeness to pointwise closeness, apply `F` uniformly, and use `ε/2 < ε`
as the output rounding witness. The existing function-space module
already has nonexpanding postcomposition. This proposed UC extension
uses a single modulus of `F`, so it does not choose moduli of all `f`.
It would be an ingredient of the interpolation lift, not a proof of
joint evaluation or exact uncurrying of arbitrary nested families.
