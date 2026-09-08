# Exact missing statements and the conditional final theorem

2026-09-07. The attaching-map obstruction is one missing ingredient.
It is not presently the only unproved implication between our checked
work and the final group comparison. This file distinguishes the local
obstruction from a sufficient statement for the entire goal.

[VIABILITY.md](VIABILITY.md) assesses which of these statements have
credible constructive proof plans and which remain research risks.

## The local boundary obstruction

In dimension `n+2`, the library defines a complete boundary by

```text
∂Cube (n+2) A =
  Σ lower : Cube (n+1) A.
  Σ upper : Cube (n+1) A.
  (∂ lower ≡ ∂ upper).
```

The last path includes the side faces and their overlapping coherence.
It is not merely a proof that a set of vertices agrees. For a square,
it supplies the two side edges between the boundaries of the opposite
edges. In higher dimensions its components themselves carry higher
face data.

[BoundaryObligation.agda](Realization/BoundaryObligation.agda) exposes
the local missing type, for cell labels `Cells`, a preceding stage `A`,
and its interpretations `lower`, `upper` of opposite faces:

```agda
MissingSideCoherence =
  (σ : Cells) → ∂ (lower σ) ≡ ∂ (upper σ)
```

Its `attachingMapFromCoherence` constructs an actual
`CubeBoundary (n+2) → A` from this data, using the checked inverse of
`boundaryMapsEquiv`. `attachingMap-boundary` proves recovery of the
complete boundary data.

The unproved realization construction must **generate** these paths
from its prescribed lower-dimensional cells, uniformly in dimension,
and verify their face computation laws. Arbitrarily choosing the paths
does not prove that the prescribed side faces were interpreted correctly.
This local module makes that output type visible; it is not a complete
specification or construction of a realization functor.

## A sufficient statement for the final goal

[ComparisonObligations.agda](ComparisonObligations.agda) defines
`RepresentativeComparisonData n X A`. Let `R.Loop` be the actual real
loops in `realΩ^ n X` and `Target = Synthetic.πGr n A`. The fields are:

```agda
realize : R.Loop → fst Target

respects : (p q : R.Loop) →
  R.PathHomotopy p q → realize p ≡ realize q

preserves : (p q : R.Loop) →
  realize (R.concatPath p q) ≡
  GroupStr._·_ (snd Target) (realize p) (realize q)

complete : (p q : R.Loop) →
  realize p ≡ realize q → R.Homotopic p q

represents : (a : fst Target) →
  ∥ Σ[ p ∈ R.Loop ] realize p ≡ a ∥₁
```

The fields specify a representative map, real-homotopy invariance,
multiplication, injectivity after quotienting, and surjectivity without
choosing representatives globally. `comparisonFromData` derives the group
isomorphism using the existing checked quotient argument in
[Comparison.agda](Comparison.agda). These conditions were already the
parameters of `FromRepresentatives`; the new record makes them a named
statement that can be passed to the final theorem.

[The sphere specialization](../../Spheres/ComparisonObligations.agda)
defines

```agda
SphereComparisonObligation n m =
  RepresentativeComparisonData n (RealSphere∙ m) (S₊∙ m)
```

and proves the exact implication requested:

```agda
sphereComparisonFromObligation : (n m : ℕ) →
  SphereComparisonObligation n m →
  GroupIso (realπGr n (RealSphere∙ m))
           (Synthetic.πGr n (S₊∙ m))
```

`sphereComparisonFromAllObligations` quantifies over all `n` and `m`.
The missing result is an inhabitant of `SphereComparisonObligation n m`
for all dimensions. No such inhabitant is postulated. The homotopy
degree is `n+1`; the sphere dimension is independently `m`.

## Where the realization route enters

The same sphere file proves `sphereComparisonViaRealization` from:

1. A pointed higher type `R` intended to realize the real sphere.
2. `RepresentativeComparisonData n (RealSphere∙ m) R`.
3. A pointed equivalence `R ≃∙ S₊∙ m`.

The proof first derives the representative group comparison and then
composes it with `Synthetic.πIso` for the pointed sphere equivalence.
It does not assume the first group isomorphism as a field.

Uniform attaching maps would help construct `R` and the first two fields
of the representative data. They do not alone prove all five fields
or the pointed sphere equivalence. Remaining mathematical work includes:

- The analytic bridge from iterated real loops to appropriate jointly
  UC cubes. The existing currying isomorphism still retains an explicit
  equiuniformity condition.
- Relative prism and concatenation compatibility.
- Relative approximation and representability, needed for `complete`
  and `represents`.
- Identification of the realized real sphere with the pointed synthetic
  sphere, needed for the separate realization route.

Thus the new conditional theorem proves sufficiency of explicit missing
mathematical statements. It does not show that the attaching-map lemma
is the sole remaining obstacle, or turn the roadmap into assumed axioms.

## Verification

The local `BoundaryObligation` module, generic `ComparisonObligations`
module, and sphere `ComparisonObligations` module all returned **exit 0**
from `agda-codex` after their last edits, with no holes, unsolved metas,
constraints, or warnings. The proof assumptions are ordinary function
arguments and record fields; no inhabitant is postulated.

During compiler diagnosis, four checks of an earlier concrete record
were manually stopped as memory grew; the highest sampled RSS was about
13 GiB. Abstracting the loop carrier, homotopy relation, concatenation,
and target group as parameters of the small record resolved the issue.
The final comparison proof is opaque to limit downstream unfolding.
No memory-guard stop occurred, and compiler processes never overlapped.
