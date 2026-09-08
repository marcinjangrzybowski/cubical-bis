# Analytic progress and the face-restriction test

2026-09-07. This follows the two tests proposed in [VIABILITY.md](VIABILITY.md).
The analytic operator and its lift through arbitrary loop depth are now
checked. The proposed realization invariant fails the closure test below.
This is a finding about that invariant, not an impossibility result for
the desired real/synthetic sphere comparison.

## Checked analytic operator

[InterpolationControl.agda](../../Spheres/InterpolationControl.agda)
constructs the universal sphere interpolation on

```text
Oₘ = {(x,y) : Sₘ × Sₘ | 0 ≤ dot(x,y)}
Fₘ : UC(I_real × Oₘ, Sₘ).
```

It proves the start, end, and agreement laws. In particular,
`Fₘ(t,x,x)=x`. Comparing an admissible pair with `(x,x)` and with `(y,y)`
using one modulus for `Fₘ` gives `errorModulus`: a merely existing complete
function `μ : ℚ₊ → ℚ₊` such that

```text
x ≈[μ ε] y  ⇒  Fₘ(t,x,y) ≈[ε] x  and  Fₘ(t,x,y) ≈[ε] y.
```

The implication holds for every admissible pair and every real time.
`controlledModulus` takes the minimum with the previously checked safe
radius, so the same input bound also supplies the squared-distance bound
needed to establish admissibility. It combines two witnesses inside
propositional truncation. No countable choice, compactness theorem, or
new norm estimate is used.

## Checked lift through arbitrary loop depth

[MappingLifts.agda](MappingLifts.agda) proves, for arbitrary premetric
spaces `A`, `P`, `M`, and `N`,

```text
UC(P × M, N) → UC(P × UC(A,M), UC(A,N)),
(p,f) ↦ (a ↦ h(p,f(a))).
```

All mapping spaces use the existing rounded uniform premetric. A modulus
`μ` for `h` becomes `ε ↦ μ(ε/2)` for the lifted operator. Input rounded
closeness implies pointwise closeness; the output estimates at `ε/2`
provide a strict rounding witness at `ε`. Each output map is UC by
composition. No common modulus for every input `f` is required.

For based spaces the fixed inductive invariant is

```text
BasedFamily P X Y =
  {h : UC(P × X, Y) | ∀p, h(p,base_X) = base_Y}.
```

`loopBasedFamily` preserves this invariant. The endpoints follow from the
input loop's endpoints and the given basepoint law; constant-loop
preservation follows by path extensionality. Consequently the internal
natural-number induction `iterateBasedFamily` has type

```text
BasedFamily P X Y → BasedFamily P (realΩ^ n X) (realΩ^ n Y).
```

This is one checked construction for variable `n`, not a sequence of
separately implemented dimensions. These are actual real loop spaces
before quotienting.

The specialization is checked in
[IteratedInterpolation.agda](../../Spheres/IteratedInterpolation.agda):
the source is `realΩ^ n Oₘ`, based at `(x,x)`, and the target is
`realΩ^ n Sₘ`, based at `x`. A separate
product/subspace comparison is still needed to present this source as
admissible pairs of nested sphere loops. The unary operator lift alone
does not establish that comparison or propagate the quantitative
approximation invariant through that presentation.

Finite approximation also still needs the parameterized strip-gluing
invariant, finite sampling estimates, and relative endpoint restoration.
None of those is claimed to follow from the operator lift alone.

## The face-restriction invariant does not close

The proposed test started with an interpreter for cells and paths `η`
expressing compatibility with all face masks. Schematically,

```text
ηθ : restrict θ (eval σ) = eval (restrict θ σ).
```

For two masks, add a composition witness `χ` comparing the direct path
with the composite of the two restriction paths. For three composable
masks, there are two composites of `χ`. After the appropriate whiskering
and associativity adjustment, their equality is a further law `Ξ`:

```text
Ξθφψ : leftComposite(χ) = rightComposite(χ).
```

This law does not follow for arbitrary choices of `η` and `χ`. A useful
mathematical diagnostic is the nested face chain
`vertex ⊂ edge ⊂ square ⊂ cube`. In a constant diagram at a point of
synthetic `S²`, take all restriction paths to be reflexivity. The binary
comparison witnesses then contain 2-loops. Choosing one relevant witness
with a nonzero `π₂(S²)` class and the others trivial obstructs the required
ternary coherence. The library proves this group's nontriviality through
`πₙSⁿ≅ℤ` in [PinSn.agda](../../../../Homotopy/Group/PinSn.agda).
This diagnostic has not been encoded as a counterexample Agda module;
the new checked modules concern the analytic construction.

The masks being a set does not make these higher target paths
proposition-valued. A record containing the evaluator, `η`, and `χ`
therefore cannot itself be the invariant for the desired construction.

## Why the special source has not repaired this

Ordered masks built from `empty`, `keep`, and `fix Bool` admit structural
composition and evaluation against one original real cube. Function laws
can be proved by induction and lifted with `UC≡`. The category-of-elements
API's `ElementHomPathP` and `ElementHom≡` can remove irrelevant equality
proofs from source arrows. This supplies a credible source-category
normalization, but not the complete synthetic boundary interpreter.

The UC maps' underlying functions compose definitionally, while their
continuity certificates differ: [Mappings.agda](../../../../Relation/Premetric/Mappings.agda)
uses `UC≡ refl` for associativity and identities. These source laws do not
supply the arbitrary-dimensional synthetic laws needed after attachment.

All higher compatibility could follow by congruence if every comparison
were obtained from canonical source equalities under a single complete
frame interpreter. The current construction does not supply this:

- [SquareAttachment.square-boundary](Realization/SquareAttachment.agda)
  is a pushout gluing path, not simply congruence of equal cube labels.
- [CubeMapping](Realization/CubeMapping.agda) translates already complete
  boundary data and relative extensions.
- [BoundaryObligation](Realization/BoundaryObligation.agda) still needs
  the side-coherence data that completes the boundary from its faces.

Literal evaluation at synthetic coordinates also cannot provide the
interpreter: an endpoint-preserving map from the synthetic interval to
the real interval would imply equality of its distinct real endpoints.

Two independent read-only reviews found no existing construction in this
library that supplies the missing complete interpreter. Neither review
ran Agda. No further realization stage was implemented.

## Decision point

The analytic direction has passed its first test and has a uniform loop
iteration. Continuing with admissible pairs and finite approximation is
a concrete, useful next task.

The proposed realization invariant has failed its stated closure test.
Before resuming it, we need a replacement construction that generates
all compatibility laws together. Adding `Ξ` as another independent field
would repeat the problem one dimension higher. The final comparison and
the separate representability/descent obligations remain unproved.

At the user's request, further repair and alternative-route reviews were
started after this finding. [ALTERNATIVE_APPROACHES.md](ALTERNATIVE_APPROACHES.md)
records the carrier, algebraic cubical, and James directions and the
obligations they retain.

## Checked carrier test and compiler results

[ContractibleCarriers.agda](Realization/ContractibleCarriers.agda) proves
that complete boundaries, relative cubes, and extension fibers into a
contractible type are contractible in every dimension. The extension
fiber retains its specified boundary agreement, so its uniqueness covers
that higher data as well.

It also proves `contractible-subtype-loops`: a contractible
proposition-valued subtype forces the ambient loop space at each included
point to be contractible. This rules out using such subtypes as the
contractible charts of a synthetic sphere with nontrivial higher homotopy.
Actual synthetic carrier maps require lift data, not just membership.

The subsequent [SelectedFaceCarriers.agda](Realization/SelectedFaceCarriers.agda)
constructs actual HIT carriers for nonempty consistent selections of
coordinate faces, proves their contractibility, and maps them into the
synthetic cubical boundary. Coherent weakening between these carriers
remains to prove, as detailed in the alternatives note.

All five new Agda modules (`InterpolationControl`, `MappingLifts`,
`IteratedInterpolation`, `ContractibleCarriers`, and `SelectedFaceCarriers`)
returned exit 0 after
their final edits, without holes, unsolved metas, constraints, or warnings.
No postulates or new options were introduced. Compiler runs were sequential.

Three initial checks of the sphere specialization were stopped manually
while memory grew; sampled RSS was around 7 GiB. A declaration trace
located the expensive conversion in `interpolationFamily`. Making the
universal interpolation opaque, while exposing and proving its endpoint
and agreement laws, resolved the issue; the specialization then checked.
No memory-guard stop occurred.
