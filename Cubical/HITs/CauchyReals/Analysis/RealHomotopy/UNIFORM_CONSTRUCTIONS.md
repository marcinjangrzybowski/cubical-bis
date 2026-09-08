# Uniform cubical constructions and the remaining realization problem

Continuation, 2026-09-07. The requirement in
[SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md) remains in force: establish
an internal argument for arbitrary dimension before implementing a
realization tower. The results below are independent general theorems;
they do not assume that tower exists.

## Checked: every cubical boundary is a synthetic sphere

[CubicalShapes.agda](Realization/CubicalShapes.agda) defines, simultaneously
for all natural numbers, a synthetic disk, its boundary, and the boundary
map. Write `J` for the HIT interval and `e : Bool → J` for its endpoints:

```text
D₀ = Unit                         B₀ = Empty
Dₙ₊₁ = J × Dₙ                    Bₙ₊₁ = PushProd e bₙ
b₀ = empty elimination           bₙ₊₁ = e ×̂ bₙ
```

The pushout defining the boundary glues `Bool × Dₙ` to `J × Bₙ` along
`Bool × Bₙ`. This includes the intersections of the two opposite faces
with all the remaining faces in one recursive definition.

The proof is uniform: each disk is contractible, and the pushout-product
of maps into two contractible disks has domain equivalent to the join
of their boundary types. Consequently `Bₙ₊₁ ≃ Susp Bₙ`. Induction, with
the library's special presentations of dimensions zero and one, gives:

```agda
cubeBoundarySphereIso : (n : ℕ) → Iso (CubeBoundary (suc n)) (S₊ n)
cubeCofiberSphereIso : (n : ℕ) →
  Iso (cofib (cubeBoundaryMap (suc n))) (S₊ (suc n))
```

These are untruncated equivalences with the library's synthetic spheres.
The cofiber collapses the whole boundary. No real sphere carrier is used
as a synthetic sphere. Pointed compatibility, orientations, and the
comparison with a realization of real cubes are further obligations.

## Checked: the mapping and relative extension theorem in every dimension

[CylinderBoundary.agda](Realization/CylinderBoundary.agda) proves a fixed
comparison for any map `b : B → D`:

```text
PushProd e b ≃ Pushout b b.
```

It also proves compatibility with the maps into `J × D`. On the right,
the two copies of `D` map to opposite endpoints and the gluing path for
`y : B` maps to `(seg i, b y)`. The inverse uses the two endpoint gluing
paths and the side interval. Its inverse homotopies use the ordinary
double-composition filler. This is a single general theorem, not a
collection of dimension-specific comparisons.

[CubeMapping.agda](Realization/CubeMapping.agda) then proves, for every
natural number `n` and every higher target `A`:

```text
(CubeDisk n → A) ≃ Cube n A
(CubeBoundary n → A) ≃ ∂Cube n A
```

`restriction-compatibility` identifies restriction along
`cubeBoundaryMap n` with the library operation `∂_`. Taking the fibers of
this comparison gives `cubeExtensionEquiv`: a disk map together with its
agreement with a specified boundary is equivalent to the corresponding
`CubeRel n A`. The zero-dimensional case is included.

The induction retains the entire restriction arrow, including its
domain, codomain, and function. For an arrow `r : C → B`, one fixed
successor operation is

```text
P(C) = Σ x:C. Σ y:C. (x = y)
L(r) = Σ x:C. Σ y:C. (r x = r y)
R(r) : P(C) → L(r),  (x,y,p) ↦ (x,y,cong r p).
```

Both the geometric mapping arrow and the internal cube-boundary arrow
are equivalent to this successor of their previous arrow. Univalence
packages the equivalences and commuting square as a path of arrows;
congruence under `R` carries the whole induction hypothesis. No larger
coherence record is added at the next degree. Interval and pushout
elimination supply the two mapping universal properties used here.

All four new modules (`CubicalShapes`, `FiberCorrection`,
`CylinderBoundary`, and `CubeMapping`) checked with **exit 0** after their
last edits, with no holes, unsolved metas, constraints, or warnings.
Checks ran sequentially in the main thread; reviewers ran no Agda.
Two intermediate diagnostics in the relative extension corollary were
resolved by passing the library's explicit base and family arguments to
`fiberProjIso`. No memory-guard stops occurred.

This proves representation of arbitrary coherent synthetic boundaries.
It does not produce the boundary attached to an arbitrary real singular
cube in a realization. Nor does it yet give naturality of these chosen
mapping equivalences under arbitrary target maps, a pointed sphere
equivalence, or a real/synthetic homotopy-group comparison.

## A second candidate: normalize a raw realization by a fiber

Suppose `Raw(X)` realizes all real singular cubes using only face
attachments. Constant cubes remain cells. Define

```text
T = Raw(*)
p_X : Raw(X) → T
R(X) = fiber p_X t₀.
```

Here the fiber is the untruncated homotopy fiber. This is an alternative
to attaching a separate contraction for each degeneracy and then
constructing their overlapping coherence. It does not yet construct
`Raw`, so it does not close the realization gate.

Classically the extra terminal space is understood: the realization of
the faces-only cubical set with one cube in every dimension is the James
construction on the circle, with homotopy type `ΩS²`.
[Fenn–Rourke–Sanderson, Proposition 3.3](https://arxiv.org/pdf/math/0301354).
The library already has the synthetic
[James construction](../../../James/Base.agda) and its
[loop-suspension equivalence](../../../James/LoopSuspEquiv.agda).
Their agreement with a future internal raw realization remains to prove.

For full singular cubes of a topological space, the classical comparison
map is explicitly `(evaluation, augmentation)` and is a weak equivalence
to `X × T`. Being over the augmentation matters for identifying its
homotopy fiber. The author manuscript's proof uses geometric
transversality and relative collar arguments; this is motivation, not
an internal constructive theorem for our UC cubes.
[Antolini–Wiest, author manuscript, printed p. 48, Theorem 3.1](https://wiest.pages.math.cnrs.fr/rosa.ps).

The terminal test needs none of that external identification: if raw
functoriality identifies `p_*` with `id_T`, then `R(*)` is contractible
as a fiber of the identity, in all dimensions at once.

### Scope: this cannot be generalized to arbitrary minimal cubical sets

There is a useful elementary diagnostic. In the cube category with just
ordered faces and coordinate deletions, the representable interval has
`n+2` cubes in degree `n`: two constants and `n` coordinate projections.
Its ordinary realization is an interval. In its faces-only cellular
chain complex, the constants have zero boundary and the `j`th projection
has boundary `(-1)^(j-1) (c₁-c₀)`. Thus in every positive degree `n`,
the kernel has rank `n+1` and the image from degree `n+1` is the primitive
rank-one constant difference. Its raw homology in degree `n` is `ℤⁿ`.

In particular the second homology is `ℤ²`, whereas that of the terminal
raw realization is `ℤ`. Hence a blanket product comparison for every
faces-and-deletions cubical set would fail this test. The positive source
claim we use is restricted to full singular cubes. A broader introductory
summary in Fenn–Rourke–Sanderson has not been reconciled with these minimal
site conventions; no general product theorem is being assumed here.

## Checked: cancel the projected loop to obtain a fiber homotopy

A real homotopy would give a raw prism. Its projection to `T` generally
traces a loop; it need not be a homotopy over `T`. A constant real
homotopy has the same extra projected loop. Subtracting the constant
prism can therefore correct this problem.

[FiberCorrection.agda](Realization/FiberCorrection.agda) proves the exact
path algebra for arbitrary higher types. Given `p : E → B`, points
`u = (x, α)` and `v = (y, β)` in its fiber over `b`, a path `h : x ≡ y`,
a loop `d : y ≡ y`, and

```text
cong p h = (α ∙ sym β) ∙ cong p d,
```

it constructs `correctedFiberPath : u ≡ v` with first coordinate exactly
`h ∙ sym d`. Congruence preserves composition; cancellation gives

```text
cong p (h ∙ sym d) = α ∙ sym β.
```

The resulting commutative square is the second coordinate of a path in
the fiber. The module also proves the result for families indexed by any
type, giving an equality of fiber-valued functions. No truncation or
dimension-specific fillers are used.

For raw prisms, the displayed hypothesis must follow from augmentation
naturality on the entire raw realization, including all cells. Agreement
only at its vertices is insufficient. The theorem does not supply that
naturality or define a real-homotopy action on `R` by itself.

There is a further based/relative obligation. Where the real homotopy is
constant, its prism must equal the selected constant prism, and the
projection comparison must satisfy a compatible diagonal computation law.
The equality `d ∙ sym d = refl` only contracts the first coordinate;
an arbitrary projection comparison can still contribute higher homotopy
in the fiber. This requirement must be proved, not omitted from a based
group comparison.

## What the source audit rules out

The hard part is still the internal recursion that generates attaching
maps and their higher naturality. Sato describes precisely this recursive
dependency for realization: stage `n` needs functoriality of stage `n-1`,
then higher functoriality of earlier stages. His construction is explicitly
parametrized at the meta level. This documents the difficulty; it is not
an impossibility result for Cubical Agda.
[Sato, 2018 realization abstract](https://hott-uf.github.io/2018/abstracts/HoTTUF18_paper_13.pdf).

The inspected library and compiler do not supply the following shortcuts:

| Proposed shortcut | Specific missing ingredient |
| --- | --- |
| Set-valued cubical nerve | Setness resolves input equations, not higher equalities between synthetic fillers. |
| Graph colimit or ordinary groupoid quotient | The former lacks category-law coherence; a 1-truncated target cannot retain all sphere homotopy. |
| Type localization/nullification | Their recursors invert specified type maps; they do not construct the coherent cubical diagrams needed here. |
| One HIT constructor returning `CubeRel n R ...` | At variable `n`, reduction does not expose the required constructor target. |
| Bundled primitive coordinates `Fin n → I` | The interval-sort rules place this in `SSet`; fibrancy of its function space into a type does not follow from the `I → A` rule. |
| A constructor with a computed `Sub` boundary | The inspected constructor checker handles datatype applications and exposed Pi/PathP binders, not an arbitrary unreduced `Sub` result. |

Compiler evidence is in local
[`CubicalPrims.agda`](/Users/marcin/agda/test/Succeed/CubicalPrims.agda:365)
and [`Data.hs`, `constructs`](/Users/marcin/agda/src/full/Agda/TypeChecking/Rules/Data.hs:1850),
in the checkout at `92016fffeb5711692f5ccefff0e493d25f0ede49`.
These observations exclude those particular shortcuts; they do not rule
out a recursive construction using ordinary fibrant types and pushouts.
No compiler changes or extra axioms were made.

## Next bounded realization obligation

The mapping and relative extension theorem above is now checked. The
next obligation is to construct an actual boundary-valued function from
the internally indexed source cocone, uniformly in dimension. Its
recursive invariant must retain all face compatibilities and show how
the successor generates them. An input field requesting that function
would not count as its construction. The raw-fiber and normalized-nerve
routes both still owe this argument, then prisms, finite regularization,
relative representatives, sphere descent, and multiplication compatibility.

The target remains

```text
GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m)).
```

The sphere dimension `m` and homotopy degree `n+1` remain independent.

The next assessment is in [VIABILITY.md](VIABILITY.md). The precise
sufficient statements and checked conditional final theorem are in
[MISSING_STATEMENTS.md](MISSING_STATEMENTS.md); the local boundary
obstruction alone is not claimed to imply the final comparison.
