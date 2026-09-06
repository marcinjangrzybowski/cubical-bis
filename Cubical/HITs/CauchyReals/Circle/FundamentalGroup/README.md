# Comparison with the earlier circle homotopy group

Import `Cubical.HITs.CauchyReals.Circle.FundamentalGroup`.
The chosen basepoint is `injCircle 0` in `CirclePremetricSpace`.

`CircleLoopGroup` is the automorphism group of that point in the new
uniform path groupoid. Its elements are endpoint-fixed uniform homotopy
classes of uniformly continuous maps `[0,1] → Circle`; its multiplication
is the stitched concatenation from `Analysis.PathGroupoid`.

The comparison theorem is a **group isomorphism**, including the group
operations:

```agda
circleLoop≅circleHomotopy :
  GroupIso CircleLoopGroup (AbGroup→Group CircleHomotopyAbGroup)
```

Here `CircleHomotopyAbGroup` is the earlier group from
`Circle.Homotopy.Quotient`: homotopy classes of circle self-maps under
pointwise circle addition. The earlier homotopies need not fix a basepoint;
the new loop homotopies do. The theorem compares these two constructions.

The underlying type equivalence and group equivalence are also exported
as `circleLoop≃circleHomotopy` and `circleLoopGroupEquiv`.

## What the isomorphism does

The forward map sends a loop class to the earlier `integerClass` with the
same winding number. The inverse sends an earlier class to the based loop

```text
t ↦ injCircle (t · k),   k = the winding number of the earlier class.
```

`comparison-winding` proves that the comparison preserves the earlier
winding invariant. `comparison-integer` identifies every integer loop
with the corresponding earlier integer class, in particular the positively
oriented generator.

## Proof

1. `LoopGroup` packages the automorphism group at a point of any premetric
   space. Its operation is exactly `composeClass` from the path groupoid.
2. `Base` extends interval loops constantly outside `[0,1]` and defines
   `loopWinding` using the earlier winding construction.
3. `Invariance` proves invariance under the new endpoint-fixed homotopies.
   It applies the earlier close-loop winding theorem along a finite dyadic
   subdivision of homotopy time.
4. `NormalForm` reuses the earlier `loopIntervalLift` theorem. The lift
   starts at zero and ends at the integer winding number. Interpolating
   it with `t ↦ k · t` gives a homotopy that fixes both endpoints. The
   lift remains under propositional truncation throughout.
5. `Addition` proves `concat-pointwise`: stitched concatenation is
   endpoint-fixed homotopic to pointwise addition of based loops. The
   proof moves the two waiting clocks continuously to the identity clock.
   Pointwise addition of the integer loops `k` and `l` is the `k+l` loop.
6. `Comparison` obtains `circleLoop≅ℤ` and composes it with the earlier
   `ℤ≅circleHomotopy`.

Further results include `loopWinding-concat`, `loopWinding-classifies`,
and `loopClasses-commute`.

No extra axioms, global choices of lifts, or weakened options are used.
Check with:

```sh
agda-codex Cubical/HITs/CauchyReals/Circle/FundamentalGroup.agda
```

Verified on 2026-09-06 with Agda 2.9.0: the complete import checks with
exit code 0, with no holes, unsolved metas, constraints, or warnings.

To keep checking manageable, `Addition` proves the homotopy's boundary
equations directly instead of transporting the entire continuity record.
`Comparison` keeps `integerLoopClass` opaque and unfolds it explicitly
in its defining lemmas, avoiding expansion of the analytic loop during
quotient comparisons.
