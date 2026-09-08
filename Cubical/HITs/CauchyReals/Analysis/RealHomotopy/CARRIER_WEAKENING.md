# Checked carrier weakening and the next normalization law

**Follow-up:** the endpoint square below is now checked, extended over
the whole anchor face with a fixed seed, and used to compare the actual
anchored and fixed-corner transitions. See [CHECKPOINT.md](CHECKPOINT.md)
for the three new modules, the convergence audit, and the paused state.
Variable-carrier grid assembly remains unproved.

2026-09-07. This continues the selected-face direction from
[ALTERNATIVE_APPROACHES.md](ALTERNATIVE_APPROACHES.md). Seven new Agda
modules check. The fixed-corner transition spaces are now proved
contractible, with their full homotopies in the synthetic boundary.
For an arbitrary nested pair of selections, the common coordinate face
also gives a checked family of transitions independent of its anchor.
Composition across different nested pairs remains a separate law.

## 1. Actual corner points and pointed boundary maps

[CarrierCorners.agda](Realization/CarrierCorners.agda) constructs cube
corners, carrier points, and `carrierCorner-boundary`. This last equality
lives in `CubeBoundary`, not merely in its contractible ambient disk.
The recursive step uses the boundary's actual pushout path.

For a nonempty selection `s` compatible with a corner `v`, it supplies

```text
(Carrier s, carrierCorner s v) →∙ (CubeBoundary, boundaryCorner v).
```

It uses the existing `carrierBoundaryMap` as its underlying function.
Compatibility means that every selected signed face contains the corner;
it is finite coordinate data, not mere inhabitation of a homotopy fiber.

## 2. A closed local transition invariant

[PointedCarrierMaps.agda](Realization/PointedCarrierMaps.agda) proves

```text
isContr X → isContr (X∙ →∙ Y∙)
```

for an arbitrary pointed target. Evaluation at the source basepoint is
an equivalence, and pointed maps form its fiber. Consequently, for
pointed maps `p : X∙ →∙ S∙` and `q : Y∙ →∙ S∙`, the complete transition
type

```text
PointedOver p q = Σ w : X∙ →∙ Y∙. q ∘∙ w = p
```

is contractible when `X` is contractible. This retains the entire
pointed commuting homotopy in `S`; it makes no truncation assumption on
`S` and does not claim that `S` is contractible.

[CornerWeakening.agda](Realization/CornerWeakening.agda) applies this to
all nonempty carriers sharing one corner. It constructs transitions,
proves their identity and composition comparisons, and proves their
comparison path spaces contractible. Repeated path-space contraction
supplies higher transition coherence from the same invariant. No new
next-dimensional field is required at each successor.

These are homotopy-compatible maps between carriers. They are not
claimed to be geometric inclusions or to preserve each individual face
strictly. Their commuting homotopy is in the actual synthetic boundary.

## 3. Complete carried maps, restrictions, and extensions

[CarriedMaps.agda](Realization/CarriedMaps.agda) uses the full fiber
presentation

```text
CarriedMap e f = (x : D) → fiber e (f x).
```

A carrier transition acts on each fiber, retaining the path to the
prescribed ambient value. Restriction along any `B → D` is ordinary
precomposition, so it commutes with this action definitionally. This
applies to full cubical boundaries and every individual face in every
dimension.

The module proves the fiber action's identity and composition laws. Its
`mapRelativeSections` also transports a section together with its
specified boundary agreement. These are statements about supplied
sections/extensions, not assertions of their existence.

[CornerCarriedMaps.agda](Realization/CornerCarriedMaps.agda) specializes
the operations to the checked fixed-corner transitions, proving
`weakenCarried-identity`, `weakenCarried-composition`, restriction
compatibility, and the full `weakenExtension` operation.

The distinction between two extension problems remains essential:

- A complete boundary already valued in a contractible carrier has a
  contractible ordinary carrier-valued extension space.
- Lifting a fixed sphere-valued map into that carrier involves fibers of
  its boundary map. Such fiber spaces need not be contractible.

For example, a point-carrier over its own boundary point has the
ambient loop space as its fiber. None of the new proofs confuses these
two extension problems.

## 4. A whole parameter space for changing the anchor

[CarrierAnchors.agda](Realization/CarrierAnchors.agda) defines
sign-preserving inclusions `s ⊆ t` and the fibrant type `Anchor(t)`:
chosen coordinates are fixed (`Unit`), omitted coordinates vary over the
synthetic interval. It is contractible by ordinary induction on dimension.
Geometrically, this is the common coordinate face in the cubical
presentation. It is not asserted to be a homotopy pullback of the
carrier maps into the sphere.

For each nonempty `s ⊆ t`, the file constructs

```text
anchorCarrier(s⊆t) : Anchor(t) → Carrier(s)
E_st(a) : q_s(anchorCarrier(s⊆t,a)) = q_t(anchorCarrier(id,a)).
```

Here `q_s` denotes `carrierBoundaryMap s`. The homotopy is defined on
the whole parameter space, not only at Boolean corners. Its induction
has three cases:

- Both first faces selected: they have the same sign and the maps agree.
- Both omitted: apply the previous homotopy inside the side constructor.
- Source omitted and target selected: use the boundary's inverse push
  path to reach that selected face, then a disk comparison within it.

No selected-to-omitted case is allowed. All dimensions use the same
construction.

## 5. Checked anchor independence for each nested pair

[AnchoredCarrierWeakening.agda](Realization/AnchoredCarrierWeakening.agda)
uses `E_st(a)` to point the source carrier map at the target anchor's
image. For each `a : Anchor(t)`, its pointed transition space is
contractible by the preceding generic theorem.

Forgetting the basepoint data gives one function

```text
transitionOver : Anchor(t) →
  (Σ w : Carrier(s) → Carrier(t). q_t ∘ w = q_s).
```

The codomain retains the complete commuting homotopy. Since `Anchor(t)`
is contractible, `anchor-independent` proves that any two values of
this function agree in that full codomain. `weakeningOver` selects the
value at the contraction center. This is checked for arbitrary internal
dimension and every nonempty nested pair.

This is anchor independence for one fixed inclusion and its displayed
normalization. It is not independence of arbitrary routes through
different carriers. A route around the boundary of a square can carry
the circle's fundamental loop, which must remain visible.

## The next exact normalization problem

For `s ⊆ t ⊆ u`, compare direct weakening with the composite. The new
parametric construction reduces the geometric part to comparing
`E_su` with `E_st` followed by `E_tu`, on the common parameter space
`Anchor(u)`. This must retain the coordinate/restriction normalization
paths that identify their intermediate carrier points. Merely equating
the underlying functions into the contractible carrier is insufficient;
the whole commuting homotopy in the boundary must agree.

### Why a triangle alone does not close the invariant

A read-only coherence audit identified a further condition on this
proposal. Even after obtaining

```text
Θ_stu : E_su = E_st · E_tu,
```

one cannot conclude that all higher comparisons follow just by
transporting each candidate into a contractible `PointedOver` space.
Such transports can change the pointing data while leaving the
forgotten unpointed over-map unchanged as a value. A path between the
resulting pointed lifts can still project to a nontrivial loop of
unpointed over-maps.

A useful diagnostic, not a new formalized theorem in these files, is
to take all carriers and anchors to be `Unit`, with all boundary maps
constant at `b : A` and all edge comparisons `refl`. The pointed
transition space is contractible, whereas the unpointed over-map space
is equivalent to `Ω A`. Higher pointing changes can retain elements of
`Ω² A` after comparison and forgetting. Contractibility of the former
space does not imply contractibility of the latter's comparison paths.

For a four-selection chain, the two composites of the `Θ` triangles
therefore need a compatible comparison, including path associativity.
Implementing one such law and then requesting the next would repeat
the earlier failure to establish an invariant for arbitrary dimension.
The acceptable stronger target is a single normalization operation
on complete comparison frames, with its boundary computations proved
together. Both comparison routes must lift to the same pointed frame
with the prescribed boundaries; separately lifted values are not
enough. This closure property has not been established.

### Comparing with the checked fixed-corner system

There is also a precise comparison with the earlier fixed-corner API.
If `a` represents a compatible Boolean corner `v` and

```text
κ_s : anchorCarrier(s⊆t,a) = carrierCorner(s,v)
κ_t : anchorCarrier(id,a)  = carrierCorner(t,v),
```

then the required square is, with the appropriate association,

```text
E_st(a) · cong q_t κ_t · β_t,v
  = cong q_s κ_s · β_s,v.
```

The paths `β` are the checked `carrierCorner-boundary` paths. A concrete
proof is coordinate induction, using `homotopyNatural` for the inverse
push path and uniqueness of paths inside the disk. This square is now
implemented for generated compatible Boolean corners in
[CarrierCornerNormalization.agda](Realization/CarrierCornerNormalization.agda),
retaining both normalization paths. The subsequent family and actual
transition comparison are described in [CHECKPOINT.md](CHECKPOINT.md).

The fixed-corner coherence theorem and the pairwise anchor-independent
construction are established. A coherent diagram for an entire grid
with varying selections, finite real approximation, and relative
synthetic finite approximation are still unproved. The final real/synthetic
sphere group comparison therefore remains conditional.

## Verification

All seven new modules (`CarrierCorners`, `PointedCarrierMaps`,
`CornerWeakening`, `CarriedMaps`, `CornerCarriedMaps`, `CarrierAnchors`,
and `AnchoredCarrierWeakening`) returned exit 0 from `agda-codex` after
their final edits, with no holes, unsolved metas, constraints, or warnings.
No postulates, option changes, or compiler changes were added. Checks
were sequential and small; no memory-guard stop occurred.

Intermediate diagnostics were resolved with explicit pointed-map
arguments and explicit tuple patterns for indexed face inclusions.
Agents performed read-only mathematical and library reviews without
running Agda.
