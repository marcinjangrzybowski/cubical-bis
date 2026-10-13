# Restart checkpoint — analytic regularization

## Current checkpoint, 2026-09-11

[FINITE_APPROXIMATION.md](FINITE_APPROXIMATION.md) records five new
checked modules and the exact sampling induction still to implement.
Finite lists of adjacent admissible nested sphere loops now produce
actual based real loops with jointly UC cube evaluation. The finite
constructor generates its overlap equations and endpoint laws.

`FiniteInterpolationControl.Against.approximant` turns suitable finite
sample bounds into the precise witness required by `JointDensity`,
including the strict rounding witness in the actual loop premetric.
Rational mesh selection, inverse clocks, and endpoint samples are
checked. What remains is to construct the finite sample witnesses and
their window bounds, then close the dimension induction. The full
real/synthetic sphere comparison is still unproved.

The generic quantitative clipped-affine estimate checks. A direct
specialization to the inverse mesh clock was expensive to typecheck
and was removed; the next geometric proof should consume the generic
API through a smaller interface. No holes or postulates were introduced.
All five new modules and the changed `JointLoops` check with exit 0
after their final edits. No compiler or agent task is pending.

## Previous analytic checkpoint, 2026-09-09

Work resumed at the user's request. The current concrete direction is
finite real regularization. Read
[ANALYTIC_REGULARIZATION.md](ANALYTIC_REGULARIZATION.md) for the eleven
new checked modules, alternative-route reviews, and remaining proof.

The new construction interpolates actual pairs of nested sphere loops,
uniformly in dimension. It proves jointly UC nearby homotopies and
equality in the existing `realπGr` groups. The same sufficient sphere
radius works at every loop depth. `DenseRepresentatives` proves that
metric density of a predicate suffices for a representative in every
real-homotopy class.

The exact next target is `DenseSphereRepresentatives.JointDensity` in
[DenseRepresentatives.agda](../../Spheres/DenseRepresentatives.agda):
approximate each existing nested loop by one whose raw real-cube
evaluation is jointly UC. [JointLoops.agda](JointLoops.agda) defines
this predicate independently and turns its witnesses into based cubes.
It does not assume arbitrary nested loops can be uncurried.

The finite gluing and open-interval coverage inductions are now checked.
Next construct rational samples and separated interpolation plateaus,
then prove the finite approximation successor using sampled lower joint
loops, strict error slack, and finite choice. `JointInterpolation`
proves jointness of the interpolation branches; `FiniteEvaluation`
proves jointness of the evaluated paste from those branch witnesses.
Their geometric instantiation remains. Relative approximation with
prescribed endpoint cubes remains a separate step.

The audit now finds convergence toward this analytic deliverable, with
actual consequences for the intended groups. The synthetic interpreter
and relative synthetic finite representability remain unresolved.
Do not resume the carrier branch by adding independent higher
coherence fields. The James finite-stage alternative is documented,
but does not supply finite cubical labels.

All eleven new modules checked with exit 0 after their final edits.
No compiler process or agent investigation remains pending at this
checkpoint. Current changes are saved in the working tree.

## Archived carrier checkpoint, 2026-09-07

The following records the earlier pause. Its carrier feasibility gate
still applies to that branch; the current analytic task is above.

## Goal and constraints

The intended theorem remains

```agda
GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m))
```

The group degree is `n+1`; sphere dimension `m` is independent. The
right-hand sphere is the library's synthetic HIT sphere, never the set
carrier of the real sphere. Keep cubical shapes and constructions
uniform in internal natural-number dimensions. No postulates, choice
axioms, weakened compiler options, or foundation changes have been added.

The conditional final theorem is already checked; its missing
representative-level inputs remain in
[MISSING_STATEMENTS.md](MISSING_STATEMENTS.md).

## Latest checked results

This continuation added three modules, consuming the seven preceding
carrier modules described in [CARRIER_WEAKENING.md](CARRIER_WEAKENING.md).

### 1. The endpoint normalization square

[CarrierCornerNormalization.agda](Realization/CarrierCornerNormalization.agda)
defines Boolean anchors of a common coordinate face. Selected coordinates
have their specified sign; omitted coordinates supply a Boolean.
`discreteCorner` generates a compatible corner and `discreteAnchor` its
point in the whole synthetic anchor face. The module constructs the
coordinate and carrier endpoint paths `disk-normalization` and
`corner-normalization`.

Its main theorem `endpoint-normalization` proves the previously missing
square, for every nonempty selection inclusion `s ⊆ t` and generated
compatible corner:

```text
E_st(a₀) · (cong q_t κ_t · β_t)
  = cong q_s κ_s · β_s.
```

`E_st` is the actual `anchorComparison`; `β` is the existing
`carrierCorner-boundary`. The equality lives in the synthetic boundary.
The proof is a single dimension induction. The omitted-to-selected
case uses `homotopyNatural` for the boundary's inverse push path.
Uniqueness of disk paths compares only paths within the selected face;
it is not used to identify arbitrary paths in the sphere.

### 2. A complete normalization family with a fixed seed

[CarrierNormalizationFamilies.agda](Realization/CarrierNormalizationFamilies.agda)
immediately consumes that theorem. For each point `a` of the common
anchor face, `Normalization a` contains both carrier endpoint paths and
the entire sphere-valued square above. The type

```text
Σ f : ((a : Anchor(t)) → Normalization a).
  f a₀ = normalization-seed
```

is contractible. Evaluation of dependent sections over a contractible
domain is an equivalence, so its fiber over the checked endpoint seed
is contractible. No proposition assumption on `Normalization a` is made.

This constructs a whole family together with its endpoint computation
equation. Its comparison path spaces are contractible. Pulling it back
along any parameter map commutes definitionally with restriction, so a
fixed inclusion's anchor cubes and full boundaries are handled together.
It does not normalize independently prescribed seeds or varying labels.

### 3. Comparison of the actual weakening maps

[CarrierTransitionComparison.agda](Realization/CarrierTransitionComparison.agda)
consumes that whole family. It constructs a path of pointed
presentations, retaining both normalization squares. The space of
transition comparisons over this specified path is contractible.

Forgetting the pointing data then proves

```text
transition-comparison a : anchoredTransition(a) = cornerTransition
weakening-comparison    : chosenAnchoredWeakening = cornerTransition.
```

These are equalities in the complete unpointed over-map type

```text
Σ w : Carrier(s) → Carrier(t). q_t ∘ w = q_s.
```

Thus the two previously separate local APIs now provably agree,
including their commuting homotopies in the synthetic boundary.
This is not merely equality of their underlying carrier maps.

## Independent convergence assessment

Two agents performed read-only reviews without invoking Agda. One
developed the normalization proof and the dependent-section invariant;
the other independently audited progress toward the final theorem.

The audit's conclusion is: **the local carrier theory is converging;
convergence toward the full sphere comparison is not yet demonstrated**.
The new lemmas close actual local gaps and use arbitrary dimensions.
However, this carrier cluster still has no consumer constructing a
general `realize`, `complete`, or `represents` field of the final
representative-comparison data.

Three substantial gaps remain:

1. A variable-carrier interpreter from independently defined finite
   cubical incidence data, constructing complete ambient boundaries
   and restriction equations together.
2. Relative synthetic finite approximation: arbitrary synthetic classes
   and homotopies must have finite descriptions of that kind, preserving
   prescribed endpoints after refinement. Existing CW approximation
   through skeleta does not supply finite labels.
3. Relative real finite approximation and compatible carrier assignment.
   The checked interpolation and loop-operator lifts support a concrete
   finite constructive approach; the regularization theorem remains
   unproved. Exact uncurrying is stronger than necessary and should not
   be put back on the critical path.

General singular realization and cap descent are alternative
architectures, not additional required tasks if a direct common-finite-
description comparison succeeds. Do not accumulate both roadmaps into
one mandatory workload.

## The next feasibility gate

Before more carrier implementation, specify one internal type of finite
cubical incidence data and one arbitrary-dimensional successor which
constructs a complete normalized comparison frame together with its
restriction equation.

The inputs must not already contain the missing ambient attaching maps,
arbitrary higher coherences, or complete boundary lifts. An arbitrary
unpointed-frame lifting theorem would be false: even point-carriers can
retain the sphere's loop space in their unpointed over-map type. The
allowed geometric frame condition must be explicit and do real work.

The latest normalization family passes this test only for a fixed
inclusion and fixed endpoint seed. It does not yet pass it for a grid
whose labels and seeds vary. A statement that all transition values
can be normalized does not imply that every generated complete frame
can be normalized with its prescribed boundary.

If the next proposed successor needs an independently chosen
tetrahedron/pentagon law or an unspecified coherent-frame field, stop
extending that hierarchy and mark the grid construction as not yet
certified viable. Preserve the local results and reassess the finite
description or the separate real-approximation branch. Even a successful
interpreter still requires a credible relative synthetic approximation
proof before the overall project can be called close to completion.

## Verification and saved state

All three new Agda modules returned exit **0** from `agda-codex` after
their final source edits, with zero holes, unsolved metas, constraints,
or warnings. Their final checks were sequential:

| Module | Last successful check, UTC |
| --- | --- |
| `CarrierCornerNormalization` | 2026-09-07 02:43:33 |
| `CarrierNormalizationFamilies` | 2026-09-07 02:44:48 |
| `CarrierTransitionComparison` | 2026-09-07 02:46:09 |

The endpoint proof's intermediate diagnostics were resolved by an
absurd dependent function, the existing proposition-to-set lemma, and
separate omitted/selected coordinate signatures with explicit boundary
types. No memory-guard stop occurred. No incomplete Agda source from
this continuation remains.

Files are saved in the working tree. This pause does not create a Git
commit; the broader real-homotopy/sphere development was already
untracked when this continuation began.
