# Cauchy real generality and module refactor plan

This is the living plan for moving definitions that are not intrinsically
about the Cauchy-real higher inductive type into reusable algebra, order, data,
and premetric modules. It also records the internal dependency cleanup needed
before those moves can be made safely.

## Baseline

- Audit date: 2026-07-15
- Implementation started: 2026-07-16
- Baseline commit: `1108d5441` (`Refactor Cauchy real module hierarchy`)
- Audited scope: all 162 Agda files below `Cubical/HITs/CauchyReals`
- User-facing import policy: layered facades

The existing public facade modules should continue to work while definitions
are moved. Compatibility aliases and reexports may temporarily preserve old
names, but new implementation modules should depend directly on the canonical
general modules.

## Architectural diagnosis

The main blocker is that the existing commutative-ring and order structures on
`ℝ` are not assembled into an `OrderedCommRing`. As a result, generic facts
about positive elements, ordered arithmetic, absolute values, powers, finite
sums, and clamp operations are reproved under Cauchy-real-specific names.

The first dependency-unlocking goal is therefore to provide:

```text
Cubical.HITs.CauchyReals.Algebra.Order.Instance
  ℝOrderedCommRing : OrderedCommRing _ _
```

An `ℝArchimedeanRing` instance should follow later. It is useful for the
premetric migration, but it is not a prerequisite for the basic ordered-ring
cleanup.

## Rules for the migration

1. Preserve the layered public facades while implementation paths change.
2. Separate moves from generalizations:
   - use an existing generic theorem when one already exists;
   - otherwise first isolate the current theorem, then generalize it;
   - keep a Cauchy-real adapter only when it adds real-specific content.
3. Avoid introducing import cycles merely to obtain a generic instance.
4. Keep HIT constructors, eliminators, closeness, rational density adapters,
   Cauchy-limit constructions, and analytic continuity proofs under
   `CauchyReals`.
5. Make small Agda edits and check every changed Agda file with `agda-codex`.
6. Record completed moves and any changed destination in this document.

## Current next slice

Extract `Lipschitz-ℚ→ℚℙ`, `Lipschitz-ℚ→ℚℙ<`, and their conversion theorem
from `CauchyReals.Approximation.Bisection` into a focused
`Cubical.Data.Rationals.Analysis.Lipschitz` module with a layered
`Cubical.Data.Rationals.Analysis` facade. Retain compatibility reexports from
the old path and leave the rational-to-real Lipschitz bridges under
`CauchyReals`. A direct rational module is the bounded next step because the
generic premetric layer currently lacks the standard-rational instance and
predicate-subspace mapping support needed for a faithful generic alias.

## Phase 1: ordered algebra structure

Status: ordered-ring instance completed; broader theorem migration and the
Archimedean instance remain.

Proposed internal organization:

```text
Cubical/HITs/CauchyReals/Algebra/
  Ring.agda
  Order/
    Addition.agda
    AbsoluteValue.agda
    Apartness.agda
    Multiplication.agda
    Instance.agda
    Properties.agda
    Positive.agda
    Archimedean.agda
```

Work items:

- [x] Inventory the exact `IsOrderedCommRing` fields and their current proofs.
- [x] Isolate or prove the missing strict-order compatibility fields.
- [x] Define `ℝOrderedCommRing` without broad API changes.
- [x] Reexport the instance from the appropriate algebra facade.
- [x] Move the `Rℝ` ring-structure/theory namespace out of `Inverse` and
      migrate its direct consumers to the canonical module.
- [ ] Move ordinary ordered-ring lemmas out of `Continuity.Base` and
      `Inverse` or replace them with generic theorem aliases.
- [ ] Later define `ℝArchimedeanRing` and move applicable bounds into
      `ArchimedeanRing.Properties`.

Known ingredients already present include `ℝcommRing`, `isPosetℝ`, strict
order transitivity and irreflexivity, lattice laws, additive monotonicity,
multiplicative monotonicity on nonnegative/positive factors, and `0 < 1`.
The previously missing weak linearity, `≤ ≃ ¬ >`, and positive-sum
decomposition fields now live in `Algebra.Order.Properties`.

## Phase 2: exact duplicate removal

Status: in progress.

These changes should reuse existing library definitions rather than move the
local implementations verbatim.

### Fin and natural-number infrastructure

- [x] Replace `injectFin+`, `injectFin+'`, `Fin+→⊎`, `Iso-Fin+⊎`, and their
  compatibility proofs with `Data.Fin.Properties.Fin+≅Fin⊎Fin`,
  `Iso-Fin⊎Fin-Fin+`, or `Data.Fin.Recursive.Properties.sumIso`.
- [ ] Replace `Fin^2·` with `factorEquiv` or `Iso-Fin×Fin-Fin·`. The generic
  `factorEquiv` uses the opposite coordinate significance; preserve the local
  indexing until an explicit compatibility path is supplied.
- [x] Replace local parity machinery `_∣2` and `∣2-cases` with
  `Data.Nat.IsEven`.
- [x] Move genuinely missing utilities such as endpoint/middle Fin elimination
  to `Data.Fin.Properties`; do not keep them in integration modules.
- Remove local natural-power laws when the semiring exponent laws suffice.

### Rational infrastructure

- [x] Centralize the three copies of `invℚ₊-fromNat` in the rational inverse
  ordered-algebra API.
- [x] Centralize the five copies of `ℚ≤→<+₊` in
  `Cubical.Data.Rationals.Order.Algebra`.
- [x] Replace `ℚ^ⁿ-dist·` with the generic commutative-ring exponent law.
- [x] Generalize the duplicated rational/real `^ⁿ-even` and `^ⁿ-odd` laws in
  `CommRing.Properties.Exponentiation`.
- [x] Generalize or deduplicate `-1ⁿ`, `-1ⁿ·`, and their absolute-value laws.
- [x] Move rational arithmetic helpers such as `ℚmax-min-minus`, `m·n/m`, and
      `ℚabs-abs≤abs-` to generic ordered-ring or rational modules, retaining
      the Cauchy-real names as compatibility aliases.

### Dead or empty modules

- [x] Remove `Analysis.Sequence.Lipschitz`; it was an import-only module and
  has no intended facade role.

## Phase 3: positive and nonnegative elements

Status: subtype and operation compatibility layers established; inverse and
division remain at the field-specific boundary.

Current `ℝ₊`, `ℝ₀₊`, their equality/set proofs, and their operations duplicate
the `Positive`, `NonNegative`, and `PositiveHalves` modules in
`Cubical.Algebra.OrderedCommRing.Properties`.

After `ℝOrderedCommRing` exists:

- [x] Expose the generic positive and nonnegative subtypes for `ℝ`.
- [x] Verify that the existing `ℝ₊` and `ℝ₀₊` are definitionally equal to the
      generic subtypes, allowing compatibility names to be preserved.
- [x] Replace `_₊+ᵣ_`, `_₊·ᵣ_`, and `_₊^ⁿ_` with the generic positive-real
      operations after untangling their former dependency on `Inverse`.
- [x] Replace the nonnegative addition and multiplication implementations in
      `RationalPower.Core` and the nonnegative power implementation in
      `Roots.NonNegative` with `NonNegativeReals` operations.
- [x] Migrate internal consumers to the canonical nonnegative operations while
      retaining the existing operator spellings at compatibility boundaries.
- [ ] Keep inverse/division on positive reals in a field/inverse-specific
      module until an appropriate generic ordered-field abstraction exists.

## Phase 4: generic ordered-ring theory

Status: in progress.

### Arithmetic and absolute values

Move or replace the following families with `OrderedCommRing.Properties`:

- additive and multiplicative monotonicity;
- addition/subtraction rearrangement equivalences;
- negation order reversal and half-line equivalences;
- square nonnegativity and square/absolute-value identities;
- triangle and reverse-triangle inequalities;
- cancellation equivalences such as `x + y ≤ z + y ≃ x ≤ z`.
- [x] Add the generic reverse-triangle inequality and the negation De Morgan
      law for joins and meets; expose the rational `max`/`min` spelling from
      rational order algebra.

### Powers

- [x] Add generic positive/nonnegative power preservation and power operations
      on the corresponding ordered-ring subtypes.
- Put purely commutative-ring power laws in `CommRing.Properties`.
- Put power positivity and monotonicity on nonnegative elements in ordered-ring
  power theory.
- Put reflection/cancellation results in a stronger cancellative or
  Archimedean layer when `OrderedCommRing` alone is insufficient.
- Keep continuity of real powers in `CauchyReals`.

### Finite sums

- Standardize integration on the existing `FinVec`/big-operator API where
  possible.
- Put algebraic fold laws in `Semiring.BigOps` or `Ring.BigOps`.
- Put finite-sum monotonicity, positive-summand existence, and absolute-value
  bounds in ordered-ring big-operator theory.
- [x] Move the generic finite-logic theorem `Fin-∀A⊎∃B` to
  `Data.Fin.Properties`.

## Phase 5: clamp, intervals, and subset mappings

Status: completed.

Split this work by required structure:

- [x] Isolate the clamp endpoint and monotonicity lemmas from
      `Algebra.Inverse` in `Analysis.Continuity.Clamp`, retain compatibility
      reexports, and migrate the focused symmetric-arcsine consumer.
- [x] Move the remaining interval-membership and distance adapters from
      `Algebra.Inverse` into the focused clamp module and migrate their direct
      consumers.
- [x] Define clamp itself and its lattice membership/monotonicity laws in a
      generic pseudolattice/order module, and adapt the real lemmas to it.
- [x] Put translation and nonexpansiveness/distance laws in ordered-ring
      theory.
- [x] Reuse `Relation.Binary.Order.Poset.Interval` for the closed `intervalℙ`
      predicate, its subtype equivalence, and endpoint-monotone containment.
- [x] Generalize `ointervalℙ` and the half-open predicates in the weakest
      sufficient strict-order layer, `Quoset.Interval`.
- [x] Express `IsNondecreasingOn` through the order on a predicate subtype and
      the existing `IsIsotone`; add a generic strict analogue for
      `IsStrictlyIncreasingOn`.
- Retain continuity of real clamp as the Cauchy-real adapter.

## Phase 6: rational series and approximation helpers

Status: in progress; the rational alternating-series layer is complete and
the restricted-Lipschitz extraction is next.

- [x] Move the alternating-sign predicates, parity helpers, partial-sum
      bounds, and rational Cauchy estimate from
      `Analysis.Sequence.AlternatingSeries` to
      `Cubical.Data.Rationals.Series.Alternating`.
- [x] Move the rational magnitude-to-signed-series constructor to the same
      rational module.
- [x] Leave only the Cauchy-real convergence/lifting adapters under
      `CauchyReals.Analysis.Sequence`.
- [ ] Move rational restricted-Lipschitz predicates from
      `Approximation.Bisection` to rational premetric/order modules, or
      express them through the generic premetric mappings API.
- Keep the Cauchy-real inverse-bisection construction and recovery machinery
  under `CauchyReals.Approximation`.

## Phase 7: premetric migration

Status: blocked by the ordered/Archimedean structure work.

`Analysis.Metric.Base` duplicates much of `Cubical.Relation.Premetric`, which
already provides continuous, uniformly continuous, Lipschitz, nonexpanding,
and isometric maps together with composition and categories.

- [ ] Construct or obtain the real premetric instance, preferably through
      `ArchimedeanRing→PremetricSpace`.
- [ ] Migrate Cauchy-real metric consumers to `Relation.Premetric`.
- [ ] Add generic subspace/product support there only if genuinely missing.
- [ ] Keep real-root p-norm mathematics under `CauchyReals`, while moving
      generic product-space mapping facts out of `PNorm`.
- [ ] Delete the parallel `MetricSpace`, `UContMap`, and `IsIsometry` hierarchy
      after compatibility users have migrated.

## Phase 8: optional broader abstractions

Status: deferred.

- Generalize `pasteAt`, `pasteAbove`, and `pasteAboveClosed` over a
  lattice-ordered domain and an additive-group codomain if another consumer
  appears.
- Move additive-automorphism infrastructure out of exponentiation so analysis
  does not import `RealPower.Infrastructure` for basic group structures.
- Move the expression-lifting tactic to a tactic-oriented namespace if it
  remains specific to the rational embedding into Cauchy reals.

These are lower priority because they do not currently block the main import
cleanup.

## Definitions that should remain Cauchy-real-specific

- the Cauchy-real HIT, eliminators, and closeness construction;
- the rational embedding and theorems specifically relating it to this HIT;
- Cauchy sequence limits and real completeness adapters;
- real continuity proofs and analytic constructions;
- inverse, root, exponential, logarithmic, trigonometric, and calculus results
  after their generic algebraic helper lemmas have been removed;
- rational-density statements whose exact conclusion mentions the Cauchy-real
  embedding, unless the library first gains an appropriate ordered-field
  abstraction.

## Progress log

- 2026-07-15: completed the full-folder audit and identified the missing
  ordered-ring instance as the central dependency issue.
- 2026-07-15: committed the preceding hierarchy refactor as `1108d5441`.
- 2026-07-16: created this living plan and started Phase 1.
- 2026-07-16: added the `Algebra.Order` hierarchy, assembled
  `ℝOrderedCommRing`, and exposed generic positive/nonnegative real modules.
- 2026-07-16: moved order-only dichotomy and order-negation results out of
  `Analysis.Sequence.Base` into `Algebra.Order.Properties`, retaining public
  compatibility reexports.
- 2026-07-16: removed the empty `Analysis.Sequence.Lipschitz` module.
- 2026-07-16: centralized `ℚ≤→<+₊` in rational ordered algebra and retained
  the old logarithm-sequence names as compatibility aliases.
- 2026-07-16: centralized `invℚ₊-fromNat` in `Data.Rationals.Inverse` and
  retained its three Cauchy-real names as compatibility aliases.
- 2026-07-16: checked every changed Agda module plus the `Algebra`, `Sequence`,
  `Exponentiation`, and `Calculus` facades with no holes, metas, constraints,
  or warnings.
- 2026-07-16: committed that checkpoint as `83ae5ce84`.
- 2026-07-16: replaced the integration-local `Fin` sum splitter, injections,
  isomorphism, and recursive inverse proofs with `Fin+≅Fin⊎Fin`; retained all
  compatibility names and checked `Summation`, `Partition.Concatenation`, and
  `Calculus`.
- 2026-07-16: moved the modulo-two decomposition behind `_∣2` and
  `∣2-cases` to `Data.Nat.IsEven` and retained compatibility aliases in
  `AlternatingSeries`.
- 2026-07-16: replaced the local `ℚ^ⁿ-dist·` induction in `Trigonometry.Pi`
  with the generic commutative-ring exponentiation theorem.
- 2026-07-16: generalized `^ⁿ-even` and `^ⁿ-odd` as `^-even` and `^-odd` in
  `CommRing.Properties.Exponentiation`; the rational and real names are now
  compatibility aliases.
- 2026-07-16: moved `Fin-∀A⊎∃B` to `Data.Fin.Properties`, generalized its
  universe levels, and retained the old `Derivative.MeanValue` name.
- 2026-07-16: committed that checkpoint as `42eb22e7a`.
- 2026-07-16: moved `ElimFinSS`, `go-tail-finj`, and `go-tail-flast` from
  integration summation to `Data.Fin.Properties`, generalized the carrier
  universe, retained the old `Summation` reexport, and migrated
  `Partition.Base` to the canonical `Data.Fin` import.
- 2026-07-16: added generic alternating-sign iteration, ring-homomorphism
  preservation, and ordered-ring absolute-value laws; rational and Cauchy-real
  sign APIs now use aliases or thin rational-embedding adapters.
- 2026-07-16: committed the endpoint-elimination and alternating-sign batch as
  `3e1689f53`.
- 2026-07-16: added generic `abs-abs≤abs-` and `joinNeg≡negMeet`; exposed the
  rational `maxNeg≡negMin` spelling, generalized denominator cancellation as
  `[c/1]·[n/c]≡[n/1]`, retained the three Cauchy-real compatibility names, and
  migrated the real-power consumer to the rational API.
- 2026-07-16: added generic positive/nonnegative power preservation and
  subtype powers; changed the nonnegative real addition, multiplication, and
  power operators to compatibility aliases, and removed a proof-relevant
  unfolding of nonnegative power from the root/power equivalence proof.
- 2026-07-16: checked every changed Agda module plus the `Algebra`,
  `Exponentiation`, `NthRoot`, and `Calculus` facades with no holes, metas,
  constraints, or warnings.
- 2026-07-16: committed the ordered/rational and first nonnegative-operation
  batch as `01594118c`.
- 2026-07-16: removed five dead Circle imports of `RationalPower.Core`, changed
  `Metric.Discrete` to use `NonNegativeReals._+₀₊_` directly, and migrated
  `Metric.PNorm` to the canonical `_+₀₊_`, `_·₀₊_`, and `_^₀₊_` notation.
  All changed modules and the `Circle` facade checked cleanly.
- 2026-07-17: committed the nonnegative-operation consumer migration as
  `6574f4d1d`.
- 2026-07-17: split real-specific ordered addition and multiplication lemmas
  out of `Algebra.Inverse` into `Algebra.Order.Addition` and
  `Algebra.Order.Multiplication`; moved strict-order irreflexivity to
  `Algebra.Order.Properties`. This removed the `Inverse` dependency from the
  ordered-ring instance, properties, and positive/nonnegative subtype layer.
- 2026-07-17: changed `Inverse._₊+ᵣ_`, `_₊·ᵣ_`, and `_₊^ⁿ_` into
  compatibility aliases for `PositiveReals`, adapting the few root and
  rational-power proofs that observed proof-carrying subtype values.
- 2026-07-17: checked every changed Agda module plus the `Algebra`,
  `Exponentiation`, `NthRoot`, `Calculus`, and `Circle` facades with no holes,
  metas, constraints, or warnings.
- 2026-07-17: committed the ordered-addition, ordered-multiplication, and
  positive-operation extraction as `2c9394ff6`.
- 2026-07-17: migrated the order-only `Inverse` imports in `Algebra.Power.Order`,
  `Metric.Discrete`, `Approximation.InverseLipschitz`, `RealPower.BaseOrder`,
  and `Circle.Base` to the new order modules. Removed a dead import from
  `ArcSin.Symmetric.Base` and narrowed the symmetric rational module to its
  single remaining clamp-helper dependency.
- 2026-07-17: the import audit identified `Rℝ`, a general ring-theory namespace
  currently declared in `Algebra.Inverse`, as the next major source of
  unrelated inverse dependencies.
- 2026-07-17: checked all seven changed Agda modules plus the `Algebra`,
  `Exponentiation`, `ArcSin`, and `Circle` facades with no holes, metas,
  constraints, or warnings.
- 2026-07-17: committed the order-only inverse-import migration as
  `ef367b5ae`.
- 2026-07-17: introduced `Algebra.Ring`, moved the `Rℝ` namespace there, and
  reexported it through both `Algebra` and `Algebra.Inverse` for layered and
  backwards-compatible imports.
- 2026-07-17: replaced the real-specific continuity proof of
  `-ᵣ≡[-1·ᵣ]` with the generic ring theorem plus the rational `-1` adapter,
  and moved the compatibility theorem to `Algebra.Ring`.
- 2026-07-17: migrated `Algebra.Signs`, integration summation, two circle-angle
  modules, and `RealPower.CalculusProof` to the canonical ring import. The
  first-quadrant module now lists its two remaining `Inverse` helpers
  explicitly.
- 2026-07-17: checked all eight changed Agda modules plus the `Algebra`,
  `Calculus`, `Exponentiation`, and `Circle` facades with no holes, metas,
  constraints, or warnings.
- 2026-07-17: committed the `Algebra.Ring` extraction and its consumer
  migrations as `0894f45e3`.
- 2026-07-17: split absolute-value and apartness prerequisites out of
  `Algebra.Inverse` into `Algebra.Order.AbsoluteValue` and
  `Algebra.Order.Apartness`, retaining compatibility reexports through both
  `Algebra.Order` and `Algebra.Inverse`.
- 2026-07-17: migrated `Analysis.Continuity.Apart` and
  `Circle.Angle.FirstQuadrant` from the inverse implementation to the focused
  order modules; selected clamp isolation as the next implementation slice.
- 2026-07-17: checked all six changed Agda modules plus the `Algebra`,
  `ArcSin`, `Calculus`, `Exponentiation`, and `Circle` facades with no holes,
  metas, constraints, or warnings.
- 2026-07-17: committed the absolute-value/apartness extraction as
  `3d520a037`.
- 2026-07-17: introduced `Analysis.Continuity.Clamp`, moved the endpoint and
  monotonicity lemmas out of `Algebra.Inverse`, retained compatibility
  reexports, exposed the module through the layered `Analysis` facade, and
  migrated `ArcSin.Symmetric.Properties.Rational` to the canonical import.
- 2026-07-17: checked all four changed Agda modules plus the `Algebra`,
  `ArcSin`, and `Calculus` facades with no holes, metas, constraints, or
  warnings.
- 2026-07-18: committed the first clamp extraction as `74289b4a2`.
- 2026-07-18: moved real clamp interval membership and the rational-endpoint
  distance adapter into `Analysis.Continuity.Clamp`; introduced the clearer
  canonical names `clampᵣ∈intervalℙ` and `clampDistᵣ-rat`, while retaining
  `clampᵣ∈ℚintervalℙ` and `clampDistᵣ'` as compatibility aliases through
  `Algebra.Inverse`.
- 2026-07-18: replaced the duplicate bisection membership proof with a
  compatibility alias, migrated every implementation consumer to the
  canonical clamp names, and removed the `Algebra.Inverse` dependency from
  `Analysis.Continuity.Order`, `ArcSin.Symmetric.Properties.Inverse`, and
  `Calculus.Integration.Uniform`.
- 2026-07-18: checked all eleven changed Agda modules plus the `Algebra`,
  `Analysis`, `Approximation`, `ArcSin`, `Calculus`, and `Exponentiation`
  facades with no holes, metas, constraints, or warnings.
- 2026-07-18: committed the completed Cauchy-real clamp extraction as
  `cb582322e`.
- 2026-07-18: introduced `Relation.Binary.Order.Pseudolattice.Clamp` with a
  generic clamp, meet/join isotonicity, endpoint laws, and interval
  membership; exposed it through the layered pseudolattice facade and based
  the real endpoint and monotonicity lemmas on `ℝ≤Pseudolattice`.
- 2026-07-18: retained the established pair-valued implementation of
  `clampᵣ∈intervalℙ` because a dependent calculus consumer relies on its
  definitional proof term; the generic `Interval` theorem remains available
  without changing that compatibility boundary.
- 2026-07-18: checked both changed clamp modules plus the `Pseudolattice`,
  `OrderedCommRing`, `Algebra`, `Analysis`, `Approximation`, `ArcSin`,
  `Calculus`, and `Exponentiation` facades and the dependent fundamental
  theorem, with no holes, metas, constraints, or warnings.
- 2026-07-18: committed the generic pseudolattice clamp checkpoint as
  `2644a61df`.
- 2026-07-18: introduced `Algebra.OrderedCommRing.Clamp` with additive
  translation of joins, meets, and clamp, a one-sided clamp difference bound,
  and full absolute-value nonexpansiveness without an order-case split.
- 2026-07-18: replaced the rational quotient-level distribution and clamp
  proofs with ordered-ring instance aliases, and specialized the generic
  distance theorem through `ℝOrderedCommRing`; `Analysis.Uniform` now
  reexports the focused real theorem instead of reconstructing it by
  continuity lifting.
- 2026-07-18: checked all five changed Agda modules, every direct rational
  clamp-distance/distribution consumer, and the `Algebra`, `Analysis`,
  `Approximation`, `ArcSin`, `Calculus`, and `Exponentiation` facades with no
  holes, metas, constraints, or warnings.
- 2026-07-18: committed the ordered-ring clamp translation and
  nonexpansiveness batch as `dcb97c611`.
- 2026-07-18: extended `Relation.Binary.Order.Poset.Interval` with a
  universe-polymorphic closed-interval predicate, its subtype equivalence,
  point-interval contractibility, and endpoint-monotone containment.
- 2026-07-18: moved `ℝ≤Poset` down to `Foundation.Order.Base` (with a
  compatibility reexport from `Algebra.Order.Instance`) and defined the
  Cauchy-real `intervalℙ` and containment lemma through the generic layer.
  The established real point-interval proof remains unchanged for dependent
  consumers that observe its proof term.
- 2026-07-18: updated `Poset.Covering` to the current `Iso.sec`/`Iso.ret`
  field names while validating direct users of the generic interval module.
- 2026-07-18: checked all four changed Agda modules, the focused clamp,
  multiplication, and integration consumers, and the `Algebra`, `Analysis`,
  `Approximation`, `ArcSin`, `Calculus`, and `Exponentiation` facades with no
  holes, metas, constraints, or warnings.
- 2026-07-18: committed the generic closed-interval predicate bridge as
  `a90518a70`.
- 2026-07-18: introduced `Relation.Binary.Order.Quoset.Interval` with
  universe-polymorphic open and half-open predicates plus containment and
  open/closed weakening laws for compatible strict and nonstrict orders. The
  module is reexported through the layered `Quoset` facade.
- 2026-07-18: added the foundational `ℝ<Quoset` instance and expressed
  `ointervalℙ`, `pred≤<`, `pred<≤`, and all existing generic interval
  inclusions through the new order-only layer without changing their
  pair-valued membership API.
- 2026-07-18: checked all four changed Agda modules, six representative
  proof-sensitive interval consumers, and the `Algebra`, `Analysis`,
  `Approximation`, `ArcSin`, `Calculus`, `Circle`, and `Exponentiation`
  facades with no holes, metas, constraints, or warnings.
- 2026-07-18: committed the generic open/half-open interval layer as
  `2e45bdeec`.
- 2026-07-18: added universe-polymorphic `PredicatePoset` and
  `PredicateQuoset` constructors, plus a new `Quoset.Mappings` layer with
  `IsStrictlyIsotone`, composition, and proposition proofs.
- 2026-07-18: added the dependent `IsIsotoneOn` and
  `IsStrictlyIsotoneOn` APIs and equivalences to the corresponding mapping
  records on `uncurry f` over predicate subtypes.
- 2026-07-18: changed the Cauchy-real `IsNondecreasingOn` and
  `IsStrictlyIncreasingOn` definitions into generic aliases while preserving
  their original callable dependent-function shape; the existing real-power
  proofs required no source changes.
- 2026-07-18: checked all six changed Agda modules, the layered `Quoset`
  facade, the unchanged real-power construction, and the `Analysis` and
  `Exponentiation` facades with no holes, metas, constraints, or warnings.
- 2026-07-18: committed the generic predicate-subtype monotonicity layer as
  `e51a07750`.
- 2026-07-18: introduced `Data.Rationals.Series.Alternating` for the rational
  alternating-sign predicates, parity decomposition, partial-sum bounds, and
  `cauchyByAlt` estimate, and exposed it through the focused
  `Data.Rationals.Series` facade.
- 2026-07-18: reduced the old Cauchy-real alternating-series module to a
  compatibility wrapper around the rational theorem module plus the existing
  `rat`-lifting and magnitude-series adapters.
- 2026-07-18: checked both new rational series modules, the compatibility
  module, and the `Sequence` and `Analysis` facades with no holes, metas,
  constraints, or warnings.
- 2026-07-18: committed the first rational alternating-series extraction as
  `5649e8614`.
- 2026-07-18: moved the magnitude-to-signed-series construction into
  `Data.Rationals.Series.Alternating`, separating its strict-decrease
  assumption from the convergence modulus accepted by `terms→0`.
- 2026-07-18: reduced the old `AlternatingFromMagnitudes` module to public
  compatibility aliases plus the Cauchy-real partial-sum lifting result; the
  old alternating-series implementation now contains only Cauchy-real
  adapters around the rational API.
- 2026-07-18: checked the rational alternating module and facade, the old
  compatibility module, and the Cauchy-real `Sequence` and `Analysis` facades
  with no holes, metas, constraints, or warnings.
