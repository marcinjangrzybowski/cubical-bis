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

Move the endpoint/middle `Fin` eliminator (`ElimFinSS` and its computation
lemmas) out of `Calculus.Integration.Summation` into `Data.Fin.Properties`.
Retain compatibility names and check `Partition.Base` plus the `Calculus`
facade before migrating its consumers to the canonical import.

## Phase 1: ordered algebra structure

Status: ordered-ring instance completed; broader theorem migration and the
Archimedean instance remain.

Proposed internal organization:

```text
Cubical/HITs/CauchyReals/Algebra/Order/
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
- Move genuinely missing utilities such as endpoint/middle Fin elimination to
  `Data.Fin.Properties`; do not keep them in integration modules.
- Remove local natural-power laws when the semiring exponent laws suffice.

### Rational infrastructure

- [x] Centralize the three copies of `invℚ₊-fromNat` in the rational inverse
  ordered-algebra API.
- [x] Centralize the five copies of `ℚ≤→<+₊` in
  `Cubical.Data.Rationals.Order.Algebra`.
- [x] Replace `ℚ^ⁿ-dist·` with the generic commutative-ring exponent law.
- [x] Generalize the duplicated rational/real `^ⁿ-even` and `^ⁿ-odd` laws in
  `CommRing.Properties.Exponentiation`.
- [ ] Generalize or deduplicate `-1ⁿ`, `-1ⁿ·`, and their absolute-value laws.
- Move rational arithmetic helpers such as `ℚmax-min-minus`, `m·n/m`, and
  `ℚabs-abs≤abs-` to the rational modules when no generic result exists.

### Dead or empty modules

- [x] Remove `Analysis.Sequence.Lipschitz`; it was an import-only module and
  has no intended facade role.

## Phase 3: positive and nonnegative elements

Status: compatibility layer established; operation migration remains.

Current `ℝ₊`, `ℝ₀₊`, their equality/set proofs, and their operations duplicate
the `Positive`, `NonNegative`, and `PositiveHalves` modules in
`Cubical.Algebra.OrderedCommRing.Properties`.

After `ℝOrderedCommRing` exists:

- [x] Expose the generic positive and nonnegative subtypes for `ℝ`.
- [x] Verify that the existing `ℝ₊` and `ℝ₀₊` are definitionally equal to the
      generic subtypes, allowing compatibility names to be preserved.
- [ ] Replace `_₊+ᵣ_`, `_₊·ᵣ_`, `_₊^ⁿ_`, and nonnegative operations with the
      generic structures.
- [ ] Keep inverse/division on positive reals in a field/inverse-specific
      module until an appropriate generic ordered-field abstraction exists.

## Phase 4: generic ordered-ring theory

Status: pending.

### Arithmetic and absolute values

Move or replace the following families with `OrderedCommRing.Properties`:

- additive and multiplicative monotonicity;
- addition/subtraction rearrangement equivalences;
- negation order reversal and half-line equivalences;
- square nonnegativity and square/absolute-value identities;
- triangle and reverse-triangle inequalities;
- cancellation equivalences such as `x + y ≤ z + y ≃ x ≤ z`.

### Powers

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

Status: pending.

Split this work by required structure:

- Define clamp itself and its lattice membership/monotonicity laws in a
  generic pseudolattice/order module.
- Put translation and nonexpansiveness/distance laws in ordered-ring theory.
- Reuse or extend `Relation.Binary.Order.Poset.Interval` instead of maintaining
  real-only `intervalℙ`, `ointervalℙ`, and half-open predicate constructors.
- Express `IsNondecreasingOn` through the order on a predicate subtype and the
  existing `IsIsotone`; add a generic strict analogue for
  `IsStrictlyIncreasingOn` if needed.
- Retain continuity of real clamp as the Cauchy-real adapter.

## Phase 6: rational series and approximation helpers

Status: pending.

- Move the rational part of `Analysis.Sequence.AlternatingSeries` to a module
  such as `Cubical.Data.Rationals.Series.Alternating`.
- Leave only the Cauchy-real convergence/lifting adapter under
  `CauchyReals.Analysis.Sequence`.
- Move rational restricted-Lipschitz predicates from
  `Approximation.Bisection` to rational premetric/order modules, or express
  them through the generic premetric mappings API.
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
