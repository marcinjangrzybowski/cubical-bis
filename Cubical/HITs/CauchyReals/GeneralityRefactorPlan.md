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
- User-facing import policy: layered canonical facades; the legacy metric API
  was explicitly retired on 2026-07-23

Canonical public facade modules should continue to work while definitions are
moved. Compatibility aliases and reexports may temporarily preserve old names,
but new implementation modules should depend directly on canonical general
modules. The former real-valued `MetricSpace`/`UContMap` hierarchy and its
specialized compatibility packaging are an explicit exception: their modules,
names, and facade exports have been retired.

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

1. Preserve layered canonical public facades while implementation paths change;
   do not restore the explicitly retired legacy metric hierarchy.
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

The premetric migration is complete. The parallel real-valued metric hierarchy,
its old `Analysis.Metric.Base` facade, and the discrete, p-norm, and circle
compatibility packaging have been deleted. `Metric`, `PNorm`, `Discrete`, and
`Circle.Metric` now expose only their canonical premetric or real-mathematics
layers.
The first four Phase 1 arithmetic slices are complete: additive cancellation,
negation/difference characterizations, additive rearrangements, and
rational-factor multiplication monotonicity now live in generic or focused
ordered-ring modules, with compatibility reexports from `Algebra.Inverse`.
The `Analysis.Continuity.Base` dependency split needed by the ordered-ring
instance is complete:
`Analysis.Continuity.Core` contains the dependency-light continuity and
extensionality kernel, while `Algebra.Order.Addition.Base` owns additive
identities, nonstrict translation, and negation order reversal,
`Algebra.Order.Addition.Strict` owns the rational-approximation support and
strict translation proofs, and
`Algebra.Order.Lattice` owns the min/max identities and bounds needed by the
ordered-ring instance. The old continuity path publicly reexports all these
names, while `Algebra.Order.Instance` now imports only the focused addition and
lattice modules and has no `Continuity.Base` dependency. The Archimedean bound
audit is also complete: `ArchimedeanRingTheory.∃ι₊₁Larger` gives every element
a positive embedded-natural upper bound, while the rational Cauchy-real
specializations live with `ℝArchimedeanRing`. The rational-density witness
`<ᵣ→Δ` now has the dependency-light real-specific home
`Foundation.Order.Density`; the interval and unit-fraction facts remain in
`Foundation.Order.Bounds`, which preserves the old bound imports. The audit of
the remaining ordinary ordered-ring lemmas formerly defined in
`Analysis.Continuity.Base` and `Algebra.Inverse` is complete; only statements
whose proofs do not depend on Cauchy-real density, continuity, or inverse data
were moved.
The multiplication-side continuity split is now complete as well:
`Analysis.Continuity.Predicate` owns predicate-indexed continuity, open-domain
combinators, and open-interval extensionality, `Continuity.Core` owns
`cont₂+ᵣ`, and `Algebra.Multiplication` imports those focused modules directly.
`Continuity.Base` publicly reexports the extracted API for compatibility.
The first such family is now extracted: negation continuity lives in
`Analysis.Continuity.Core`, while `Algebra.Order.AbsoluteValue` owns the
triangle inequalities, comparison with lattice absolute value, sign
simplifications, and zero reflection formerly split between broad continuity
and inverse. The old paths retain compatibility reexports. The seven additive
rearrangement implications `a<b-c⇒c<b-a`, `a≤b-c⇒c≤b-a`,
`a<b-c⇒a+c<b`, `a+c<b⇒a<b-c`, `a-b<c⇒a-c<b`, `x<y→0<y-x`, and
`a-b<c⇒a<c+b` are now direct `ℝOrderedCommRing` specializations in
`Addition.Properties`. Their pre-instance implementations remain under
explicit `-bootstrap` names in `Addition.Base` and `Addition.Strict` for the
few modules below the ordered-ring instance. The new `Addition.Bootstrap`
module isolates the additional translation, positivity, cancellation, and
difference helpers required on that side of the boundary. Removing the unused
`Continuity.Base` import from the specialized real commutative-ring solver
closed the last hidden cycle, so the focused addition facade and old
continuity path now reexport the canonical instance-backed declarations.
The four negation-induced half-line isomorphisms and their four function-space
lifts are now generic `negHalfLine...Iso` theorems. Their established real
spellings live in `Addition.Base`, remain available through the old continuity
path, and are imported from the focused owner by their sole external consumer.
The four `ℝ₊`/`ℝ₀₊` min/max subtype constructors now live in
`Algebra.Order.Lattice` and remain available through `Continuity.Base`.
Positive maximum and both nonnegative operations mirror generic subtype
lattice operations; positive minimum retains its real-specific,
dependency-light proof because the generic layer does not furnish a strictly
positive meet. Generic ordered-ring theory now provides
`abs-monotoneOnNonNeg`, while the established
`absᵣ-monotoneOnNonNeg` spelling lives in `Algebra.Order.AbsoluteValue`,
remains available through `Continuity.Base`, and is imported from the focused
owner by its sole direct consumer. The real theorem retains its
dependency-light transport proof because its owner precedes
`ℝOrderedCommRing` in the bootstrap graph. Generic pseudolattice theory now
provides coordinatewise `∧Monotone` and `∨Monotone`, exposed from ordered-ring
theory as `⊓Monotone` and `⊔Monotone`. The established `minMonotoneᵣ` and
`maxMonotoneᵣ` proofs live in `Algebra.Order.Lattice`, remain available through
`Continuity.Base`, and are imported from the focused owner by their two
external consumers. The positive-domain monotone-image bounds `incr→max≤` and
`incr→≤min` now live there as well, remain available through the old continuity
path, and are imported from the focused owner by their sole external consumer.
They remain paired real-specific adapters because the generic positive subtype
has no meet operation. Generic ordered-ring theory now provides the stronger
join-minus-meet identity `abs≡⊔-⊓`. The established rational helper and
`absᵣ-min-max` now live in `Algebra.Order.AbsoluteValue`, remain available
through `Continuity.Base`, and are imported from the focused owner by all four
direct consumers. The former rational-series proof of the same generic theorem
is now a compatibility alias. The real continuity proof remains
dependency-light rather than using `ℝOrderedCommRing`, and the binary
continuity/extensionality combinators it needs now live in
`Analysis.Continuity.Core`. Generic ordered-ring theory now also provides
coordinatewise `·Mono≤`, `·Mono<`, `·Mono<≤`, and `·Mono≤<`, plus
`≤→<SumLeftPos`. Their real specializations live in the new post-instance
`Algebra.Order.Multiplication.Properties` module and in
`Addition.Properties`; `Inverse` only reexports the established names.
Positive/nonnegative power preservation moved to the multiplication properties
module in the same way. Finally, `denseℝ` now lives in
`Algebra.Order.Density` as a specialization of the generic midpoint theorem.
The continuing `Inverse` audit has also moved negation preservation of
apartness plus the open nonzero predicate to `Algebra.Order.Apartness`, and
moved the real sign function, its open-domain continuity, and its
absolute-value identities to `Algebra.Signs`; `Inverse` remains a compatibility
reexport. The general predicate-continuity comparison `≤ContWP` and its two
nonzero-domain bounded variants now live in `Analysis.Continuity.Order`.
The established positive addition, multiplication, and power spellings now
live with the generic operations in `Algebra.Order.Positive`, while
`Foundation.Rationals` owns the compatibility alias `ℚmax-min-minus`.
Generic ordered-ring theory now also provides positive-factor nonstrict
multiplication equivalences `·MonoL≤≃` and `·MonoR≤≃`; the real
`z≤x≃y₊·z≤y₊·x` spelling is a post-instance alias in multiplication
properties. The remaining algebraic declarations in `Inverse` require inverse
or division data; its predicate uniform-continuity adapter remains the
documented analytic exception. The general `≤Cont₂`, `≤Cont`, and
positive/half-line comparison family now lives in `Continuity.Order`, and its
direct consumers use that canonical path. The clamp continuity, interval, and
endpoint-bound helpers formerly left in `Continuity.Base` now live in
`Continuity.Clamp`; both focused modules are independent of the broad base
facade, which retains restricted compatibility reexports. The final
interval-predicate inclusion `sym-intervalℙ⊆ointervalℙ` now lives in
`Continuity.Predicate`; rational-domain uniform continuity lives in
`Continuity.Uniform.Base`; and the `ℚApprox…` types, equivalence, conversion,
and composition API now live in `Continuity.Approximation`. Direct consumers
use these canonical paths while `Continuity.Base` retains compatibility
reexports. The generic proposition proof `isPropIsContinuous` and the binary
addition/subtraction continuity family now live in `Continuity.Core`, with all
direct consumers using that canonical owner. The Cauchy-limit order adapters
`≤lim`, `lim≤`, and `limConstRat` now live in the focused
`Continuity.Limit` module; bisection and roots import them directly while
`Continuity.Base` preserves the old path. The residual classification is now
complete: `Analysis.Lipschitz.Extension` owns `fromLipschitz'`,
`Analysis.Order.Functions` owns the rational monotonicity predicates,
`Foundation.Rationals` owns the pure rational aliases, real/rational bounds
live in dependency-appropriate order modules, and canonical real-ring numeral
normalization lives in `Algebra.Ring`. `Continuity.Base` now contains no
declarations and is solely a
compatibility facade. `Data.Fin.Properties.factorEquiv-fst` now characterizes
the generic finite-product equivalence's coordinate order, and integration's
`Fin^2·` uses that equivalence after swapping coordinates and transporting
the cardinality; `Fin^2·-fst` records preservation of the established
row-major indexing. `Algebra.Semiring.Properties.ExponentiationLaws` now
supplies exponent addition for any semiring exponentiation satisfying the
zero/successor equations; integration's `ℕ^+` and `2^+` are compatibility
adapters over that theorem, while its doubling-recursive `2^` remains in place
for the finite-fold reduction behavior. Phase 2 is complete. The first Phase 4
power-ownership slice is complete as well: generic commutative-ring theory now
owns the small-exponent laws, rational embedding preserves powers through its
commutative-ring homomorphism, and the established real zero, one, square,
parity, absolute-value, and exponent-one spellings are compatibility adapters.
Square nonnegativity and the square/absolute-value identity are direct
`ℝOrderedCommRing` specializations. Analytic continuity remains Cauchy-real
specific. The natural-power order split is complete: generic ordered-ring
theory owns bounds above and below one, nonstrict and positive-exponent strict
monotonicity on nonnegative elements, apartness preservation from one, and
strict exponent growth for bases above one. `Algebra.Power.Order` owns the
established real and rational adapters, while `Analysis.Sequence.Base` only
reexports its former names for compatibility and all direct consumers import
the focused owner. The remaining power-order audit is now complete: generic
ordered-ring theory also owns nonstrict positive-exponent reflection on
nonnegative elements and exponent antitonicity for bases in `[0,1]`.
`Algebra.Power.Order` provides the real and rational specializations, including
the established sequence and Pi spellings, and their direct consumers use the
focused owner. Strict power reflection remains at the Cauchy-real field
boundary: its factorization proof cancels a strictly positive real factor via
the inverse-backed strict scaling equivalence, an operation not constructively
available from the current `OrderedCommRing` interface. The remaining Phase 4
order-theoretic sum family is now generic: `OrderedCommRing.SumTheory` supplies
nonstrict and nonempty strict FinVec monotonicity, positive-summand existence,
and an all-length
absolute-value bound. Integration explicitly transports its sigma-based `Fin`
folds across the existing `FinData≃Fin` equivalence and retains its established
fold theorem signatures as adapters. The former density-heavy proof of Bishop
proposition 7 is now a direct specialization of generic positive-summand
existence. The algebraic fold audit is complete as well:
`Semiring.BigOps` owns finite-sum exchange, while `Ring.BigOps` owns
pointwise-difference splitting, constant sums, and telescoping. Integration's
accumulator, zip, scalar-distribution, transpose, constant, and delta-sum
theorems retain their established signatures as bridge-based adapters.
`Algebra.Matrix.∑Exchange` is now a compatibility specialization of the generic
theorem, and `Data.Fin.Properties` records the weakening and final-index laws
needed at the `FinData≃Fin` boundary. The remaining local fold machinery is
representation-specific reindexing and cardinality transport. Phase 4 is
complete.
The additive-automorphism dependency cleanup from Phase 8 is complete as well:
the additive real group now lives in `Algebra.Ring`, the nonzero-real carrier
lives in `Algebra.Order.Apartness`, and continuous additive automorphisms,
their rational linearity, and scalar classification live in
`Analysis.Continuity.AdditiveAutomorphism`. The old real-power infrastructure
path retains restricted compatibility reexports but no longer owns or proves
the additive declarations.
The expression-lifting ownership cleanup from Phase 8 is complete as well:
`Cubical.Tactics.CauchyReals.ExpressionLifting` is the canonical owner of the
rational-to-real reflection tactic, while the former
`Algebra.Expression.Lifting` path is a compatibility facade. All active
library consumers import the tactic namespace directly. During validation,
the dependent inverse-equivalence path in `Circle.Unwind` exposed a severe
normalization blow-up; naming its sigma point, section, projection, adjoint,
and translated path reduced the check from an unbounded stall to a complete
check, and its `PointedUnwind` consumer now checks normally as well.
Predicate-indexed `IsUContinuousℙ` adapters now live in the focused
`Analysis.Metric.Compatibility.Predicate` module. They interpret a dependent
function on `P` as a map from `PremetricSubspace ℝPremetricSpace P`; the
Cauchy-real-to-generic direction retains the explicit modulus, while the reverse
direction is propositionally truncated because the generic mapping API hides
its modulus.
All unconditional migration slices and the explicitly authorized legacy-metric
retirement are complete. The remaining open checklist item is a deliberate
gate: `pasteAt`, `pasteAbove`, and `pasteAboveClosed` have no use outside their
defining modules and facade, including before their module split, so another
consumer is still required to determine the right abstraction boundary.

## Phase 1: ordered algebra structure

Status: completed; inverse and division APIs intentionally remain at their
field-specific boundary.

Proposed internal organization:

```text
Cubical/HITs/CauchyReals/Algebra/
  Ring.agda
  Order/
    Addition.agda
    Addition/
      Base.agda
      Bootstrap.agda
      Strict.agda
      Properties.agda
    AbsoluteValue.agda
    Apartness.agda
    Density.agda
    Lattice.agda
    Multiplication.agda
    Multiplication/
      Properties.agda
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
- [x] Move ordinary ordered-ring lemmas out of `Continuity.Base` and
      `Inverse` or replace them with generic theorem aliases.
  - [x] Generalize left/right additive cancellation for `<` and `≤`, including
        their proposition equivalences; expose the real spellings from
        `Algebra.Order.Addition.Properties` and retain `Inverse` reexports.
  - [x] Generalize negation reversal and the strict/nonstrict positive- and
        negative-difference characterizations; move nine established real
        names to `Algebra.Order.Addition.Properties` with `Inverse` reexports.
  - [x] Generalize the nine additive rearrangement implications near the start
        of `Inverse`, move their real spellings to
        `Algebra.Order.Addition.Properties`, and retain compatibility exports.
  - [x] Move the rational-factor monotonicity wrappers `≤ᵣ-·o` and
        `≤ᵣ-o·` to `Algebra.Order.Multiplication`, deriving them from the
        real-factor API and retaining `Inverse` reexports.
  - [x] Classify `<ᵣ→Δ` as a Cauchy-real rational-density bound, move it to
        `Foundation.Order.Density`, and retain its `Bounds` and `Inverse`
        reexports.
  - [x] Extract the continuity/extensionality kernel to
        `Analysis.Continuity.Core`; move additive identities, nonstrict
        translation, and negation reversal to
        `Algebra.Order.Addition.Base`, retaining `Continuity.Base` reexports.
  - [x] Move the five lattice bounds and their supporting min/max identities
        to `Algebra.Order.Lattice`, retaining `Continuity.Base` reexports.
  - [x] Move strict translation `<ᵣ-+o` and its rational-approximation support
        to `Algebra.Order.Addition.Strict`, eliminating the final
        `Continuity.Base` import from `Algebra.Order.Instance` while retaining
        compatibility reexports.
  - [x] Move negation continuity to `Analysis.Continuity.Core`; move the nine
        established absolute-value and triangle-inequality spellings from
        `Continuity.Base` and `Inverse` to `Algebra.Order.AbsoluteValue`,
        retaining compatibility reexports from both old paths.
  - [x] Add generic counterparts for the seven remaining additive
        rearrangement implications; retain explicitly suffixed pre-instance
        proofs in `Algebra.Order.Addition.Base` and `Addition.Strict`, isolate
        their low-level consumers through `Addition.Bootstrap`, and expose the
        established names as post-instance aliases from `Addition.Properties`
        through both compatibility facades.
  - [x] Generalize and move the four negation-induced half-line isomorphisms
        and their four function-space lifts formerly defined in
        `Continuity.Base`; retain the real bootstrap spellings in
        `Addition.Base` and compatibility reexports from the old path.
  - [x] Move the four positive/nonnegative min/max subtype constructors from
        `Continuity.Base` to `Algebra.Order.Lattice`.
  - [x] Generalize `absᵣ-monotoneOnNonNeg` and move its established real
        specialization from `Continuity.Base` to
        `Algebra.Order.AbsoluteValue`.
  - [x] Add generic coordinatewise meet/join monotonicity and move
        `minMonotoneᵣ` and `maxMonotoneᵣ` from `Continuity.Base` to
        `Algebra.Order.Lattice`.
  - [x] Move the positive-domain monotone-image bounds `incr→max≤` and
        `incr→≤min` from `Continuity.Base` to `Algebra.Order.Lattice`.
  - [x] Generalize the min/max absolute-difference identity and move the
        established `absᵣ-min-max` theorem from `Continuity.Base` to
        `Algebra.Order.AbsoluteValue`.
  - [x] Extract predicate-indexed and open-domain continuity into
        `Analysis.Continuity.Predicate`, move `cont₂+ᵣ` into `Continuity.Core`,
        and remove the broad `Continuity.Base` import from
        `Algebra.Multiplication`.
  - [x] Add generic coordinatewise multiplication monotonicity and move
        `<ᵣ₊Monotone·ᵣ`, `<≤ᵣ₊Monotone·ᵣ`, and `≤<ᵣ₊Monotone·ᵣ` to the
        post-instance `Algebra.Order.Multiplication.Properties` module.
  - [x] Replace the real positive/nonnegative power proofs and
        `≤Weaken<+ᵣ` with generic ordered-ring specializations, retaining
        `Inverse` compatibility reexports.
  - [x] Move `denseℝ` to `Algebra.Order.Density` as the real specialization
        of the generic characteristic-not-two midpoint theorem.
  - [x] Move negation preservation of apartness, the open nonzero predicate,
        and its openness proof from `Algebra.Inverse` to
        `Algebra.Order.Apartness`; move the sign function, its predicate
        continuity, and sign/absolute-value identities to `Algebra.Signs`,
        retaining `Inverse` compatibility reexports.
  - [x] Move `≤ContWP`, `≤ContWP＃≤`, and `≤ContWP＃≤'` from
        `Algebra.Inverse` to `Analysis.Continuity.Order`, migrate the real-power
        consumer to the canonical import, and retain `Inverse` reexports.
  - [x] Move `≤Cont₂`, `≤Cont`, `≤Cont₂Pos`, `≤ContPos'`,
        `<→≤ContPos'`, and `≤ContPos` from `Continuity.Base` to
        `Continuity.Order`, migrate their direct consumers, and retain the old
        path through a restricted compatibility reexport.
  - [x] Remove the broad `Continuity.Base` dependencies from
        `Continuity.Clamp`, `Continuity.Order`, and `Algebra.Order.Apartness`;
        move the remaining clamp continuity, interval-fixpoint, and endpoint
        bound helpers into `Continuity.Clamp` with `Continuity.Base`
        compatibility reexports.
  - [x] Move `sym-intervalℙ⊆ointervalℙ` from `Continuity.Base` to
        `Continuity.Predicate`, retain the compatibility path, and migrate its
        arcsine and circle consumers to the focused owner.
  - [x] Move `IsUContinuousℚℙ` to `Continuity.Uniform.Base`; extract the
        `ℚApprox…` structures, equivalence, conversion, and composition API to
        `Continuity.Approximation`; migrate all direct consumers and retain
        restricted `Continuity.Base` reexports.
  - [x] Move `isPropIsContinuous`, `IsContinuous+₂∘`,
        `IsContinuous-₂∘`, and `IsContinuous-₂` to `Continuity.Core`; migrate
        their direct consumers while retaining the public base facade.
  - [x] Extract `≤lim`, `lim≤`, and `limConstRat` to
        `Continuity.Limit`; migrate bisection and roots to the focused owner
        and retain restricted `Continuity.Base` reexports.
  - [x] Move `fromLipschitz'` to `Analysis.Lipschitz.Extension` and migrate
        real-power infrastructure to the focused owner.
  - [x] Express `isIncrasingℙ` and `isNondecrasingℙ` through the generic
        rational quoset/poset mapping APIs in `Analysis.Order.Functions` and
        migrate roots to that module.
  - [x] Move the remaining rational aliases and rational-embedding bounds to
        `Foundation.Rationals`, `Foundation.Order.RationalBounds`,
        `Foundation.Order.Base`, and `Algebra.Order.Lattice`; reduce
        `Continuity.Base` to a declaration-free compatibility facade.
  - [x] Move the established generic positive-operation aliases from
        `Algebra.Inverse` to `Algebra.Order.Positive`, and move the rational
        `ℚmax-min-minus` compatibility alias to `Foundation.Rationals`.
  - [x] Add generic positive-factor nonstrict multiplication equivalences and
        move `z≤x≃y₊·z≤y₊·x` to
        `Algebra.Order.Multiplication.Properties` as a real specialization.
- [x] Define `ℝArchimedeanRing` from the canonical integer embedding, positive
      multiplication cancellation, and the existing natural-number bound.
- [x] Move applicable bounds into
      `ArchimedeanRing.Properties`.

Known ingredients already present include `ℝcommRing`, `isPosetℝ`, strict
order transitivity and irreflexivity, lattice laws, additive monotonicity,
multiplicative monotonicity on nonnegative/positive factors, and `0 < 1`.
The previously missing weak linearity, `≤ ≃ ¬ >`, and positive-sum
decomposition fields now live in `Algebra.Order.Properties`.

## Phase 2: exact duplicate removal

Status: completed.

These changes should reuse existing library definitions rather than move the
local implementations verbatim.

### Fin and natural-number infrastructure

- [x] Replace `injectFin+`, `injectFin+'`, `Fin+→⊎`, `Iso-Fin+⊎`, and their
  compatibility proofs with `Data.Fin.Properties.Fin+≅Fin⊎Fin`,
  `Iso-Fin⊎Fin-Fin+`, or `Data.Fin.Recursive.Properties.sumIso`.
- [x] Replace `Fin^2·` with `factorEquiv` or `Iso-Fin×Fin-Fin·`. The generic
  `factorEquiv-fst` characterization supplies the explicit compatibility path;
  `Fin^2·` swaps the coordinates before applying `factorEquiv` and preserves
  the established indexing through `Fin^2·-fst`.
- [x] Replace local parity machinery `_∣2` and `∣2-cases` with
  `Data.Nat.IsEven`.
- [x] Move genuinely missing utilities such as endpoint/middle Fin elimination
  to `Data.Fin.Properties`; do not keep them in integration modules.
- [x] Add the missing semiring exponent-addition law and replace the local
  `ℕ^+` and `2^+` inductions with compatibility adapters. Retain `2^-^` only
  as the path from integration's doubling-recursive `2^` to the standard
  natural power.

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
      operations after untangling their former dependency on `Inverse`; keep
      the established spellings in `Algebra.Order.Positive` with `Inverse`
      compatibility reexports.
- [x] Replace the nonnegative addition and multiplication implementations in
      `RationalPower.Core` and the nonnegative power implementation in
      `Roots.NonNegative` with `NonNegativeReals` operations.
- [x] Migrate internal consumers to the canonical nonnegative operations while
      retaining the existing operator spellings at compatibility boundaries.
- [x] Keep inverse/division on positive reals in a field/inverse-specific
      module until an appropriate generic ordered-field abstraction exists;
      no ordered-ring-level inverse API was introduced.

## Phase 4: generic ordered-ring theory

Status: completed; strict inverse-backed reflection and analytic continuity
remain at their explicitly documented Cauchy-real boundaries.

### Arithmetic and absolute values

Move or replace the following families with `OrderedCommRing.Properties`:

- additive and multiplicative monotonicity;
- addition/subtraction rearrangement equivalences;
- negation order reversal and half-line equivalences;
- square nonnegativity and square/absolute-value identities;
- triangle and reverse-triangle inequalities;
- cancellation equivalences such as `x + y ≤ z + y ≃ x ≤ z`.
- [x] Add generic left/right additive cancellation implications and
      equivalences for both strict and nonstrict order.
- [x] Add generic coordinatewise multiplication monotonicity for strict,
      nonstrict, and mixed comparisons.
- [x] Add generic left/right nonstrict multiplication equivalences for a
      positive factor and specialize the established real scaling theorem.
- [x] Add generic negation-reversal equivalences and strict/nonstrict
      equivalences between order and the sign of a difference.
- [x] Add the generic strict/nonstrict additive rearrangement implications
      used by the established Cauchy-real order API.
- [x] Add generic absolute-value monotonicity on nonnegative elements.
- [x] Add generic coordinatewise meet/join monotonicity at the pseudolattice
      layer and expose ordered-ring `⊓Monotone`/`⊔Monotone` spellings.
- [x] Add the generic join-minus-meet absolute-difference identity
      `abs≡⊔-⊓`.
- [x] Add the generic reverse-triangle inequality and the negation De Morgan
      law for joins and meets; expose the rational `max`/`min` spelling from
      rational order algebra.
- [x] Replace the real square-nonnegativity and square/absolute-value proofs
      with `ℝOrderedCommRing` specializations, bridging the continuously lifted
      absolute value through `abs-max`.

### Powers

- [x] Add generic positive/nonnegative power preservation and power operations
      on the corresponding ordered-ring subtypes.
- [x] Put purely commutative-ring power laws in `CommRing.Properties`, including
      the small-exponent identities and homomorphism preservation, and retain
      the established Cauchy-real spellings as compatibility adapters.
- [x] Put power bounds and monotonicity on nonnegative elements in ordered-ring
      power theory, including strict monotonicity for a positive exponent and
      strict exponent growth above one; retain the real and rational names in
      `Algebra.Power.Order`.
- [x] Put nonstrict positive-exponent power reflection and exponent
      antitonicity on `[0,1]` in ordered-ring theory; retain strict reflection
      at the inverse-backed Cauchy-real boundary because strict multiplication
      cancellation is absent from `OrderedCommRing`.
- Keep continuity of real powers in `CauchyReals`.

### Finite sums

- [x] Standardize integration on the existing `FinVec`/big-operator API where
      possible. Algebraic and order-theoretic folds use an explicit
      `FinData≃Fin` bridge; only representation-specific map, transport,
      concatenation, and finite-product folds remain local.
- [x] Put algebraic fold laws in `Semiring.BigOps` or `Ring.BigOps`, including
      exchange, pointwise difference, constant sums, and telescoping.
- [x] Put finite-sum monotonicity, positive-summand existence, and
      absolute-value bounds in ordered-ring big-operator theory.
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
- [x] Add the generic clamp fixpoint and interval-elimination principle, with
      a predicate-interval adapter for Cauchy reals.
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

Status: completed.

- [x] Move the alternating-sign predicates, parity helpers, partial-sum
      bounds, and rational Cauchy estimate from
      `Analysis.Sequence.AlternatingSeries` to
      `Cubical.Data.Rationals.Series.Alternating`.
- [x] Move the rational magnitude-to-signed-series constructor to the same
      rational module.
- [x] Leave only the Cauchy-real convergence/lifting adapters under
      `CauchyReals.Analysis.Sequence`.
- [x] Move rational restricted-Lipschitz predicates from
      `Approximation.Bisection` to `Data.Rationals.Analysis.Lipschitz`, expose
      them through the layered `Data.Rationals.Analysis` facade, and retain
      compatibility reexports from the old path.
- Keep the Cauchy-real inverse-bisection construction and recovery machinery
  under `CauchyReals.Approximation`.

## Phase 7: premetric migration

Status: completed; canonical consumers and p-norm mathematics have migrated,
and the parallel legacy hierarchy and its compatibility packages are retired.

The former `Analysis.Metric.Base` duplicated much of
`Cubical.Relation.Premetric`, which already provides continuous, uniformly
continuous, Lipschitz, nonexpanding, and isometric maps together with
composition and categories.

- [x] Construct the real premetric instance through
      `ArchimedeanRing→PremetricSpace`.
- [x] Repair the generic Archimedean-ring premetric implementation to use the
      live standard-rational hierarchy and current positive-division API.
- [x] Add generic predicate-subspace support with nonexpanding and uniformly
      continuous inclusion maps; specialize it to real closed intervals.
- [x] Relate the generic real closeness relation to the established
      Cauchy-real closeness and strict distance formulations.
- [x] Add adapters between the full-real and predicate-indexed Cauchy-real
      uniform continuity interfaces and generic uniformly continuous maps.
      The focused predicate bridge uses
      `PremetricSubspace ℝPremetricSpace P` and keeps
      the reverse conversion propositionally truncated with the hidden generic
      modulus.
- [x] Migrate Cauchy-real metric consumers to `Relation.Premetric`; reversal,
      interval carriers, and the circle subspace inclusion have moved. The
      subsequently unused Euclidean circle metric packaging was retired.
- [x] Add generic coordinatewise product support with projections, pairing,
      insertions, and nonexpanding/uniformly-continuous maps.
- [x] Add the canonical unit premetric and generic nonexpanding/uniformly
      continuous maps out of it; expose the trivial-space compatibility names
      from `Analysis.Metric.Discrete`; the legacy discrete metric construction
      was subsequently retired.
- [x] Split `Analysis.Metric.Discrete` into a layered facade, a canonical
      `Discrete.Base` containing only generic unit-premetric aliases, and a
      nested compatibility layer whose legacy decidable metric was later
      retired.
- [x] Keep real-root p-norm mathematics under `CauchyReals`, while moving
      generic product-space mapping facts out of `PNorm`; the real-root proofs
      now live in `PNorm.Base`, while the former p-norm `MetricSpaceStr`,
      `pair-ucm`, and Euclidean real-plane packaging have been retired.
- [x] Audit the remaining direct `Analysis.Metric.Base` consumers; all four
      were compatibility modules or the public `Metric` facade.
- [x] Move the retained hierarchy implementation to `Analysis.Metric.Legacy`,
      migrate its internal compatibility consumers, and preserve
      `Analysis.Metric.Base` as a backwards-compatible facade during migration.
- [x] Delete the parallel `MetricSpace`, `UContMap`, and `IsIsometry` hierarchy
      after explicit authorization to retire those names. The `Legacy` and old
      `Base` modules and the discrete, p-norm, and circle compatibility modules
      are removed; surviving facades export only canonical layers.

## Phase 8: optional broader abstractions

Status: additive-automorphism and expression-lifting ownership cleanups
completed. A repository and pre-split history audit found no pasting consumer
outside this API itself, so the remaining optional generalization stays
deferred until it has another consumer.

- [ ] Generalize `pasteAt`, `pasteAbove`, and `pasteAboveClosed` over a
  lattice-ordered domain and an additive-group codomain if another consumer
  appears.
- [x] Move additive-automorphism infrastructure out of exponentiation so
  analysis does not import `RealPower.Infrastructure` for basic group
  structures. `Algebra.Ring` now owns `+Groupℝ`,
  `Algebra.Order.Apartness` owns `ℝ₋₊`, and
  `Analysis.Continuity.AdditiveAutomorphism` owns `Aut[_]ᵣ` and
  `+GrAutomorphism`; the old infrastructure path retains restricted
  compatibility reexports.
- [x] Move the expression-lifting tactic to the tactic-oriented
  `Cubical.Tactics.CauchyReals.ExpressionLifting` namespace. The former
  `Algebra.Expression.Lifting` path is a compatibility facade, while active
  library consumers use the canonical tactic path directly.

The remaining item does not currently block the main import cleanup.

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
- 2026-07-18: committed the completed rational magnitude-series extraction as
  `9e4f9badb`.
- 2026-07-18: introduced `Data.Rationals.Analysis.Lipschitz` with the clearer
  `IsLipschitzWithOn` and `IsLipschitzWithOnOrdered` API, plus compatibility
  aliases for the established rational names; exposed it through a new
  layered `Data.Rationals.Analysis` facade.
- 2026-07-18: reduced `Approximation.Bisection` to compatibility reexports and
  the genuinely Cauchy-real rational-to-real bridge, and migrated the root
  implementation to the canonical rational predicates.
- 2026-07-18: added generic `clampFixpoint` and `elimIntervalByClamp` to the
  pseudolattice clamp layer, specialized the eliminator to Cauchy-real
  predicate intervals, and migrated bisection and root implementations while
  preserving `elimInClampsᵣ` at the old path.
- 2026-07-18: checked both new rational analysis modules, all four changed
  implementation modules, and the `Pseudolattice`, `Approximation`, `NthRoot`,
  `Analysis`, and `Transcendental` facades with no holes, metas, constraints,
  or warnings.
- 2026-07-18: committed the rational Lipschitz and generic clamp-elimination
  checkpoint as `2d00fd278`.
- 2026-07-18: added `Algebra.Order.Archimedean` with `ℝArchimedeanRing`; it
  reuses the canonical ordered-ring embedding of integers, derives strict
  multiplication cancellation from the positive inverse equivalence, and
  derives Archimedean growth by applying `getClamps` to `x / y`.
- 2026-07-18: migrated `Relation.Premetric.Instances.ArchimedeanRing` from the
  removed fast-rational modules to the standard rational hierarchy, and
  updated `Relation.Premetric.Mappings` to the current positive-rational
  division API.
- 2026-07-18: introduced generic `PremetricSubspace`, nonexpanding and
  uniformly-continuous subspace inclusions, plus `ℝPremetricSpace`,
  `ClosedIntervalPremetricSpace`, and `UnitIntervalPremetricSpace` behind the
  layered Cauchy-real metric facade.
- 2026-07-18: proved `≈ℝ≃∼`, relating the Archimedean-ring premetric on reals
  to the established Cauchy-real closeness relation through positive rational
  representatives and strict absolute distance.
- 2026-07-18: split the lightweight `IsUContinuous` and `IsUContinuousℙ`
  interfaces into `Analysis.Continuity.Uniform.Base`, retained their old
  reexports, and added the checked full-real compatibility adapters under the
  nested `Analysis.Metric.Compatibility.Base` module.
- 2026-07-18: added generic coordinatewise products, projections, pairing,
  constant-coordinate insertions, and generic subspace relation bridges;
  specialized the product to `ℝ²PremetricSpace` and the circle predicate to
  `distCirclePremetricSpace`.
- 2026-07-18: made real reversal canonically nonexpanding (and hence uniformly
  continuous), exposed a nonexpanding circle inclusion, and migrated the
  carrier-only interval signatures in `Circle.PointedUnwind` and
  `Circle.Unwind` to `ClosedIntervalPremetricSpace`.
- 2026-07-18: added layered `Relation.Premetric` mapping and structural-instance
  facades. A focused predicate-continuity packaging experiment was removed
  after it caused multi-minute normalization even with explicit record
  boundaries; future work must avoid unfolding the complete subspace
  structure at that adapter boundary.
- 2026-07-18: repaired `Premetric.Completion.Properties.Lift` and its
  function-space dependency to the standard rational/inverse hierarchy,
  restored reusable half/quarter/mean facts in generic ordered-ring theory,
  and checked the complete lift module with no holes, metas, or warnings.
- 2026-07-18: added the generic `UnitPremetricSpace` instance and canonical
  nonexpanding/uniformly-continuous maps from it; exposed trivial-premetric
  compatibility names from `Analysis.Metric.Discrete` while retaining the
  legacy decidable-equality discrete metric unchanged.
- 2026-07-18: completed the interval/circle metric-consumer migration by
  moving the internally unused Euclidean p-norm circle metric packaging into
  `Circle.Metric.Compatibility`; `Circle.Metric` now directly depends on the
  coordinatewise premetric API and publicly reexports the legacy names.
- 2026-07-19: split `Analysis.Metric.PNorm` into a layered facade,
  `PNorm.Base` for the real-root inequalities and nonnegative arithmetic, and
  `PNorm.Compatibility` for the legacy p-norm `MetricSpaceStr`, `pair-ucm`,
  and `𝐑²MetricSpaceStr` packaging. The canonical base has no dependency on
  `Analysis.Metric.Base`, while the old public `PNorm` import remains intact.
- 2026-07-19: audited direct legacy metric imports after the split. Apart from
  `Analysis.Metric.Base` itself, only `Analysis.Metric.Discrete`,
  `PNorm.Compatibility`, `Circle.Metric.Compatibility`, and the layered
  `Metric` facade still import that hierarchy.
- 2026-07-19: split `Analysis.Metric.Discrete` into a layered facade,
  `Discrete.Base` for the generic `UnitPremetricSpace` aliases and canonical
  maps, and `Discrete.Compatibility` for `DiscreteMetricStr`,
  `trivialMetricSpace`, and its legacy uniform-continuity theorem. The
  canonical base now has no Cauchy-real or legacy metric imports.
- 2026-07-19: refreshed the legacy import audit after the discrete split;
  `Analysis.Metric.Base` is now imported only by `Discrete.Compatibility`,
  `PNorm.Compatibility`, `Circle.Metric.Compatibility`, and the public
  `Metric` facade.
- 2026-07-19: moved the retained `MetricSpace`, `UContMap`, and `IsIsometry`
  implementation to `Analysis.Metric.Legacy`, migrated all internal
  compatibility consumers and the layered `Metric` facade to that explicit
  path, and reduced `Analysis.Metric.Base` to a backwards-compatible reexport.
  Removing the declarations themselves is deferred while the public facade
  policy remains in force.
- 2026-07-19: added generic left/right additive cancellation implications and
  proposition equivalences to `Algebra.OrderedCommRing.Properties`; introduced
  `Algebra.Order.Addition.Properties` for the established Cauchy-real names,
  retained those names as public `Algebra.Inverse` compatibility reexports,
  and migrated the circle metric's cancellation dependency to the focused
  order module.
- 2026-07-19: completed the next ordered-arithmetic slice by adding generic
  negation-reversal equivalences and strict/nonstrict positive- and
  negative-difference implications and equivalences. Nine established real
  declarations moved from `Algebra.Inverse` to
  `Algebra.Order.Addition.Properties`, with public compatibility reexports;
  `Circle.Metric` now obtains negation reversal from the focused order module.
  The audit also recorded that extracting the corresponding foundational
  declarations from `Analysis.Continuity.Base` first requires unwinding the
  current ordered-ring-instance dependency on that module.
- 2026-07-20: generalized all nine additive rearrangement implications that
  remained near the start of `Algebra.Inverse`. Their generic proofs in
  `Algebra.OrderedCommRing.Properties` use only additive monotonicity followed
  by commutative-ring normalization; the established real spellings now live
  in `Algebra.Order.Addition.Properties` and remain public `Inverse` reexports.
  `Calculus.Integration.FundamentalTheorem` now imports its four-term
  rearrangement theorem from the focused order module while retaining its
  separate inverse dependencies.
- 2026-07-20: moved the rational-factor monotonicity wrappers `≤ᵣ-·o` and
  `≤ᵣ-o·` from `Algebra.Inverse` to `Algebra.Order.Multiplication`, where
  they are direct specializations of the real-factor monotonicity API. Moved
  the rational-density witness `<ᵣ→Δ` to `Foundation.Order.Bounds`, retained
  all three names as public `Inverse` reexports, and changed `PNorm.Base` to
  import its rational-factor theorem from the canonical multiplication module.
- 2026-07-20: introduced dependency-light `Analysis.Continuity.Core` for
  continuity, composition, rational extensionality, and the primitive
  addition/max continuity proofs needed below the full analysis layer.
  Introduced `Algebra.Order.Addition.Base` for `+IdL`, `+IdR`,
  `+ᵣMaxDistr`, nonstrict addition monotonicity, and strict/nonstrict negation
  reversal; `Analysis.Continuity.Base` now reexports those declarations instead
  of defining them. The canonical addition module reexports its new base, and
  `Algebra.Order.Instance` imports `≤ᵣ-+o` directly while listing only its six
  remaining continuity dependencies (`<ᵣ-+o` plus five lattice bounds).
- 2026-07-20: extended `Analysis.Continuity.Core` with constant and primitive
  min continuity, and introduced `Algebra.Order.Lattice` for the min/max
  identities, distributivity laws, and strict/nonstrict bounds formerly in
  `Analysis.Continuity.Base`. The compatibility path publicly reexports the
  extracted declarations, while `Algebra.Order.Instance` imports its five
  lattice bounds directly and retains only `<ᵣ-+o` from the broad continuity
  module.
- 2026-07-20: moved primitive absolute-value continuity to
  `Analysis.Continuity.Core` and moved `≤absᵣ`, the three rational
  approximation interfaces, `<ᵣ-+o-pre`, and strict left/right translation to
  `Algebra.Order.Addition.Strict`. The canonical addition facade exposes the
  strict translation API, `Continuity.Base` preserves every established name
  as a public reexport, and `Algebra.Order.Instance` no longer imports the
  broad continuity module.
- 2026-07-20: added the generic Archimedean consequence
  `ArchimedeanRingTheory.∃ι₊₁Larger`, then rebuilt the positive and nonnegative
  real rational upper bounds as thin `ℝArchimedeanRing` specializations and
  migrated their six direct consumers. Moved the real-specific `<ᵣ→Δ` witness
  to dependency-light `Foundation.Order.Density`; `Foundation.Order.Bounds`
  retains compatibility reexports and still owns the inverse-dependent
  positive unit-fraction theorem.
- 2026-07-20: moved negation continuity to `Analysis.Continuity.Core` and
  made `Algebra.Order.AbsoluteValue` independent of broad continuity. Moved
  the triangle and reverse-triangle inequalities, `abs-max`, positive and
  nonnegative simplifications, and zero-reflection spellings there; the old
  continuity and inverse paths retain compatibility reexports. Migrated nine
  dependency-sensitive consumers, including foundational bounds, the real
  Archimedean and premetric adapters, apartness, signs, and the three users of
  the former `Inverse` declarations.
- 2026-07-20: completed the remaining foundational additive-rearrangement
  family. Added six ordered-commutative-ring theorems alongside the existing
  generic positive-difference implication, moved the nonstrict real bootstrap
  proof to `Algebra.Order.Addition.Base` and the six strict proofs to
  `Addition.Strict`, and retained their `Continuity.Base` availability through
  public reexports. `Algebra.Order.Properties` now obtains the two names it
  needs from the focused addition facade, while `Algebra.Order.Multiplication`
  imports only `Continuity.Core` directly. Instance-backed real aliases remain
  deferred until `Algebra.Multiplication` no longer requires the broad
  continuity module.
- 2026-07-20: generalized the four strict/nonstrict negation-induced half-line
  isomorphisms and their four function-space lifts as the
  `negHalfLine...Iso` family in `Algebra.OrderedCommRing.Properties`. Moved the
  eight established real `reverseHalfLine...` spellings to dependency-light
  `Algebra.Order.Addition.Base`, retained their `Continuity.Base` availability
  through the existing public import, and made `EndpointExtension` name the
  focused owner for its sole external use.
- 2026-07-20: moved `maxᵣ₊`, `minᵣ₊`, `minᵣ₀₊`, and `maxᵣ₀₊` from
  `Continuity.Base` to `Algebra.Order.Lattice`, retaining their old import path
  through the existing public reexport. Positive maximum and both nonnegative
  operations align with generic subtype lattice operations; positive minimum
  remains a dependency-light real proof because there is no generic strictly
  positive meet operation.
- 2026-07-20: added generic `abs-monotoneOnNonNeg` to
  `Algebra.OrderedCommRing.Properties` and moved the established
  `absᵣ-monotoneOnNonNeg` theorem from `Continuity.Base` to
  `Algebra.Order.AbsoluteValue`. The old continuity path still publicly
  reexports it, while `Algebra.Inverse`, its sole direct consumer, now names
  the focused owner. The real theorem retains its pre-instance transport proof
  to avoid a bootstrap cycle through `ℝOrderedCommRing`.
- 2026-07-20: added generic coordinatewise `∧Monotone` and its dual
  `∨Monotone` to `Relation.Binary.Order.Pseudolattice.Properties`; ordered-ring
  theory exposes them as `⊓Monotone` and `⊔Monotone`. Moved the established
  `minMonotoneᵣ` and `maxMonotoneᵣ` bootstrap proofs from `Continuity.Base` to
  `Algebra.Order.Lattice`, retaining compatibility through the old import
  path. `Algebra.Inverse` now imports both names from the focused owner, and
  `ArcSin.Prelim.Monotone.Full` imports `maxMonotoneᵣ` there directly.
- 2026-07-20: moved the positive-domain monotone-image bounds `incr→max≤` and
  `incr→≤min` from `Continuity.Base` to `Algebra.Order.Lattice`, retaining
  their old import path through the existing public reexport. Their sole
  external consumer, `Algebra.Inverse`, now imports both names from the focused
  owner. The paired real API remains bootstrap-specific because its minimum
  theorem requires a positive meet not supplied by the generic subtype layer.
- 2026-07-20: added the stronger generic join-minus-meet identity
  `abs≡⊔-⊓` to `Algebra.OrderedCommRing.Properties`. Moved the binary
  continuity/extensionality combinators needed for the real bootstrap proof
  into `Analysis.Continuity.Core`, then moved `ℚabs-min-max` and
  `absᵣ-min-max` from `Continuity.Base` to `Algebra.Order.AbsoluteValue` while
  retaining the old public path. `Algebra.Inverse`, the integration fundamental
  theorem, `Trigonometry.Pi`, and the positive arcsine continuity estimate now
  import the real theorem from its focused owner. The former
  `Data.Rationals.Series.Alternating.abs≡⊔-⊓` proof is now an alias to the
  generic theorem.
- 2026-07-20: extracted predicate-indexed continuity, open predicates,
  open-interval support, and predicate rational extensionality into
  `Analysis.Continuity.Predicate`, and moved `cont₂+ᵣ` into
  `Continuity.Core`. `Continuity.Base` is a compatibility reexport for these
  declarations, while `Algebra.Multiplication` now imports only the focused
  continuity modules and focused addition prerequisites.
- 2026-07-20: added generic coordinatewise multiplication theorems `·Mono≤`,
  `·Mono<`, `·Mono<≤`, and `·Mono≤<`, plus `≤→<SumLeftPos`, to
  `Algebra.OrderedCommRing.Properties`. Introduced the post-instance real
  module `Algebra.Order.Multiplication.Properties`; moved the three established
  strict/mixed multiplication spellings and positive/nonnegative power
  preservation there, and moved `≤Weaken<+ᵣ` to `Addition.Properties`.
  `Algebra.Inverse` retains public compatibility reexports.
- 2026-07-20: moved `denseℝ` from `Algebra.Inverse` to
  `Algebra.Order.Density`, where it is the direct real specialization of the
  generic midpoint construction for ordered rings of characteristic not two.
  Both the layered order facade and the old inverse path reexport it.
- 2026-07-20: introduced `Algebra.Order.Addition.Bootstrap` as the explicit
  pre-instance home for the small strict/mixed addition API used by order and
  open-predicate construction. Renamed the seven low-level rearrangement
  implementations with `-bootstrap` suffixes and made their established names
  direct generic-theorem specializations in `Addition.Properties`, reexported
  through both the addition and continuity compatibility facades.
- 2026-07-20: removed the unused broad-continuity import from the specialized
  real commutative-ring solver. This eliminated the hidden solver-to-facade
  cycle encountered by post-instance addition properties; the bootstrap
  module's remaining normalizations now use explicit additive cancellation
  paths rather than reflection.
- 2026-07-20: continued the inverse ownership audit by moving `-＃`, `0＃ₚ`,
  and `isOpenPred0＃` to `Algebra.Order.Apartness`, and moving `signᵣ`, its
  rational and continuity laws, `sign²=1`, `sign·absᵣ`, and `·sign-flip≡`
  to `Algebra.Signs`. `Algebra.Inverse` retains the established public surface
  through focused compatibility imports.
- 2026-07-20: checked the complete changed addition/bootstrap dependency
  chain, the specialized real solver, predicate continuity, ordered-ring
  instance, apartness, signs, and inverse modules, plus the layered `Order`
  and `Algebra` facades and the nonzero-domain real-power construction, with
  no holes, metas, constraints, or warnings.
- 2026-07-20: moved the arbitrary open-predicate comparison `≤ContWP` and
  its two nonzero-domain bounded variants from `Algebra.Inverse` to
  `Analysis.Continuity.Order`. `Inverse` retains public reexports, while the
  real-power construction explicitly obtains the names from their canonical
  continuity owner.
- 2026-07-20: moved the established positive addition, multiplication, and
  power aliases to `Algebra.Order.Positive`, leaving only positive division at
  the field-specific inverse boundary. Moved the unused-but-public rational
  alias `ℚmax-min-minus` to `Foundation.Rationals`; `Inverse` preserves all four
  old exports.
- 2026-07-20: added generic `·MonoL≤≃` and `·MonoR≤≃` positive-factor
  scaling equivalences to ordered-ring theory and made
  `z≤x≃y₊·z≤y₊·x` a real instance-backed specialization in
  `Algebra.Order.Multiplication.Properties`. The neighboring strict scaling
  and quotient equivalences remain in `Inverse`, because strict
  multiplication cancellation is not constructively derivable from the
  current `OrderedCommRing` interface.
- 2026-07-20: verified the extracted continuity, positive-operation,
  rational-compatibility, and nonstrict-scaling owners; the compatibility
  `Algebra.Inverse` module; the nonzero-domain real-power consumer; and the
  public `Analysis` and `Algebra` facades with `agda-codex`. Every check
  completed with no holes, metas, constraints, or warnings.
- 2026-07-21: moved `≤Cont₂`, `≤Cont`, `≤Cont₂Pos`, `≤ContPos'`,
  `<→≤ContPos'`, and `≤ContPos` from `Continuity.Base` to
  `Continuity.Order`, retaining a restricted compatibility reexport and
  migrating all seven direct consumers to the canonical module.
- 2026-07-21: made `Continuity.Clamp` independent of `Continuity.Base` and
  moved `IsContinuousClamp`, its binary/composition variants, `≤clampᵣ`,
  `clamp≤ᵣ`, and `∈ℚintervalℙ→clampᵣ≡` there. `Continuity.Order` now depends
  only on focused continuity modules, while `Algebra.Order.Apartness` obtains
  `lowerℚBound` directly from `Continuity.Predicate`.
- 2026-07-21: checked all changed focused modules, every migrated comparison
  consumer, and the public `Analysis` facade with `agda-codex`; all completed
  with no holes, metas, constraints, or warnings.
- 2026-07-21: moved the last interval-predicate compatibility theorem
  `sym-intervalℙ⊆ointervalℙ` from `Continuity.Base` to
  `Continuity.Predicate`. Its arcsine and circle consumers now import the
  focused predicate module, while the old base path remains available through
  the existing public reexport.
- 2026-07-21: moved rational-domain uniform continuity
  `IsUContinuousℚℙ` to `Continuity.Uniform.Base` and introduced
  `Continuity.Approximation` as the owner of the `ℚApprox…` types,
  equivalence, conversion, and composition operation. `Continuity.Base`
  retains restricted compatibility reexports and all inverse, bisection,
  root, and exponentiation consumers now use the canonical owners.
- 2026-07-21: checked the predicate, uniform, approximation, and base
  continuity modules; every migrated consumer; and the public `Analysis`
  facade with `agda-codex`. All checks completed with no holes, metas,
  constraints, or warnings.
- 2026-07-21: moved the proposition proof `isPropIsContinuous` and the binary
  addition/subtraction continuity combinators `IsContinuous+₂∘`,
  `IsContinuous-₂∘`, and `IsContinuous-₂` to `Continuity.Core`. Their
  real-power, derivative, integration, and trigonometry consumers now import
  the focused owner; `Continuity.Base` continues to reexport Core publicly.
- 2026-07-21: introduced `Continuity.Limit` as the focused owner of `≤lim`,
  `lim≤`, and `limConstRat`. Bisection and roots now use the canonical module,
  the `Analysis` facade exports it directly, and `Continuity.Base` retains a
  restricted compatibility reexport.
- 2026-07-21: checked Core, Limit, the base compatibility facade, all migrated
  consumers, and the public `Analysis` facade with `agda-codex`; every check
  completed with no holes, metas, constraints, or warnings.
- 2026-07-21: introduced `Analysis.Lipschitz.Extension` as the focused owner
  of the truncated-constant extension `fromLipschitz'`; exposed it through the
  Lipschitz facade and migrated real-power infrastructure to the canonical
  import.
- 2026-07-21: moved the rational restricted monotonicity spellings to
  `Analysis.Order.Functions` as aliases of generic poset/quoset mapping
  predicates, and migrated their roots consumer.
- 2026-07-21: moved `m·n/m`, `abs'q≤Δ₁'`, and `ℚabs-abs≤abs-` to
  `Foundation.Rationals`; moved the mixed bound `abs'q≤Δ₁` to the new
  dependency-light `Foundation.Order.RationalBounds`; and placed `<min-rr`
  and `rexprTest` with the lattice and foundational expression-lifting facts
  they specialize. The separate rational-bound module avoids the
  `Bounds`/`Inverse` compatibility cycle discovered during extraction.
- 2026-07-21: removed every implementation import and declaration from
  `Continuity.Base`, leaving only focused compatibility reexports. Checked all
  new owners, both affected foundational facades, the Lipschitz facade, roots,
  real-power infrastructure, and the continuity compatibility facade with no
  holes, metas, constraints, or warnings.
- 2026-07-21: added `factorEquiv-fst` to `Data.Fin.Properties` and replaced
  integration's hand-built `Fin^2·` bound proof with the generic
  finite-product equivalence, swapping its inputs to retain the established
  row-major coordinate significance. The explicit `Fin^2·-fst` path now
  supports both injection compatibilities and the `foldFin·2^` base case.
- 2026-07-21: checked `Data.Fin.Properties` and `Calculus.Integration.Summation`
  with `agda-codex`; both completed with no holes, metas, constraints, or
  warnings.
- 2026-07-21: introduced `Algebra.Semiring.Properties.ExponentiationLaws`,
  parameterized by an exponentiation operation and its zero/successor laws,
  together with the canonical semiring exponentiation specialization. Replaced
  the integration-local inductions for `ℕ^+` and `2^+` with adapters to the
  generic exponent-addition theorem without changing their public statements.
- 2026-07-21: checked `Algebra.Semiring.Properties`, integration summation, and
  the direct partition consumer with `agda-codex`; all completed with no holes,
  metas, constraints, or warnings. Phase 2 is complete.
- 2026-07-21: completed the pure commutative-ring portion of the power-ownership
  audit. Added `x^1≡x` and `x^2≡x·x` to
  `Algebra.CommRing.Properties.Exponentiation`; made the established real
  square and rational-power embedding theorems adapters to generic
  exponentiation and commutative-ring-homomorphism laws; and replaced the real
  zero, one, absolute-value, and exponent-one power inductions with generic
  adapters while preserving their public statements.
- 2026-07-21: replaced `x·x≡∣x∣·∣x∣` and `0≤ᵣx²` with direct generic
  ordered-ring specializations through `ℝOrderedCommRing` and `abs-max`.
  `Algebra.Power.Base` now imports `Continuity.Core` instead of the broad
  compatibility facade and no longer needs expression lifting; its genuinely
  analytic `IsContinuous^ⁿ` proof remains local.
- 2026-07-21: checked `Algebra.CommRing.Properties`, real multiplication,
  `Algebra.Power.Base`, rational-power convexity, and the public Cauchy-real
  algebra facade with `agda-codex`; all completed with no holes, metas,
  constraints, or warnings.
- 2026-07-21: added generic ordered-ring natural-power bounds and monotonicity
  to `Algebra.OrderedCommRing.Properties`: `one<pow`, `pow<one`, `pow≤one`,
  `powMono`, `powStrictMono`, `one#pow`, and
  `powExponentStrictMono`. These require no Cauchy-real continuity, density,
  sequence, or inverse data.
- 2026-07-21: moved the established real and rational spellings `1<^`, `^<1`,
  `^≤1`, `1＃^`, `^ⁿ-Monotone`, `^ⁿ-StrictMonotone`,
  `ℚ^ⁿ-Monotone`, and `ℚ^ⁿ-StrictMonotone` to
  `Algebra.Power.Order` as instance-backed adapters. Its exponent-growth
  theorem is now generic as well. `Analysis.Sequence.Base` retains a restricted
  public compatibility import instead of implementations, reversing the old
  power-order-to-sequence dependency.
- 2026-07-21: migrated all eleven direct circle, roots, trigonometry,
  rational-power, arcsine, p-norm, and exponential-series consumers to import
  the focused power-order owner. Checked generic ordered-ring theory, the
  focused owner, the sequence compatibility module, and every changed consumer
  plus the public algebra and sequence facades with `agda-codex`; all completed
  with no holes, metas, constraints, or warnings.
- 2026-07-21: added generic `powReflects≤` and `powExponentAntitone` to
  `Algebra.OrderedCommRing.Properties`. Nonstrict reflection follows by
  contraposing positive-exponent strict monotonicity, so it needs neither the
  Cauchy-real factorization nor density; exponent antitonicity is the generic
  multiplication induction for a nonnegative base below one.
- 2026-07-21: moved `^ⁿMonotone⁻¹`, `^ⁿMonotone⁻¹-with0`, and the Pi-local
  `^ⁿ-MonotoneR-inv` to `Algebra.Power.Order` as instance-backed adapters, and
  made rational power reflection a direct generic specialization. Sequence
  retains its two established nonstrict names through a restricted public
  reexport, while rational power, roots, angle bounds, and Pi import the
  focused owner directly. `^ⁿStrictMonotone⁻¹` remains in Sequence because its
  proof uses inverse-backed strict positive scaling, which is intentionally
  outside the current ordered-ring interface.
- 2026-07-21: checked ordered-ring theory, the focused power-order owner, the
  sequence compatibility module, all four migrated consumers, and the public
  algebra and sequence facades with `agda-codex`; every check completed with
  no holes, metas, constraints, or warnings.
- 2026-07-21: added FinVec sum theorems `∑Mono≤`, `∑Mono<`,
  `pos∑→∃pos`, and `abs∑≤∑absFinVec` to
  `Algebra.OrderedCommRing.Properties.SumTheory`. The established nonempty
  natural-index absolute bound remains intact alongside the all-length FinVec
  form.
- 2026-07-21: added the explicit `Fin→FinVec`, `foldFin+≡+∑`, and
  `foldFin+≡∑` bridge in integration summation, using the existing equivalence
  between its sigma-based `Fin` and canonical `FinData`. Replaced the local
  inductions for `foldFin+≤`, `foldFin+<`, `foldFin+<-abs`, and
  `foldFin+≤-abs` with generic sum adapters while preserving their statements.
- 2026-07-21: replaced the rational-density and dichotomy induction for
  `Bishop-Proposition7` with a transport to generic `pos∑→∃pos`. Checked
  ordered-ring theory, integration summation, derivative mean value, the direct
  partition consumer, and the public calculus facade with `agda-codex`; all
  completed with no holes, metas, constraints, or warnings.
- 2026-07-22: added generic finite-sum exchange to `Algebra.Semiring.BigOps`
  and replaced the matrix-local induction with a compatibility specialization.
  Added pointwise-difference splitting, constant-vector sums, and telescoping
  adjacent differences to `Algebra.Ring.BigOps`.
- 2026-07-22: added `FinData→Fin-weakenFin` and `FinData→Fin-fromℕ` to
  `Data.Fin.Properties`, making the weakening and final-index behavior of the
  existing finite-type equivalence explicit.
- 2026-07-22: moved the canonical real-ring numeral normalization
  `fromℕ≡fromNatℝ` to `CauchyReals.Algebra.Ring`; the Archimedean construction
  now consumes that lighter algebraic owner rather than reproving it.
- 2026-07-22: replaced integration's local inductions for accumulator shifts,
  zipped addition, scalar distribution, transposed sums, constant sums, and
  telescoping differences, together with the derived subtraction adapter, by
  the `FinVec` bridge and generic big-operator laws. Public statements are
  unchanged; only representation-specific fold and reindexing machinery
  remains local. Phase 4 is complete.
- 2026-07-22: checked `Semiring.BigOps`, `Ring.BigOps`, `Algebra.Matrix`,
  `Data.Fin.Properties`, the Cauchy-real ring and Archimedean owners,
  integration summation, its partition and integration consumers, derivative
  mean value, the real premetric consumer, and the public algebra and calculus
  facades with `agda-codex`; all completed with no holes, metas, constraints,
  or warnings.
- 2026-07-22: moved the additive group `+Groupℝ` and its natural-scalar
  helper to `Algebra.Ring`, moved the nonzero-real carrier `ℝ₋₊` and
  subtype equality to `Algebra.Order.Apartness`, and moved the continuous
  automorphism group, rational-linearity proof, and scalar classification to
  `Analysis.Continuity.AdditiveAutomorphism`. The analysis implementation no
  longer imports `RealPower.Infrastructure`; that old path preserves the
  established additive names through restricted compatibility reexports.
- 2026-07-22: moved `fromLipschitz'-rat` beside `fromLipschitz'` in
  `Analysis.Lipschitz.Extension`, exposed additive automorphisms through the
  `Analysis` facade, and migrated the exp-log group consumer to the canonical
  additive-group owner. Checked every new owner, the real-power compatibility
  module, both direct group consumers, and the `Analysis` and `Transcendental`
  facades with `agda-codex`; all completed with no holes, metas, constraints,
  or warnings.
- 2026-07-23: moved the Cauchy-real rational-expression reflection tactic to
  `Cubical.Tactics.CauchyReals.ExpressionLifting`, retained
  `Algebra.Expression.Lifting` as a compatibility facade, and migrated every
  active library consumer to the canonical tactic namespace.
- 2026-07-23: isolated the apparent nontermination in `Circle.Unwind` to
  definitional normalization of an inline dependent pair through a restricted
  inverse equivalence. Naming the concrete sigma point and the section,
  projection, adjoint, and translated paths makes `Unwind` check completely
  in 72 seconds; `PointedUnwind` then checks in 23 seconds. The canonical
  tactic, compatibility facade, and every migrated consumer now check with no
  holes, metas, constraints, or warnings. Final checks of the public
  `Algebra`, `Analysis`, and `Geometry` facades completed cleanly as well.
- 2026-07-23: added the focused predicate-uniform-continuity bridge
  `Analysis.Metric.Compatibility.Predicate`. It converts `IsUContinuousℙ`
  witnesses to generic maps out of `PremetricSubspace ℝPremetricSpace P`,
  converts an explicit generic modulus back directly, and recovers the legacy
  witness from a packaged generic map under propositional truncation. The leaf
  module and public compatibility and metric facades check with no holes,
  metas, constraints, or warnings.
- 2026-07-23: re-audited both remaining conditional items. Legacy
  `MetricSpace`, `UContMap`, and `IsIsometry` references are confined to
  `Analysis.Metric.Legacy` and the explicitly nested discrete, p-norm, and
  circle compatibility modules; only the public `Metric`/`Analysis` facades
  keep them visible beyond that boundary. `pasteAt`, `pasteAbove`, and
  `pasteAboveClosed` have no consumer outside their own implementation and
  facade, including in the pre-split history. No source deletion or speculative
  generic API was made without changing those two stated policies.
- 2026-07-23: after explicit authorization to retire the public legacy metric
  API, deleted `Analysis.Metric.Legacy`, its old `Analysis.Metric.Base` facade,
  and the discrete, p-norm, and circle compatibility modules. Removed their
  reexports from the surviving `Metric`, `Discrete`, `PNorm`, and
  `Circle.Metric` facades. The canonical premetric instances, mappings,
  Cauchy-real continuity bridges, unit-premetric aliases, and real-root p-norm
  mathematics remain.
- 2026-07-23: confirmed that no Cauchy-real Agda source still mentions a
  retired module or any of `IsMetric`, `MetricSpace`, `UContMap`, or the legacy
  `IsIsometry`. Checked `Discrete`, `PNorm`, `Circle.Metric`, `Metric`,
  `Analysis`, `Circle`, and `Geometry` with `agda-codex`; all completed with no
  holes, metas, constraints, or warnings.
