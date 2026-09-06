# Analysis improvements — 2026-09-05

Starting revision: `d947f1182`. The working tree was clean, and the previous
review checked all 363 Analysis modules successfully.

Updated after the [choice-free cleanup](CHOICE_FREE_2026-09-06.md): the former
choice-dependent exact inverse adapters are no longer present. The original
verification figures below are historical, not counts for the current tree.

## Implementation plan

1. Centralize repeated additive identities and elementary continuity proofs.
2. Reuse the symmetric-interval bound helper in `Domain.Radius`.
3. Add a backwards-compatible ordered-domain integration API, making the
   endpoint-order requirement explicit and keeping legacy definitions intact.
4. Derive inverse-trigonometric zero values, parity, and monotonicity.
5. Complete the exact mean-value endpoint bound and interval-local variant.
6. Complete finite slack-bisection toward restricted-sine approximate density.
   Exact surjectivity remains a separate constructive obligation.

Three subagents developed the analytic items in disjoint work areas; the
mean-value agent subsequently implemented the ordered integration wrapper.
The main agent handled shared algebra, exports, integration checks, and this
log. Independent read-only reviews covered the mean-value/partition and
bisection proofs. No postulates, unsafe options, or weakened statements
were introduced.

## Progress

- Initial review confirmed duplicate additive identities and continuity
  proofs. Shared helpers were placed in lightweight modules to avoid
  introducing dependency cycles in the foundational algebra.
- Added checked `AdditiveGroup.Properties` with opaque subtraction/cancellation
  identities, and `Real.Mappings` with generic real-valued constant-map
  continuity/nonexpansiveness and real identity continuity. Replaced repeated
  proof bodies in their clients while preserving existing signatures.
- `Domain.Radius` now uses `symmetricIntervalFromAbsBound`; its redundant
  private order-conversion proof was removed. The changed module checks.
- New inverse modules prove zero values, endpoint values, oddness of arcsine,
  `arccos(-x) = pi - arccos(x)`, and both weak and strict monotonicity.
  Characterized-pi adapters preserve the existing conditional construction.
  Strict order reflection uses continuity and locatedness, not a classical
  conversion from inequality to apartness.
- The exact mean-value endpoint bound and interval-local version check:
  `abs(f b - f a) <= bound * (b - a)`. The epsilon slack is removed using
  dyadic radii and order preservation under limits. Assumptions remain the
  radiuswise-uniform derivative remainder estimate; the result does not
  pretend to derive uniform differentiability from pointwise differentiability.
- Added checked partition-point endpoint bounds and endpoint-order recovery,
  including the zero-cell case. The old partition-bound API is retained as
  a specialization of a core needing assumptions only at partition nodes.
- Added `RiemannIntegral.Ordered` and its properties: ordered endpoints are
  bundled once, legacy integral witnesses are reused definitionally, and
  uniqueness no longer needs a separately supplied ordering proof. Constant,
  addition, negation, subtraction, and scaling adapters are checked. Regression
  theorems cover zero-width constants and reversed-endpoint vacuity in the
  unchanged legacy predicate; this wrapper does not define signed integrals.
- Completed finite slack-bisection: initial brackets, overlapping midpoint
  branches, exact halving of widths, finite iteration, small-width limits, and
  a sine oscillation/error estimate. `sineQuarterApproximateImageDensityByBisection`
  proves approximate density from quarter-turn endpoint laws and a nonnegative
  quarter alone. No first-zero property, monotonicity, or choice is used here.
- The former choice-based bridge from finite density to exact restricted
  sine/cosine equivalences was removed. The retained named inverse APIs need
  an independently supplied equivalence or intermediate-value witness.
- Public facades now expose the new algebra, mappings, partition/integration,
  mean-value, bisection, and inverse results. Independent agent reviews found
  no issues in the mean-value/partition or bisection proofs, including
  zero-cell partitions, degenerate bounds, closed target endpoints, and the
  factor-of-two slack calculation. Bisection proves finite approximate
  existence under truncation, not an untruncated numerical search algorithm.
- The four shared additive identities now each have exactly one definition
  in Analysis. Constant/identity continuity proof bodies were consolidated
  across ten modules, keeping lightweight typed aliases where useful.

## Implementation findings

- Generic opaque identities keep proofs over completed trigonometric values
  from expanding their implementation during normalization. Typed endpoints
  and syntactically matching terms still matter at transported inequalities.
- Bundling interval endpoints as dependent pairs reuses the existing integral
  predicates definitionally and avoids proof-bearing record normalization.
- Finite bisection does not need a positive endpoint slope, rational-valued
  function evaluation, or a rational bound on the exponential majorant. The
  shrinking width multiplied by that fixed real majorant tends to zero.
- Exact slack elimination uses canonical dyadic radii and proposition-valued
  truncation elimination; it does not choose a sequence of fine partitions.
- Foundational helper changes invalidate many dependents. Individual clean
  checks and a final stable aggregate check are both needed; transient
  dependency/import warnings were fixed before final verification.

## Remaining mathematical boundaries

- `CharacterizedHalfPi` is still a supplied input, not a constructed inhabitant.
  Bishop/damped iteration convergence and positivity before the limit remain
  needed for an unconditional `piℝ`.
- Exact restricted-sine IVT still needs a
  coherent native-Cauchy construction or another completion argument. Finite
  density alone must not be advertised as choice-free exact surjectivity.
- The mean-value inequality needs radiuswise-uniform remainder estimates.
  Supplying them for sine/cosine and deriving exact global one-Lipschitz bounds
  remain useful next steps toward the damped Bishop contraction.
- The ordered integral API does not establish general integrability of
  uniformly continuous functions or introduce oriented/signed intervals.

## Final verification

- Import-graph audit: **380 Analysis modules**, all reachable from
  `Cubical.Analysis.Everything` (17 new modules in this pass).
- After the last Agda edit, ran `agda-codex --codex-format=json` individually
  on all **57 changed/new Agda files**, followed by
  `Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda`.
- **All 59 commands exited 0**. Every diagnostic reported the current source,
  zero visible holes, zero unsolved metas, zero constraints, and zero warnings.
  The final sequential verification run took 367.1 seconds, including the
  dependency rebuild after foundational cleanup.
- `git diff --check` passed. All changes are confined to `Cubical/Analysis/`;
  no postulates, unsafe pragmas, weakened options, or external dependencies
  were added. The later cleanup intentionally removes choice-dependent public
  signatures; choice-free mathematical results from this pass are retained.
- Starting revision remains `d947f1182`; this follow-up implementation is
  left in the working tree, uncommitted.
