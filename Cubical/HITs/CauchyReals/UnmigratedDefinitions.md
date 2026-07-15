# Unmigrated and Commented Cauchy-real Definitions

This catalogue complements [MigratedDefinitions.md](MigratedDefinitions.md). It covers:

- every module currently under `Cubical/HITs/CauchyReals/Dirty`;
- every named definition found inside line or block comments under
  `Cubical/HITs/CauchyReals`, including its subdirectories;
- anonymous evaluator goals when they affect the apparent completeness of a file.

Disabled imports, `unfolding` lists, previous-name comments, prose, and isolated proof
fragments without a declaration are not treated as definitions.

## Status legend

- **Checked**: active code reached a checked semantic state with `agda-codex`.
- **Source-complete**: commented code has a body and no visible hole, but is not checked.
- **Partial**: a substantial body exists, but it contains holes or missing context.
- **Stub**: only a statement or a hole-sized sketch exists.
- **Migrated**: a checked equivalent exists in the clean tree.
- **Experiment**: evaluator/demo code rather than reusable mathematics.
- **Small / medium / large**: estimated work to fit the current imports, names, and APIs.
- **Restate**: the current statement is malformed, false, or lacks a necessary hypothesis.

The estimates are about migration into the current architecture, not merely making an
old text typecheck by restoring compatibility aliases.

## Executive summary

The clean-tree recovery pass is complete. Checked replacements now exist for inverse
differentiation, real-power and logarithm derivatives, exp/log laws and group
isomorphisms, positive-base real-power continuity and strict monotonicity, real-power
factorization, lower real-power slope bounds, alternating series, endpoint extension,
pasting, generic continuous order comparison, and the Cauchy-real universal property.

A fresh scan finds no disabled named declaration or commented proof hole in the clean
`CauchyReals` tree. False, malformed, duplicated, and superseded drafts were removed
after their status or replacement was established. In particular, `𝕣-lim'←`,
`𝕣-lim'≃`, `clamp-Δ-·f'`, the malformed real-power interval draft, and the
hypothesis-free `0≤ᵣlnSeq` statement were not retained.

One mathematically valid result from the old comments remains deferred rather than
migrated: secant-slope monotonicity of `x ↦ x ^ y` in the positive base for `1 ≤ y`.
Its old body called a rational theorem named `slope-monotone-^ℚ`; that theorem is not
present in this repository or its history. There is currently no checked consumer of
the result, so adding a postulate or rebuilding a large convexity development would be
the wrong completion criterion for this cleanup pass.

## Dirty compiler snapshot

These checks were run with `agda-codex --codex-format=json` on 2026-07-13. No check
exceeded 45 seconds.

| Module | Compiler result | Immediate cause |
| --- | --- | --- |
| `Dirty/AproxDemo.agda` | Exit 10, checked with holes | One anonymous `ℕ` evaluator hole. |
| `Dirty/ExpExtended.agda` | Exit 10, checked with holes | Positivity proof in `expℚclamped` and one anonymous rational result. |
| `Dirty/NthRootEvalTest.agda` | Exit 10, checked with holes | `t0'` asks Agda to evaluate `t0`. |
| `Dirty/TypesDemo.agda` | Exit 10, checked with holes | Positivity proof in `expℚclamped`. |

## Dirty modules

### `Dirty/AproxDemo.agda`

This is evaluator code built around the old rational `ℚIncrFunBisect` interface. The
root constructions duplicate the checked `Bisection`/`NthRoot` development.

| Definition | What it contains | Completeness and migration |
| --- | --- | --- |
| `Sqrt2.icsSqrt2`, `Sqrt2.sqrt2` | Cauchy proof and real limit of rational bisection for `x^2 = 2`. | Checked. Migrated in general form; no port needed. |
| `Sqrt2.sqrt2-val`, `Sqrt2.sqrt2-val'` | Rational approximation demos for `3√2`. | Checked experiments. |
| `NthRoot.fQ`, `NthRoot.n'` | Chooses a rational bisection upper bound. | Checked, old API, duplicated by clean nth-root machinery. |
| `NthRoot.icsNthRoot`, `NthRoot.nthRootℚ₊` | Cauchy proof and limit for a rational positive nth root. | Checked, but superseded by `NthRoot`. |
| `NthRoot.val` | Exposes `getApproxVal` for the constructed root. | Checked experiment. |
| `fromConstSeq` | Constructs zero from a constant Cauchy sequence. | Checked API experiment; no migration needed. |
| `realNum`, `realNum'` | Example roots `13^(1/7)` and `11^(1/3)`. | Checked experiments. |
| `ratAprox` | Approximation of their product. | Checked experiment. |
| anonymous `_` declarations | Decimal/rational evaluator requests. | All check except the explicit `ℕ` hole near the end. |
| `Aprox-𝓮.eAprox`, `Aprox-𝓮.𝑒Aprox`, `Aprox-𝓮.e-dgts` | Computed and hard-coded approximations of Euler's number. | Checked experiments; one adjacent anonymous goal is a hole. |
| `c1` | Reduced numerator/denominator inspection for a root approximation. | Commented experiment, apparently complete. |
| `digits` | Local rational decimal extraction. | Source-complete but superseded by active `Approximation.Recovery.digits`. |
| `ℯDigits` | Decimal extraction from the old exponential fraction sequence; local values are `frac`, `num`, `den`, `integerPart`, and `fractionalPart`. | Source-complete evaluator tied to old sequence names. No theorem migration value. |
| `ttt`, `zzz`, `zzzz`, `sinAprox`, `zz` | Scratch values and evaluator holes. | Incomplete experiments. |
| two `𝑒N` sketches | Incompatible sketches for an approximation witness and for `𝑒` itself. | Commented holes; discard. |

### `Dirty/ExpExtended.agda`

This tests extension of a rational function by `fromLipschitz`; it is not a completed
alternative exponential construction.

| Definition | What it contains | Completeness and migration |
| --- | --- | --- |
| `LipshitzProofIrrelTest.testL`, `test-f`, `testA` | Extends rational embedding to reals and evaluates it, parameterized by a Lipschitz proof. | Checked experiment. Small move only if retained as a regression test; fix `Lipshitz` spelling. |
| `expℚclamped` | Intended positive, clamped rational exponential input. | One positivity hole; the actual clamp body is commented. Superseded by clean exponential machinery. |
| `L` | Candidate Lipschitz constant `4`. | Checked experiment. |
| `expℝ-L`, `expℝ` | `fromLipschitz` extension, conditional on an unproved `expLip`. | Checked under the parameter, but not a construction of exponential by itself. |
| live `eAprox` and anonymous results | Evaluations of the conditional extension. | One anonymous rational hole; experimental only. |
| commented `eAprox'`, `eAprox` and anonymous goals | Alternative nested exponential evaluations. | Incomplete experiments. |

Use `Exponentiation.Series.Base.expℝ` for actual mathematics. Porting this file
would be a redesign of a test, not recovery of a missing theorem.

### `Dirty/NthRootEvalTest.agda`

| Definition | What it contains | Completeness and migration |
| --- | --- | --- |
| `t0` | The type of a two-digit approximation of `√4` using the checked root API. | Checked evaluator expression. |
| `t0'` | Requests Agda to synthesize/evaluate `t0`. | Explicit hole. Keep only as a local evaluator regression test. |

### `Dirty/TypesDemo.agda`

This combines the same old bisection root demo as `AproxDemo` with the same conditional
Lipschitz exponential experiment as `ExpExtended`.

| Definition | What it contains | Completeness and migration |
| --- | --- | --- |
| `NthRoot.fQ`, `NthRoot.n'`, `NthRoot.icsNthRoot`, `NthRoot.nthRootℚ₊` | Old rational-bisection construction of positive nth roots. | Checked but superseded by clean `Bisection`/`NthRoot`. |
| `expℚclamped` | Intended clamped rational exponential. | One positivity hole; alternate clamp body is commented. Superseded. |
| `L`, `expℝ-L` | Conditional Lipschitz extension. | Checked under an unproved `expLip` parameter. Experiment only. |
| `exp`, `_√_`, `🧙`, `🔮` | Local aliases for the conditional exponential, old root, approximation, and decimal extraction. | Checked once the surrounding parameter and hole are accepted. API/type demo only. |
| anonymous `_` declarations | Large rational and decimal evaluator values. | Checked; no reusable theorem content. |

## Clean-tree commented-code status

As of 2026-07-13, a recursive scan of every Agda module outside `Dirty/` finds no
commented named declaration and no commented explicit hole. Remaining comments are
provenance notes, book theorem references, explanations of active proofs, and local
TODO notes; they are not disabled APIs.

The cleanup resolved the previous catalogue as follows:

- Integration scaling is active as `integral'-pre·<` and `integral'-pre·` in
  `Calculus/Integration/Base.agda`.
- Predicate-indexed order extension moved to `Analysis/Continuity/Order.agda`.
- Rational power order reflection and exponent monotonicity moved to
  `Algebra/Power/Order.agda`.
- The Cauchy-real universal property moved to `Foundation/UniversalProperty.agda`.
- Positive-base real-power continuity, factorization, and strict monotonicity moved to
  `Exponentiation/RealPower/BaseContinuity.agda`,
  `Exponentiation/RealPower/Laws.agda`, and
  `Exponentiation/RealPower/BaseOrder.agda`.
- The nonzero-real group decomposition moved to
  `Exponentiation/RealPower/NonzeroRealGroup.agda`.
- `preLn<0` is active in `Exponentiation/Logarithm/Sequence/Limit.agda`, and
  the positive unit-fraction bound is active as `∃UnitFractionBelowℝ₊` in
  `Foundation/Order/Bounds.agda`.
- Bernoulli's strict rational-power estimate was already checked in
  `Exponentiation/RationalPower/Convexity.agda`.
- Old sequence, finite-sum, closeness, power, inverse, approximation, partition, and
  logarithm drafts were either replaced by the checked APIs above or removed after
  being shown false, malformed, redundant, or evaluator-only.

## Deferred result

### Positive-base real-power secant slopes

The old `slope-monotone-^ᵣ` draft asserted that, for positive endpoints
`a < b` and `a' < b'` with `a ≤ a'`, `b ≤ b'`, and `1 ≤ y`, the secant
slope of `x ↦ x ^ y` on `[a,b]` is at most its secant slope on `[a',b']`.

The statement is mathematically valid, but the displayed proof reduced it to
`slope-monotone-^ℚ`, a rational-exponent theorem about variation in the base that
has never been defined in this repository. Existing `Convexity.slope-monotone`
instead varies the exponent for a fixed base, so it cannot fill that role.

A sound future implementation should first establish rational base convexity, for
example a checked theorem of the following shape:

```agda
rationalPowerBaseSecantMonotone :
  (a b a' b' : ℝ₊) (q : ℚ) →
  1 ℚ.≤ q →
  fst a <ᵣ fst b →
  fst a' <ᵣ fst b' →
  fst a ≤ᵣ fst a' →
  fst b ≤ᵣ fst b' →
  -- ordered secant slopes for x ↦ x ^ℚ q
  ...
```

Only after that theorem exists should continuity in the exponent be used to lift the
result to real `y`. No checked module currently imports or requires this result.

## Completed action plan

1. Removed the unprovable `Dirty/ExpLog.agda` module.
2. Recovered the valid high-value real-power, order, logarithm, algebra, and integration
   helpers in focused checked modules.
3. Removed superseded, false, malformed, and duplicate commented source after verifying
   the corresponding checked replacement or the defect in the old statement.
4. Kept evaluator/demo modules quarantined under `Dirty/`; none participates in the
   clean analysis import graph.
5. Deferred only the independent secant-slope theorem whose prerequisite mathematics
   is genuinely absent.

## Remaining work

- Keep the four `Dirty/` modules as optional evaluator tests, or delete them in a
  separate experiment-cleanup change.
- Develop rational base convexity only when a concrete theorem consumes it.
- Treat removal of the remaining `--lossy-unification` pragmas as a separate compiler
  performance and elaboration project; it is not hidden commented-code migration.
