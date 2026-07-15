# Lossy-unification migration status

This records the completed targeted migration on 2026-07-14 and the module
organization adopted on 2026-07-15.

## Repository state

- Branch: `book-cauchy-reals-new-solvers`
- HEAD when the original checkpoint was written: `117647706`
- The lossy-unification proof migration was committed before the subsequent
  module-organization refactor.

## Completed migration

The targeted exponentiation files no longer use `--lossy-unification`. The
following files were checked with `agda-codex` after their proof migrations and
had exit code 0, with no holes, metas, constraints, or warnings:

- `Approximation/Base.agda`
- `RationalPower/Core.agda`
- `RationalPower/Convexity.agda`
- `RationalPower/Bernoulli.agda` (new module)
- `Logarithm/Sequence/Base.agda`
- `Logarithm/Sequence/Bernoulli.agda`
- `Logarithm/Sequence/Squares.agda`
- `Logarithm/Sequence/Inequalities.agda`
- `Logarithm/Sequence/Elementary.agda`
- `Logarithm/Sequence/Delta.agda`
- `Logarithm/Sequence/Limit.agda`
- `RealPower/Infrastructure.agda` (then `RealPowerBase.agda`)
- `RealPower/Construction.agda` (then `RealPower.agda`)
- the leaves now split out of the former `ExponentiationMore.agda`
- the aggregate `Exponentiation.agda`

A fresh targeted sweep found no `lossy-unification` pragmas. The three final
migration files also contain no explicit holes or temporary bisection markers.

## Main proof changes

### Logarithm sequence layer

- `lnSeq-one` proves `lnSeq 1 n ≡ 0` pointwise, avoiding inference through an
  expanded Cauchy limit.
- `preLn-inv` uses opaque `inverse-lnSeq-error-path` and
  `inverse-lnSeq-error-bound` helpers.
- `slope-monotone-preLn` separates the root-slope rewrite, pointwise
  inequality, and proof-relevant Cauchy-limit mapping into explicit opaque
  helpers. In particular, `preLn-slope-limit-path` retains the intermediate
  Cauchy witness for negation instead of treating it definitionally as
  `-preLn`.
- Fully typed local `leftLimit` and `rightLimit` packages remove inference over
  the dependent Cauchy witnesses in the final slope proof.

### `RealPower/Infrastructure.agda`

- Rational factors, natural indices, interval endpoints, and base/exponent
  arguments are explicit in the automorphism, slope-bound, and monotonicity
  proofs.
- The Lipschitz constant in `Σfun'` and the rational/real maximum in
  `intervalℙ→dist<` are fixed by typed local terms rather than reconstructed
  from later uses.
- The lower- and upper-slope proofs state their intermediate powers and
  rational identities explicitly, so no blocked exponent metas remain.

### `RealPower/Construction.agda`

- Proof-relevant changes of positivity witnesses are isolated by opaque paths,
  including `BDL-preLn-positive-path` and the inverse/one specializations.
- The sequence-stage function and its `BDL` components are connected by typed
  paths (`Seq-^-fun≡BDL` and its component helpers).
- `Seq-^-fun-snd≡preLn-with` exposes the logarithm endpoint directly as
  `expPreDer.expPreDer'.preLn`. This prevents clients from unfolding the large
  `BDL` module merely to align two definitionally equal representations.
- `𝒇-zero-real` exposes the real-zero endpoint directly. Derivative clients no
  longer ask conversion to reconstruct `rat zeroℚ ≡ 0` through the complete
  parameterized `BDL` construction.
- Continuity and component projections are passed through small opaque helpers
  where inference previously expanded dependent records.

### Real-power derivative layer

- The zero-point remainder estimate is exposed through an opaque
  `𝒇-derivativeAtZero` boundary.
- The everywhere estimate and tolerance chooser are opaque local helpers, and
  use the typed `𝒇-zero-real` endpoint. This removes a pathological conversion
  that otherwise expanded the parameterized construction for many minutes.
- `realPowerDerivativeProof` transports the `BDL` derivative explicitly along
  `Seq-^-fun≡BDL`, instead of depending on the intersection construction and
  its local `BDL` instance being definitionally identical.

### Former `ExponentiationMore.agda`

This catchall no longer exists. Its definitions are organized as:

- `RealPower/Definition.agda` for real power, logarithm, continuity, and basic
  laws;
- `RealPower/Composition.agda` for composition of real powers;
- `Logarithm/StrictMonotonicity.agda` for strict order estimates;
- `Logarithm/Injectivity.agda` for the inverse-Lipschitz injectivity proof.

- Migrated `rootₙ→1`, both rational clamp case lemmas, strict logarithm
  monotonicity, and `realPowerMulExponent` using explicit endpoints and typed
  sequence transports.
- `invLipPreLn` now factors the continuity argument, strict rational case,
  clamp/log endpoint paths, quotient bound, and final rational product bound
  into separately typed terms.
- `inj-ln` transports its intersection-stage equality through
  `Seq-^-fun-snd≡preLn-with` before applying inverse-Lipschitz injectivity. Its
  interval predicate is stated as `Seq⊆.𝕡 seq-^-intervals Z`, eliminating the
  final predicate meta without unfolding the interval implementation.

## Final verification commands

```bash
agda-codex Cubical/HITs/CauchyReals/Exponentiation/RealPower/Infrastructure.agda
agda-codex Cubical/HITs/CauchyReals/Exponentiation/RealPower/Construction.agda
agda-codex Cubical/HITs/CauchyReals/Exponentiation/RealPower/Definition.agda
agda-codex Cubical/HITs/CauchyReals/Exponentiation/RealPower/Composition.agda
agda-codex Cubical/HITs/CauchyReals/Exponentiation/Logarithm/StrictMonotonicity.agda
agda-codex Cubical/HITs/CauchyReals/Exponentiation/Logarithm/Injectivity.agda
agda-codex Cubical/HITs/CauchyReals/Exponentiation.agda
```

The original migration targets finished with exit code 0. The reorganized
paths are checked as part of the module-organization refactor.

## Remaining review note

The lossy-unification migration itself is complete. Before an eventual commit,
review the large `RationalPower/Convexity.agda` refactor for intentionally
retained historical comments and split or squash the uncommitted work according
to the desired commit structure. Do not delete its later active definitions
during that cleanup.
