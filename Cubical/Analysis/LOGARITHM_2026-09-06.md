# Logarithm and exponential — 2026-09-06

Updated after the choice-free cleanup and the constructive inverse development.
The former countable-choice exact-IVT and global inverse adapters remain removed.
The standing rule is in [AGENTS.md](AGENTS.md); the cleanup is recorded in
[Choice-free Analysis](CHOICE_FREE_2026-09-06.md).

## Retained development

- The entire exponential has zero, addition, and negative-argument
  reciprocal-product laws from exact Cauchy products and factorial identities.
- It is strictly positive, strictly increasing, injective, and preserves and
  reflects weak order. It has a linear lower bound on nonnegative inputs and
  an explicit positive-target bracket `[-1/y,y]`.
- Exponential continuity, uniform continuity on closed intervals, inverse-
  distance estimates on lower-bounded half-lines, and the global self-
  derivative theorem are checked without choice assumptions.
- A reusable approximate intermediate-value theorem uses finite partitions
  and overlapping located comparisons. It needs neither monotonicity nor
  exact real comparison. It returns a truncated approximate preimage, not an
  exact preimage or a coherently chosen infinite family.
- The local series `F(x) = x + x²/2 + x³/3 + ⋯` is constructed for
  `|x|<1`, with absolute convergence, uniform convergence on every closed
  rational subunit radius, proof-independent values, `F(0)=0`, continuity,
  and derivative `F′(x)=1/(1-x)`.
- Generic logarithm laws accept an independently supplied proof that the
  exponential is an equivalence. They prove both inverse identities,
  uniqueness, independence of that proof, the value at one, product and
  reciprocal laws, order, continuity, and the reciprocal derivative. They
  do not themselves construct the equivalence. The new `Global` module now
  instantiates them with the constructive equivalence described below.
- Shared slack estimates and strict-order reflection from continuity remain
  in general-purpose modules and are reused by the trigonometric proofs.

## Constructive exponential equivalence

`Functions/Exponential/Inverse.agda` now proves `expPositive-isEquiv` and
exports `expPositiveEquiv : ℝ ≃ ℝ>0`, without any choice assumption.

For a positive target `y`, use the explicit bracket `a=-1/y`, `b=y` and set
`R=|a|+|b|`, `c=exp(-R)`. The deterministic recurrence is

```text
x₀ = a
xₙ₊₁ = xₙ + c (y - exp xₙ).
```

`InverseIteration.agda` proves that the iterates remain in `[a,b]`, increase,
and satisfy `exp xₙ ≤ y`. Their residuals contract with
`q=1-c exp(a)`, where `0≤q<1`. Thus successive increments are dominated by
a convergent geometric series. `Sequence/Geometric.agda` supplies a native
Cauchy witness by summing and telescoping those increments. Continuity and
ordered limits then prove `exp(lim xₙ)=y`; existing injectivity completes the
equivalence.

The only auxiliary selections are single truncated rational bounds on the
contraction and leading coefficient. They are eliminated into the proposition
`SeqWitness`; no precision-indexed family is selected. The new
`Series/Geometric/Real.agda` similarly proves geometric convergence directly
from `|q|<1` by constructing one common quantitative bound.

## Public entry points

`Cubical.Analysis.Real.Functions.Exponential` exposes
`expℝ : ℝ → ℝ` and `expPositive : ℝ → ℝ>0`.
`expPositive-value` exposes the underlying real value, and
`exponentialHasSelfDerivative` in its derivative module proves `exp′=exp`.

`Cubical.Analysis.Real.Series.PowerSeries.Logarithm` exposes the actual
choice-free local series `negativeLogOneMinus`, including closed-radius
and open-unit restrictions.

`Cubical.Analysis.Real.Functions.Logarithm` now exposes:

```agda
logℝ : ℝ>0 → ℝ
expPositive-logℝ : ∀ y → expPositive (logℝ y) ≡ y
expℝ-logℝ : ∀ y → expℝ (logℝ y) ≡ fst y
logℝ-expPositive : ∀ x → logℝ (expPositive x) ≡ x
```

Its `Global` module specializes the existing uniqueness, value-at-one,
product, reciprocal, injectivity, order, continuity, and derivative laws.
The generic `logarithmFromEquivalence` interface remains available for reuse;
ordinary callers no longer need to supply its equivalence obligation.
`logPositiveEquiv : ℝ>0 ≃ ℝ` packages the named logarithm in the reverse
direction. `logℝ-atOne` states the value-at-one law using an explicit equality
of the underlying input with `1ℝ`, avoiding expensive concrete-unit reduction.

## Multiplicative group and exp/log isomorphisms

`Real/Algebra/MultiplicativeGroup.agda` now supplies `ℝ>0AbGroup` and
`ℝ>0Group`. Their carrier is the existing positive-real subtype `ℝ>0`,
their operation is the existing `_·>0_`, their unit is `1>0`, and their
inverse is `positiveInverse`, the positive reciprocal. Associativity,
commutativity, both unit laws, and both inverse laws are proved directly from
real arithmetic. This module does not import exponential or logarithm and
does not define multiplication by transporting addition along an equivalence.
It also exposes inverse involution, the inverse of one, positive division
`_/>0_`, and division by self/one.

`Real/Functions/Logarithm/Group.agda` packages the previously established
choice-free inverse as standard library algebraic maps:

```agda
expPositiveGroupIso : GroupIso (AbGroup→Group ℝAbGroup) ℝ>0Group
logℝGroupIso : GroupIso ℝ>0Group (AbGroup→Group ℝAbGroup)
```

Both directions also have `GroupHom`, `GroupEquiv`, and `AbGroupEquiv`
bundles. The `GroupIso` forward and inverse maps are explicitly the named
`expPositive` and `logℝ`, with their already checked round-trip laws.
Homomorphism proofs reuse exponential addition and logarithm product laws;
the generic group API then supplies preservation of unit and inverse.
The resulting named laws include `expPositive-zero`,
`expPositive-negative`, `logℝ-one`, `logℝ-positiveInverse`,
`expPositive-sub`, and `logℝ-quotient`. These respectively express
`exp(0)=1`, `exp(-x)=1/exp(x)`, `log(1)=0`, `log(1/x)=-log(x)`,
`exp(x-y)=exp(x)/exp(y)`, and `log(x/y)=log(x)-log(y)`.

The algebra and logarithm facades re-export these modules. The multiplicative
domain is deliberately **positive** reals: all reals are not a multiplicative
group because zero has no inverse, and the multiplicative group of signed
nonzero reals cannot be isomorphic to the additive reals because of its
nonidentity element of order two, `-1`. No signed multiplicative group is
claimed or introduced in this pass.

Elaboration lesson: keeping the positive unit and positive reciprocal opaque,
with explicit projection paths, prevents their positivity witnesses from
being unfolded throughout completed-real calculations. Two optional direct
corollaries (product inverse and division cancellation) were not retained
after expensive conversion; the standard group laws and isomorphism proofs
check without them, and ordinary `GroupTheory` remains applicable to the
bundled group. This is not a missing group axiom or a conditional result.

## Remaining constructive boundary

The local series has the expected coefficients and derivative, but its
exponential inverse identity is not yet established. Its descriptive name
does not replace an exp/log compatibility theorem.

The separate series construction `t=(y-1)/(y+1)` and
`L(y)=F(t)-F(-t)` for `y>0` is now implemented as `logarithmSeries` in
`Functions/Logarithm/Construction.agda`. Both arguments are proved to lie
in `(-1,1)`, `(1-t)y=1+t` is checked, and the candidate vanishes at one.
Its equality with `logℝ` remains unproved. Proving `exp(L(y))=y` needs local
exp/log compatibility, for example
via power-series composition or suitable derivative-uniqueness machinery.
The current mean-value theorem requires uniform derivative estimates.
New `Difference/UniformDerivative` modules establish the generic uniform
power-series remainder via uniform continuity of difference factors;
`Logarithm/UniformDerivative.agda` supplies the local-series specialization
on every closed rational subunit radius. The corresponding composition and
product compatibility proof remains future work.

Do not restore the removed choice-based inverse route. The arithmetic
iteration already constructs the global inverse with native Cauchy data;
the remaining series identities are independent compatibility theorems.

## Elaboration findings

Proof-bearing completed-real values can trigger large normalization inside
the entire exponential. Keeping `expPositive` opaque with a projection law,
and transporting arguments before applying the exponential, avoids this.
The generic `log(1)=0` proof checks efficiently through the inverse return
law and an explicit positive-real equality. These are proof-structure changes,
not weakened statements or compiler options.

The inverse iteration's state, recurrence paths, bounds, and limit are kept
opaque. Keeping the specialized geometric estimates with their arithmetic
invariant avoids costly conversion through imported module aliases.
The named `logℝ` likewise has an explicit `logℝ-value` path to the generic
inverse; laws are transported along this path rather than asking Agda to
normalize a completed exponential around a function alias. All helper inputs
that affect real-valued expressions need explicit types: unresolved metas
can otherwise trigger large, unproductive normalization.

Generic factorial/binomial lemmas currently imported from
`Trigonometric/Addition/DividedPowers` could move to a shared power-series
module. Exponential continuity and derivative specializations could also
share more setup after careful dependency-layering work.

An optional natural-power/zero/sign corollary module was not retained because
its concrete positive-unit specializations triggered excessive conversion.
There are no holes or placeholder declarations for those corollaries. The
later group-isomorphism layer now supplies the zero and negation laws through
unit/inverse preservation, without that concrete-unit normalization.

## Verification of the global inverse pass

- All **19 changed/new Agda files** were checked after their final edits with
  `agda-codex --codex-format=json`. `Cubical/Analysis/Everything.agda` and
  `Cubical/Analysis.agda` also passed: **21 clean checks**, exit code 0,
  with zero holes, unsolved metas, constraints, or warnings.
- The import audit reaches all **416 Analysis modules** from `Everything`,
  with no missing imports or orphan modules.
- The source/document audit found no forbidden choice schema or adapter
  references in Analysis; no postulates or unsafe pragmas were added.
- An independent review checked the iteration invariant, contraction,
  native-Cauchy construction, and truncation eliminations.
- `git diff --check` is clean. Earlier unrelated working-tree changes were
  preserved. The earlier removal checks remain recorded in
  [Choice-free Analysis](CHOICE_FREE_2026-09-06.md).

## Verification of the multiplicative-group pass

- Both new group modules and both edited facades passed final
  `agda-codex --codex-format=json` checks. `Cubical/Analysis/Everything.agda`
  and `Cubical/Analysis.agda` passed too: **six clean checks**, exit code 0,
  with zero holes, unsolved metas, constraints, or warnings.
- All **418 Analysis modules** are reachable from `Everything`, with no
  missing Analysis imports or orphan modules.
- The source/document choice audit remains clean; no postulates, unsafe
  pragmas, choice assumptions, or conditional inverse adapters were added.
- `git diff --check` is clean. Pre-existing work was preserved; this pass
  changed only the two new modules, their two facades, and the progress notes.
