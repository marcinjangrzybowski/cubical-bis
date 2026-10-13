# Native real trigonometric identities

The public entry point is `Cubical.Analysis.Real.Series.PowerSeries.Trigonometric`.
All statements concern the sequential-completion reals of `Cubical.Analysis`.
The HIT Cauchy-real development supplies a comparison of mathematical results,
not a carrier equivalence or a source of transported proofs.

## Comparison with HIT Cauchy reals

The audit covers real sine/cosine identities in
`Cubical/HITs/CauchyReals/Trigonometry/{Base,Pi,Identities}.agda`, together with
the periodicity formulas in `Circle/Core.agda` and the real parity and
monotonicity prerequisites in `ArcSin/Prelim`. Existing native proofs are
reused. All sine/cosine equations in HIT `Trigonometry/Identities.agda` have
native counterparts below; its auxiliary rational-injectivity lemma is not
a trigonometric identity.

| HIT result | Native Analysis result | Work in this tranche |
| --- | --- | --- |
| Values at zero; sine odd and cosine even | `Entire`, `Parity` | Already present |
| Addition laws | `sinℝ-add`, `cosℝ-add` in `Addition` | Already present |
| Pythagorean identity in product form | `sin²+cos²≡1` in `Pythagorean` | Already present |
| Pythagorean identity with natural powers; complementary squares | `sinℝ-pow²+cosℝ-pow²≡1`, `sinℝ-square-complement`, `cosℝ-square-complement` in `Identities.Squares` | Derived from the existing product identity |
| Double-angle cosine, including `1−2sin² x` and `2cos² x−1` | `Identities` already proves the doubled-sum/product forms; `cosℝ-two-mul`, `cosℝ-two-mul-sinSquare`, `cosℝ-two-mul-cosSquare` give the coefficient/power forms | Added coefficient/power corollaries and `sinℝ-two-mul` |
| `sin(π/2)=1`, quarter-turn shifts, half-turn sign changes, `2π` periodicity | `Pi.Value` | Already present, with unconditional native π |
| `cos x = −sin(x−π/2)` | `cosℝ≡neg-sinℝ-sub-halfPiℝ` in `Pi.Reflection` | Added, with both negative shifts and reflections about half/full turns |
| Integer-period invariance in circle turn coordinates | `sinℝ-equal-turns`, `cosℝ-equal-turns` in `Pi.IntegerPeriod` | Added using the native integer embedding |
| Global sine/cosine difference bounds with constant one; Lipschitz continuity | `sinℝ-difference-bound`, `cosℝ-difference-bound`, `sinℝ-isNonExpanding`, `cosℝ-isNonExpanding` in `Estimates.NonExpanding` | Derived from native uniform derivatives and mean-value bounds |
| `∫sin = cos a − cos b`, `∫cos = sin b − sin a` | `sinℝ-hasRiemannIntegral`, `cosℝ-hasRiemannIntegral`, `integral-sinℝ`, `integral-cosℝ` in `Integrals` | Constructed directly by native FTC |
| Cosine of absolute value and positivity on the symmetric quarter interval; sine monotonicity there | `QuarterTurn.Injectivity.AbsoluteCosine`, `Bounds`, `StrictMonotonicity` | Already present |

`Estimates.AdditionDerived` already proved the subtraction laws and the two
displacement expansions. These are now re-exported by the trigonometric
facade rather than reproved. The existing
`sinℝ-quarterTurnDifference x y` is the unrestricted sum-to-product identity
for `sin y − sin x`; despite its module/name, it has no quarter-interval
hypothesis.

## Additional identities

- `Identities.Products` supplies all four sine/cosine product-to-sum formulas,
  both doubled and with a rational half factor, plus the sine/cosine sum and
  cosine difference factorizations. The existing sine difference proof is
  reused.
- `Identities.Squares` supplies power reduction and squared half-angle
  formulas. These do not choose a square-root sign.
- `Pi.Reflection` supplies the cofunction formulas at `halfPiℝ − x`, the
  reflections at `piℝ − x` and `twoPiℝ − x`, and negative period shifts.
- `Pi.IntegerPeriod` also proves invariance under adding any integer multiple
  of `twoPiℝ`, and the sine/cosine values at those multiples.
- `Estimates.NonExpanding` also gives `|sin x| ≤ |x|`.

`quarterTurnHalf ⋆ x` is the native rational scalar action by `1/2`;
`realNatural 2 · x` and `powℝ x 2` give the usual coefficient/power notation.
Some subtraction arguments are written `x + (- y)` to avoid normalizing the
power-series implementation during elaboration. This is the same native real
subtraction.

The integral witnesses require no independently supplied integrability or
chosen continuity modulus. Equality with any supplied integral value requires
`a ≤ℝ b`, as does uniqueness in the native ordered-interval integration API.

## Constructive boundaries

The algebra uses Analysis ring laws and its existing addition/Pythagorean
proofs. Bounds use radiuswise uniform derivatives, constructive closed-bound
order cases, and the native absolute-difference metric. Only propositional
targets eliminate truncated data; no family of radii or approximations is
chosen. None of these modules imports `Cubical.HITs.CauchyReals`.

The HIT complex trigonometric identities concern a different carrier and are
outside this real identity comparison. Exact restricted sine/cosine inverses
are now constructed in `Pi/InverseValue.agda`, using deterministic iteration
and an explicit rational reflection modulus; see
[the construction](QuarterTurn/Restriction/README.md). The Cartesian unit
circle equivalence remains separate work. Existing conditional inverse laws
and finite approximate image density are preserved.

## Verification

On 2026-10-08, `agda-codex` checked all six new theorem modules, the `Pi` and
`Trigonometric` facades, `Cubical/Analysis/Everything.agda`, and
`Cubical/Analysis.agda`: exit code 0, no holes, unsolved metas, constraints,
or warnings. An import-closure audit of the six modules found no HIT
Cauchy-real imports. No postulates, unsafe options, or choice assumptions
were added.
