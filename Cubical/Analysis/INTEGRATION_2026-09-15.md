# Integration and FTC consequences — 2026-09-15

This extends the [initial FTC development](FTC_2026-09-15.md). All results use
the sequence-backed `Cubical.Analysis.Real.Base.ℝ`. The public entry points
are `Cubical.Analysis.Real.Integration` and `Cubical.Analysis`.

The next tranche, [Boundedness, derivative limits, and series](LIMITS_2026-09-15.md),
adds automatic bounds for uniformly continuous integrands and substitution,
uniform convergence of integral functions, derivative limit theorems, and
termwise differentiation of series.

## Integral comparison and local equality

[`RiemannIntegral.Comparison`](Real/Integration/RiemannIntegral/Comparison.agda)
proves monotonicity, nonnegativity, and constant lower/upper bounds on ordered
intervals. It also proves the quantitative estimate

```text
|f(x) - g(x)| ≤ E on [a,b]
⇒ |∫[a,b] f - ∫[a,b] g| ≤ (b-a) E.
```

Both integrals are supplied in this comparison theorem. Pointwise bounds
only concern the integration interval. The corresponding tagged-sum estimates
hold for every tagged partition, including zero-cell partitions.

[`RiemannIntegral.Extensionality`](Real/Integration/RiemannIntegral/Extensionality.agda)
transfers integral witnesses between functions equal on the interval.
Every function has integral zero on `[a,a]`, with no continuity assumption.

[`RiemannIntegral.Error`](Real/Integration/RiemannIntegral/Error.agda)
turns uniform metric errors into errors of sums and integrals using an
explicit positive rational upper bound for the interval length.

## Uniform limits and series

[`Sequence.Uniform`](Real/Sequence/Uniform.agda) distinguishes:

- `IsUniformLimit`: a separately truncated tail index for each tolerance;
- `UniformLimitWitness`: mere existence of a single convergence modulus.

These predicates have pointwise, uniqueness, and restriction helpers.

[`RiemannIntegral.UniformLimit`](Real/Integration/RiemannIntegral/UniformLimit.agda)
provides three complementary results:

1. `integralsConvergeUnderUniformLimit`: if the approximants and limit are
   integrable, radiuswise uniform convergence implies convergence of their
   integral values.
2. `uniformLimitPreservesIntegral`: if the approximant integral values
   already converge, their limit is the integral of the uniform limit.
   This also needs only radiuswise uniform convergence of functions.
3. `uniformLimitIsRiemannIntegrableOn`: integrable approximants and a
   `UniformLimitWitness` construct the limit function's integral. The supplied
   modulus produces native Cauchy data for the sequence of integral values.

No separately truncated tails are assembled into a modulus. The finite
choices used at one requested tolerance are combined with natural-number
maximum. Existential elimination for constructing a value targets the
proposition of having the unique integral on an ordered interval.

[`Integration.Series`](Real/Integration/Series.agda) proves integration of
finite partial sums, termwise integration when both limits are supplied,
and an existence theorem from `UniformlyCauchySeries` on the interval.
`integrateUniformlyCauchySeries` constructs one value which is both the
integral of the uniform sum and the sum of the term integrals. Each term
integral is supplied. The sum function is identified by `UniformHasSum`.

The supporting [`Series.Uniform.Limit`](Real/Series/Uniform/Limit.agda)
constructs a uniform convergence modulus by explicitly rescaling the native
uniform Cauchy modulus and using the existing late-term limit estimate.

## Oriented integrals within an interval

[`IntervalIntegral`](Real/Integration/IntervalIntegral.agda) takes ordered
ambient endpoints and integrability on all ordered subintervals. It defines

```text
between x y = value y - value x,     value x = ∫[a,x] f.
```

The points `x` and `y` lie in the ambient closed interval; they need not be
ordered. Checked laws include:

- zero length, reversal, and additivity through any intermediate point;
- independence of the chosen basepoint for differences;
- agreement with the semantic tagged integral when `x ≤ y`;
- evaluation by any uniform antiderivative;
- `|between x y| ≤ |y-x| B` for `|f| ≤ B`;
- monotonicity of the accumulation function for nonnegative integrands;
- a Lipschitz, hence uniformly continuous, accumulation function for bounded
  integrands, without continuity of the integrand;
- derivative `f` with respect to the upper endpoint and `-f` with respect
  to the lower endpoint when the integrand is continuous.

`UniformlyContinuousIntervalIntegral` constructs its subinterval integrals
from standard uniform continuity. Endpoint derivatives are relative to the
closed interval. The original raw integral predicate for reversed endpoints
has not been changed; the oriented API above gives the intended signed values
inside a fixed enclosing interval.

## Consequences of FTC

[`FundamentalTheorem.Consequences`](Real/Integration/FundamentalTheorem/Consequences.agda)
uses the existing radiuswise **uniform** derivative hypothesis to prove:

- a nonnegative derivative gives a nondecreasing function;
- constant derivative bounds give bounds on increments;
- a positive constant lower bound on the derivative gives strict monotonicity;
- two antiderivatives of the same function differ by a constant;
- equal initial values make those antiderivatives equal;
- a zero derivative gives a constant function on the interval.

These results do not silently replace uniform differentiability with ordinary
pointwise differentiability.

## Integration by parts

[`FundamentalTheorem.IntegrationByParts`](Real/Integration/FundamentalTheorem/IntegrationByParts.agda)
assumes uniform derivatives `F' = f`, `G' = g` and positive rational absolute
bounds on `f` and `g` over the interval. It proves

```text
∫ (f G + F g) = F(b)G(b) - F(a)G(a).
```

If either product is integrable, subtraction constructs the other product's
integral. For supplied integral values, the usual formula follows:

```text
∫ f G = F(b)G(b) - F(a)G(a) - ∫ F g.
```

No separate continuity or boundedness premise on `F` or `G` is needed.
[`Uniform.Estimates`](Real/Calculus/Derivative/Uniform/Estimates.agda) derives
Lipschitz bounds, standard uniform continuity, and function bounds from bounded
uniform derivatives. The new uniform product rule in `Derivative.Product`
reuses the existing local product remainder identity and error estimates.

## Substitution

[`FundamentalTheorem.Substitution`](Real/Integration/FundamentalTheorem/Substitution.agda)
proves the endpoint formula for `f(G(x)) g(x)` when `G' = g` uniformly,
`G` maps `[a,b]` into `[c,d]`, and the target integrand and inner derivative
have supplied positive rational absolute bounds. It has two forms:

- a supplied uniform antiderivative `F` of `f` gives integral
  `F(G(b)) - F(G(a))`;
- `UniformlyContinuousSubstitution` constructs the antiderivative from
  standard uniform continuity of `f` on `[c,d]`.

The oriented endpoint formula requires neither monotonicity nor injectivity
of `G`. When `G(a) ≤ G(b)`, `integralEquality` identifies it with the ordinary
ordered integral of `f` between those endpoints. These theorems construct
the transformed integral; they do not assume its integrability.

The supporting uniform indexed chain rule reuses the existing chain remainder
estimate. Uniform derivative composition and interval adapters preserve
radiuswise truncation.

## Remaining work

- Integral existence from only radiuswise uniform continuity, or only
  radiuswise uniform convergence of integrable approximants, remains open.
- General pointwise FTC/mean-value conclusions require additional constructive
  arguments beyond the uniform derivative results here.
- A signed integral API without a fixed enclosing interval, stronger
  integrable-function closure laws, and less restrictive substitution or
  integration-by-parts hypotheses remain useful next steps.

## Verification

Every affected Agda module passed `agda-codex`, followed by
`Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda`: exit code 0,
with no holes, unsolved metas, constraints, or warnings. The source/import
audit found no added postulates, unsafe options, choice assumptions, or
imports from other real implementations. `git diff --check` for Analysis
passed, and all local links in this report resolve.
