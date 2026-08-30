# Sequential real analysis development

This directory develops real analysis from the sequence-backed completion in
`Cubical.Relation.Premetric.Completion.Alternative.Sequential`.  Its organizing
principle is that operations are extensions of rational functions.  Proofs
should use the recently developed Cauchy-continuous, completion-centered, and
uniformly-continuous lifting APIs instead of recursively rebuilding operations
from the constructors of a particular real-number HIT.

## Design decisions

- The real carrier is the sequential completion of the ordinary rational
  premetric.  It is denoted `ℝ` and rationals enter through `rat`.
- Generic theorems remain generic.  In particular, extensionality for maps out
  of a sequential completion belongs under `Cubical.Analysis.Completion`, not
  in a rational-only module.
- Arithmetic is defined by lifting rational arithmetic.  The comparison with
  `Completion.Base` may be used to transfer an already generic theorem (for
  example density/extensionality), but not as a hidden definition of an
  arithmetic operation.
- Primitive lifted definitions retain visible computation on `rat` and use
  limit uniqueness for `lim` equations.  Witness-eliminating derived
  operations may be opaque when their public computation and law theorems are
  already exposed; this prevents proof witnesses from becoming a reduction
  interface.
- Non-expanding lifting is preferred whenever the base operation admits it.
  Ordinary addition is separately non-expanding, but its uncurried product map
  is only Lipschitz with constant two.  This distinction is represented in the
  API instead of weakening every operation to continuity.
- Multiplication is the important exception: it is not globally uniformly
  continuous, so its definition uses completion-centred continuity on the
  rational product and then curries through the completion/product map.

## Inventory and lessons

### Existing completion machinery

- `Sequential.Base` presents the completion with rationally indexed closeness,
  an injection, and limits of ordinary sequences carrying merely a Cauchy
  witness.
- `Sequential.Properties` proves density, roundedness, constructs the
  premetric structure, and identifies the `lim` constructor as a sequential
  limit.
- `Sequential.Lift.CauchyContinuous` gives the central universal property:
  base maps satisfying the graph-Cauchy condition extend canonically, preserve
  Cauchy sequences, compute definitionally on the base injection, and satisfy
  uniqueness/extensionality.  It also packages restriction and extension as an
  isomorphism of sigma types.
- `Sequential.Lift.UniformlyContinuous` turns ordinary uniform continuity into
  the graph-Cauchy condition and proves that the lifted map remains uniformly
  continuous.
- `Sequential.Lift.CompletionCentered` handles genuinely non-uniform maps.  A
  local modulus centred at every completion point is enough to construct a
  Cauchy-continuous extension, and the extension is continuous.
- `Sequential.Product` proves that completion commutes with binary products.
  This is the correct route for rational functions of several variables.
- `Sequential.Comparison.Regular` is an isometric isomorphism with
  `Completion.Base`, computing to the same base point in both directions.

### What transfers well from `CauchyRealsP`

- Dense extensionality is the main reusable proof pattern.  Algebraic laws can
  be reduced to rational laws once both sides have suitable continuity.
- Rational computation lemmas should be part of every lifted operation's
  public API.
- Bundled algebraic structures should be constructed only after the primitive
  operations and their quantitative behavior are available.

### What should not be copied

- Constructor-by-constructor definitions of uniformly continuous operations:
  the generic lift already provides them.
- Bound-selection machinery for multiplication when completion-centred
  continuity can lift the whole rational product map directly.
- Specialized copies of generic lifting or extensionality lemmas.

### New generic completion layer

- `Completion.Extensionality` transfers dense continuous extensionality once,
  generically, across the isometric comparison with `Completion.Base`.  It
  includes unary and iterated binary/ternary forms.
- `Completion.NonExpanding` constructs the sequential lift using the recent
  uniformly-continuous/Cauchy-continuous machinery, then proves the exact
  non-expanding estimate by comparison with the regular generic lift.  It
  computes on the base injection and has lift-specific extensionality.
- `Completion.BinaryNonExpanding` does the same for separately non-expanding
  binary operations.  The underlying function comes from lifting the product
  map with the half-radius modulus; only the quantitative proof is sharpened by
  comparison with the regular completion.
- `Completion.Limit` proves generic `map-lim` rules.  Non-expanding maps build
  their image Cauchy witness directly.
- `Completion.BinaryLimit` proves that a separately non-expanding binary map is
  jointly Lipschitz with constant two and therefore commutes with synchronized
  sequential limits, including construction of the image witness.
- `Completion.Completeness` proves generically that the sequence-backed
  completion is complete, using the non-expanding isometric retract to the
  already complete regular presentation.
- `Completion.Lipschitz` extends a base map at one fixed positive rational
  Lipschitz constant and proves that the exact constant survives completion.
  It is the quantitative engine for bounded reciprocal.

### Real-number layer now available

- `Real.Base` exposes `ℝ`, `rat`, closeness, sequence witnesses and limits,
  density, sethood, and injectivity of `rat`.
- `Real.UniversalProperty` exposes continuous extensionality and the existing
  Cauchy-continuous restriction/extension isomorphism.
- Negation, addition, absolute value, maximum, and minimum use non-expanding
  lifts (or composites of them).  Their rational computation and exact
  one-variable non-expansion laws are public.
- Multiplication uses the completion-centred lift of rational multiplication on
  `ℚ × ℚ`; its product and curried forms compute on rationals and preserve
  synchronized limits.
- Dense extensionality proves the additive-group, multiplication, lattice, and
  absolute-value laws.  The resulting reals are packaged as an `AbGroup` and a
  `CommRing` without importing either Cauchy-real implementation.
- The fixed points of absolute value form an explicitly closed nonnegative cone
  under addition and multiplication.  This predicate is equivalent to the
  order-theoretic statement `0 ≤ x` once the lifted-max order is introduced.
- `Real.Order` defines `x ≤ y` by `max x y = y`, packages a `Poset`, proves the
  exact rational-order equivalence, and proves addition preserves and reflects
  order.  Multiplication is monotone by a nonnegative factor.  Pointwise order
  is closed under sequential limits.
- `Real.Order.Strict` defines `x < y` by the mere existence of a positive
  rational gap `δ` with `x + δ ≤ y`.  It proves the exact rational-order
  equivalence, mixed and strict transitivity, weakening, irreflexivity,
  asymmetry, translation/cancellation laws, negation reversal, and the
  positive-difference characterization.  Rational density gives locatedness
  and weak linearity, so the relation is packaged both as a `Quoset` and as a
  `StrictOrder`.
- Closeness is equivalent to the strict order bound
  `abs (x - y) < rat ε`.  The difficult direction is proved directly from
  rational density and the non-expanding absolute-value lift.  It yields the
  arbitrarily-small-slack principle and the exact compatibility
  `x ≤ y ≃ ¬ (y < x)`.
- The symmetric closure of strict order is a cotransitive apartness relation.
  Its rational restriction, translation invariance, cancellation, and
  negation law are public, and it is packaged as the library's `Apartness`
  structure.
- The lifted `min` and `max` package the non-strict order as a
  `Pseudolattice`.  Together with the strict-order compatibility and the
  existing ring laws this gives a complete `ℝOrderedCommRing`; `rat` is
  packaged as an ordered-commutative-ring homomorphism.
- Positive real multiplication is now constructive at the gap level: positive
  rational lower bounds multiply to a positive rational lower bound.  This
  yields strict monotonicity of multiplication by a positive real.  The
  subtype `ℝ>0`, its rational embedding, and its addition/multiplication
  operations expose the positive cone independently of a still-pending total
  strict-order bundle.
- `Real.Metric.Distance` defines `|x - y|`; it is separately non-expanding,
  symmetric, continuous, and computes on rational points.
- `Real.Sequence` gives canonical witness-producing limit rules for negation,
  absolute value, addition, distance, maximum, and minimum.  Multiplication's
  rule retains an explicit image witness because it is not globally
  non-expanding.
- Closed intervals and closed absolute-radius balls are now inherited
  premetric subspaces with non-expanding inclusions and clamp retractions.
  Both are complete by generic retract completeness; the unit interval is
  exposed as a specialization.  Open lower/upper half-lines, intervals, and
  absolute-radius balls are inherited subspaces with checked openness
  witnesses.
- `Real.Functions.Powers` illustrates compositional analysis: powers and square
  are continuous because multiplication takes continuous pairs to a continuous
  product; no new completion recursion is needed.
- Every real lies merely in a rational interval of any requested positive
  radius.  Widening it gives strict rational bounds, and the rational floor
  theory upgrades these to strict natural upper, lower, absolute, and
  two-sided bounds.
- Reciprocal is constructed in layers: a globally Lipschitz rational
  reciprocal clamped away from zero, compatibility between bounds, elimination
  of a positive-gap witness, and finally the signed apartness split.  The API
  includes rational computation, positivity, two-sided laws, involution,
  product/negation laws, division, cancellation, and multiplicative-apartness
  reflection.
- Natural-number embedding, a rational module action, rational affine maps,
  Horner polynomial evaluation, and finite sums are available.  The scalar
  lift retains its exact positive Lipschitz bound and agrees with
  multiplication by an embedded rational.  Polynomials have nonnegative
  majorants, absolute evaluation bounds, and derivative-ready closed-ball
  Lipschitz estimates.  Finite sums preserve native sequence witnesses and
  ordinary limits and expose monotonicity and an absolute-value bound.
- `Real.Sequence` now distinguishes native `SeqWitness` data from ordinary
  convergence, packages unique sequence limits, and proves constant, shift,
  unary, additive, multiplicative, and subtractive limit preservation.  Its
  choice-free tail layer covers eventual equality, eventual non-strict/strict
  order, and radiuswise asymptotic closeness, including transport of limits.
  A stronger merely selected asymptotic modulus preserves and reflects native
  witnesses, and constructive pointwise/eventual squeeze theorems are public.
- `Real.Series` provides partial sums, summability, additive and scalar closure,
  proof-independent sums, and the necessary theorem that terms of a summable
  series tend to zero.  Tail dropping and finite modification preserve and
  reflect summability with exact correction formulas.  Partial-sum distance
  bounds support dominated native Cauchy series, absolute-Cauchy convergence,
  and the standard absolute bound on the resulting sum.
- Finite sums additionally expose extension, splitting, addition, negation,
  subtraction, scalar and multiplicative distribution, exchange, telescoping,
  reversal, anti-diagonal sums, and triangular reindexing.  Series expose
  monotonicity and arbitrary summable-majorant bounds.
- Geometric series have a division-free finite identity and an explicit
  block/binary decay modulus for every rational `|q| < 1`, yielding native
  Cauchy witnesses, summability, and the reciprocal sum formula.  A real ratio
  dominated by such a rational contraction inherits the same conclusions and
  reciprocal value.  Uniform series distinguish a selected point-independent
  modulus from its propositionally truncated interface.  Uniform convergence
  of continuous partial sums gives a continuous canonical sum.  A single
  geometric majorant therefore proves bounded-coefficient power-series
  convergence and continuity uniformly across every closed positive rational
  radius strictly below one.  More generally, coefficients satisfying
  `|a n| ≤ B G^n` converge absolutely and uniformly on every closed rational
  radius `R` with `G R < 1`; the corresponding canonical value is continuous
  and has the geometric-majorant absolute bound.  These growth certificates
  are closed under addition, subtraction, negation, and explicitly bounded
  real scaling.  Evaluation at zero is unconditionally summable with value
  equal to the constant coefficient.  Eventual coefficient equality transports
  Cauchy and summability witnesses, and explicit cutoffs give exact finite
  corrections to power-series values.
- Cauchy products expose bilinearity, commutativity, unit laws, triangular and
  rectangular partial-sum identities, an explicit remainder and its absolute
  majorant.  The quantitative Mertens theorem proves convergence and sum
  multiplication from native absolute/Cauchy witnesses plus explicit uniform
  partial-sum bounds, without asserting a choice-producing converse from mere
  summability.  Native Cauchy witnesses now construct merely existing rational
  partial-sum bounds; eliminating those only into propositions gives
  bound-free remainder, `HasSum`, summability, and product-value theorems.
  Cauchy multiplication of coefficient sequences evaluates exactly to the
  Cauchy product of the corresponding power-series terms, with both
  explicit-bound and native-Cauchy convergence wrappers.
- The first differential-calculus kernel uses a division-free first-order
  remainder.  It supports general premetric parameter spaces, continuous
  reparameterization, and continuous difference-factor proofs; constants and
  identity are differentiable, and derivative values and functions are unique
  without a choice principle.  Addition, negation, subtraction, arbitrary
  real scaling, rational scaling, multiplication, composition, natural powers,
  Horner polynomials, and finite sums preserve derivatives.  Differentiable
  maps are continuous, and open-predicate subspaces support restriction and
  pointwise ambient derivative adapters.  An indexed chain theorem also
  composes two derivatives living on the same parameter space.  Reciprocal
  derivatives are checked on explicit positive and negative rationally bounded
  domains, with transfer to proof-independent inverse values; arbitrary
  differentiable numerators and denominators have a quotient rule whenever a
  uniform positive rational bound separates the denominator from zero on
  either side.
- Formal power-series differentiation is available at the coefficient and
  term levels: it respects addition and scaling, computes on rational
  coefficients, and identifies every successor power term with its derivative
  term.  Generic coefficient majorants are preserved by formal
  differentiation.  The finite divided-difference factor now has its power
  factorization, diagonal formal-derivative identity, continuity,
  closed-radius bound, and derivative-majorant domination.  The remaining
  family is uniformly Cauchy on a closed radius whenever the corresponding
  derivative-majorant series is native Cauchy, including by restriction from a
  larger radius.  The remaining analytic step is deliberately separate:
  identify the canonical factor sum with the series difference and its
  diagonal before deriving a derivative for the infinite sum.

## Work log

- [x] Surveyed the sequential completion, all three lifting interfaces, product
  comparison, and the foundational/additive parts of `CauchyRealsP`.
- [x] Selected a hierarchy separating generic completion principles from the
  rational real-number development.
- [x] Added generic sequential-completion extensionality, non-expanding lifts,
  synchronized limit rules, and completeness.
- [x] Added the sequential-real foundation and universal-property facade.
- [x] Defined negation and addition by lifting rational maps; exposed rational
  computation and continuity laws.
- [x] Defined multiplication as a lifted map from the rational product and curried
  it through the completion/product isomorphism.
- [x] Established algebraic laws by dense extensionality and packaged additive
  group and commutative-ring structures.
- [x] Added lifted absolute value, lattice operations, distance, powers, a
  partial order, monotonicity laws, completeness, and sequence-facing results.
- [x] Develop the positive-gap strict order, its rational characterization,
  additive laws, and multiplicative positivity/strict monotonicity.
- [x] Prove locatedness/cotransitivity, the metric/strict-order
  characterization, and package apartness and the standard ordered-ring
  interfaces.
- [x] Add inverses away from zero, natural embeddings, polynomial evaluation,
  and finite sums using quantitative lifts and finite recursion.
- [x] Establish the sequence/series baseline: ordinary limit combinators,
  partial sums, linear operations, and the summable-term test.
- [x] Add rational scalar/affine maps, polynomial majorants and local estimates,
  choice-free eventual sequence relations, finite-sum bounds, series tails,
  finite modifications, and native-witness absolute convergence comparison.
- [x] Add finite-sum algebra, selected asymptotic witnesses and squeeze,
  complete closed domains, rational half-contraction geometric series, series
  comparison, and the first bounded-coefficient power-series convergence
  layer.
- [x] Add signed half-contraction geometric series, point-independent uniform
  series moduli, uniform closed-radius power-series convergence, open
  intervals, and the definition/basic/uniqueness derivative kernel.
- [x] Add open absolute-radius domains, uniform-limit continuity and continuous
  closed-radius power-series values, derivative linear algebra and continuity,
  open-subspace derivative adapters, and arbitrary strict-rational geometric
  convergence.
- [x] Add real geometric convergence under rational contraction bounds,
  strict-interior rational-radius power-series convergence and continuity,
  product and chain rules, and convolution-oriented finite-sum reindexing.
- [x] Add natural-power, Horner-polynomial, and finite-sum derivative rules,
  controlled positive/negative reciprocal and quotient rules, finite
  Cauchy-product algebra, explicit remainder bounds, and a quantitative
  Mertens convergence theorem.
- [x] Add indexed derivative composition, arbitrary-denominator quotients on
  uniformly positive/negative domains, constructive native bounds and
  bound-free Mertens theorems, exponential coefficient-growth convergence and
  closure laws, exact zero/finite-modification formulas, power-series products,
  generic majorants, and the uniform formal-derivative/divided-difference
  foundation.
- [ ] Generalize geometric and power-series convergence, extend domain-local
  continuity and calculus algebra,
  integration, and elementary functions in the phases recorded in
  `SCOPE_ROADMAP.md`.

## Computational behavior

- Unary and separately non-expanding binary lifts compute on `ι` through the
  sequential lift's base computation equation.
- `rat p + rat q`, `rat p · rat q`, `max (rat p) (rat q)`, and the analogous
  operations all have checked public computation lemmas.
- Unary/binary `lim` rules are stated by uniqueness of sequential limits.  For
  non-expanding maps the target witness is constructed canonically from the
  source witnesses; multiplication exposes why a more general lift needs an
  explicit image witness.
- The comparison with `Completion.Base` is used for generic theorems and exact
  quantitative proofs, never as the hidden definition of a real operation.

## Performance observations

- A single module instantiating four fully generic non-expanding completion
  lifts exhausted the checker.  Lift extensionality therefore lives beside one
  lift instance; future identity/composition laws should use a lighter abstract
  interface rather than multiply instantiating the implementation.
- Bundling the nonnegative subtype as a `CommSemiring` forced the complete real
  `CommRing` proof through every subtype law and also exhausted the checker.
  The cone and its closed operations are retained; the redundant bundle is not.
- Unrestricted public opens in aggregate facades caused an accidental scope
  explosion.  Curating their exported names reduced `Algebra.Lattice` from
  roughly 36 seconds to 4 seconds and `Algebra` from more than 15 minutes to
  under 5 seconds; the top-level `Real` and `Analysis` facades then checked in
  roughly 8.5 and 7.3 seconds respectively.
- A dependent no-eta record whose field mentioned completed-real addition and
  order made the positivity checker expand the entire lifting implementation
  (over 9 GB without finishing).  The mathematically identical dependent-pair
  representation of a positive gap avoids that checker pathology.  Splitting
  strict order into base, rational, additive, and multiplicative modules keeps
  each focused check around 4--6 seconds.
- Leaving an endpoint as an unconstrained `refl` inside a transported strict
  inequality made Agda unfold the implementations of lifted `max` and
  addition and left several enormous constraints.  Replacing it with the
  one-sided `subst` whose endpoint was explicit removed all metas and restored
  a sub-five-second check.  Proof transports around lifted operations should
  identify their changing endpoint explicitly.
- The first open-interval proof inherited `width gap`, whose hidden real
  endpoints were harmless mathematically but disastrous for elaboration:
  checking reached roughly 13.4 GB without finishing.  Projecting the sigma
  witness as `fst gap`, pinning both endpoints of order transports, and using
  small generic transport helpers reduced the complete module to about 2.8
  seconds.  In dependent quantitative proofs, apparently redundant explicit
  endpoints are an important performance boundary.
- No ring/order solver is used anywhere under `Cubical.Analysis`; rational and
  real laws are proved from named algebraic lemmas and dense extensionality.
- Moving the max-based absolute triangle proof into `Real.Order.AbsoluteValue`
  removed duplicate proof terms from both polynomial-bound modules and gives
  finite sums and series one shared ordered-ring estimate.
- A direct attempt to synthesize multiplication's diagonal `SeqWitness`
  through the product-completion comparison ran for more than two minutes and
  was removed.  This confirms that witness plumbing across a large comparison
  should first be factored into a lightweight generic combinator.  The public
  ordinary-limit theorem for multiplication remains fast because it uses
  continuity instead.
- An inline proof-dependent reciprocal inside the geometric `HasSum` statement
  caused more than two minutes of normalization.  Factoring the positive
  denominator proof and the proof-dependent sum into named definitions reduced
  the complete rational geometric check to roughly 4.2 seconds.
- A redundant proof that the geometric majorant is nonnegative, phrased through
  the fully general four-variable multiplication monotonicity theorem, also
  pushed a focused check past thirty seconds.  It was removed because all
  consumers need only the sharper termwise domination theorem, which checks in
  about four seconds.
- Composing an arbitrary negative denominator through the proof-indexed signed
  inverse again made completion-level normalization run past forty seconds.
  Pulling back the already checked uniformly upper-bounded negative reciprocal
  gives the same inverse law and reduced the complete quotient module to about
  four seconds.  Bounded reciprocal representations should remain visible
  through derivative composition and be erased only at the convenience API.
- A decidable `<` split for the finite-prefix/tail cases in the native Cauchy
  bound theorem ran past a minute.  Replacing it by structural natural-number
  `≤` case induction, with the prefix ending at `suc cutoff`, made the complete
  module check in about five seconds.
- The exact coefficient-product theorem expressed through proof-indexed
  `powerSeriesValue` ran past fifty-eight seconds.  Its underlying `HasSum`
  theorem and summability wrapper each check in about five seconds, so the slow
  convenience theorem was removed and the proof-independent sum equation is
  the exported boundary.

## Open technical questions

- Which completion-centred maps admit automatically generated image witnesses
  for `lim` equations?  Multiplication currently exposes the witness explicitly.
- A categorical identity/composition API for non-expanding lifts is desirable,
  but it needs an abstraction that does not instantiate the heavy construction
  several times in one generic module.
- `SeqWitness` is a truncation of a globally chosen modulus, whereas
  `isLimitSequence` has radiuswise truncated tails.  A convergent sequence does
  not automatically regain a native witness without an additional choice
  step.  The series API therefore treats `Summable` as primary and exposes
  only the sound native-Cauchy-to-summable direction.
- Multiplication's completion-centred construction knows enough to preserve
  suitable Cauchy graphs, but its cheapest reusable binary witness interface
  is not yet exposed.  This should be solved generically before polynomial or
  series clients request multiplication witnesses.
- Termwise power-series differentiation should be built from a uniformly
  summed divided-difference factor, not from division by `y - x`.  This matches
  the division-free derivative kernel and makes the diagonal/formal-derivative
  identity a finite algebraic theorem.  The remaining design question is how
  much of that family belongs in generic uniform-series infrastructure versus
  the power-series layer.
