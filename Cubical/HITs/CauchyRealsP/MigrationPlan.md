# Cauchy reals over generic premetric completion

This directory is a parallel migration of `Cubical.HITs.CauchyReals`.  Its
working name is `CauchyRealsP`, where `P` records that the construction is
based on `Cubical.Relation.Premetric`.

The purpose is not merely to reproduce the old module names.  The purpose is
to recover, and where useful generalise, the mathematical scope of the old
formalisation while making the real-number completion an instance of
`Cubical.Relation.Premetric.Completion`.

The existing `CauchyReals` directory remains the checked reference
implementation during the migration.

For a stable conceptual comparison of migrated scope, legacy mathematical
content, and the new generic-completion architecture, see
`MigrationScope.md`.

## Working principles

1. **Specialise before duplicating.**  The real numbers are defined by
   specialising the generic completion to `ℚPremetricSpace`.  Constructors,
   elimination, closeness, completeness, and extension theorems should come
   from the generic development unless a real-specific theorem genuinely
   needs a separate proof.
2. **Port mathematical content, not accidental architecture.**  Old proofs
   are important sources of ideas and lemmas, but their dependency structure
   and public API are not requirements.
3. **Build in small checked layers.**  A layer is added only after its direct
   dependencies check.  Umbrella modules are added after, rather than before,
   their contents are stable.
4. **Keep decisions reversible.**  Experimental interfaces stay small.  A
   decision that makes later algebra, order, or analysis awkward may be
   replaced and is then recorded as superseded below.
5. **Prefer reusable general theorems.**  If a proof belongs to arbitrary
   premetric completions, it should be implemented under
   `Cubical.Relation.Premetric` and only re-exported here.
6. **No axiomatic shortcuts.**  The migration adds no postulates, unsafe
   pragmas, weakened options, or unchecked compatibility shims.

## Mathematical target

The intended mature development should cover analogues of the main subjects
currently present under `CauchyReals`:

- the Cauchy completion of the rationals and its universal properties;
- rational approximation, density, located closeness, and completeness;
- addition, negation, multiplication, natural/integer powers, and the
  constructive ordered-field interface based on apartness from zero;
- strict and non-strict order, apartness, Archimedean properties, absolute
  value, minima and maxima;
- limits, Cauchy sequences, continuity, uniform continuity, and Lipschitz
  maps;
- series, finite sums, infinite sums, and convergence estimates;
- elementary transcendental functions and their estimates;
- metric and topological consequences;
- complex numbers and the substantial theory already built over the old
  reals.

Exact theorem statements may differ when the generic premetric formulation is
more useful.  “Analogous” means that downstream non-trivial mathematics can be
recovered, not that every old identifier has an alias.

## Layered architecture

The current intended dependency direction is:

```text
Relation.Premetric.Instances.Rationals
                 │
                 ▼
        Foundation.Rationals
                 │
                 ▼
          Foundation.Base
                 │
       ┌─────────┼──────────┐
       ▼         ▼          ▼
   Closeness  Approximation  UniversalProperty
       │
       ▼
 algebra and order
       │
       ▼
 analysis, topology, transcendental functions
       │
       ▼
 complex numbers and applications
```

`Foundation.Base` is deliberately thin.  It gives conventional real-number
names to the generic completion specialised to the rational premetric space.
The proofs that this closeness relation is a premetric and that the completion
is complete belong to `Foundation.Closeness`.

Operations will be constructed using completion lifts where their quantitative
continuity permits it:

- unary globally Lipschitz operations use `liftLipschitz` or
  `liftNonExpanding`;
- separately Lipschitz binary operations use
  `liftLipschitzBinaryWith`;
- multiplication is first lifted after symmetrically clamping both rational
  inputs to a positive bound.  These globally Lipschitz bounded operations
  agree exactly when the bound is enlarged.  Total multiplication is then
  obtained by coherently eliminating the merely existing Archimedean bounds
  into the set of reals.

## Milestones

### M0 — checked foundation

Status: **complete (initial version), 2026-07-29**.

- [x] rational premetric source;
- [x] specialised completion and eliminators;
- [x] real premetric space, completeness, density/approximation;
- [x] extension and uniqueness principles into complete premetric spaces;
- [x] a small umbrella module validating the intended interface.

### M1 — additive and order core

Status: **complete (initial version), 2026-07-29**.

- [x] addition and negation via generic completion lifts;
- [x] additive commutative-group structure;
- [x] strict and non-strict order foundations;
- [x] rational embedding preserves and reflects both orders;
- [x] non-strict order compatibility with addition and negation;
- [x] strict order compatibility with addition and negation;
- [x] absolute value with non-expansion and triangle estimates;
- [x] the metric/order bridge;
- [x] rational bounds, density, apartness, and Archimedean lemmas;
- [x] symmetric real clamps and their metric/order properties.

### M2 — multiplication and ordered field

Status: **in progress**.

- [x] globally Lipschitz bounded multiplication;
- [x] exact compatibility across increasing bounds;
- [x] total multiplication by coherent Archimedean gluing;
- [x] rational computation and commutativity;
- [x] zero/unit, associativity, and distributivity;
- [x] commutative-ring structure and the rational ring homomorphism;
- [x] multiplication preserves nonnegativity and positivity;
- [x] located strict order and ordered-commutative-ring packaging;
- [x] natural powers, rational computation, and basic order/absolute-value
  estimates;
- [x] a compatible lower-bounded reciprocal and a well-defined reciprocal on
  positive reals;
- [x] local continuity of total multiplication and continuous extensionality
  from rational density;
- [x] the lower-bounded and positive reciprocal laws;
- [x] signed inversion, uniqueness, multiplication, and division cancellation
  for inputs apart from zero;
- [x] positivity and order reversal for positive reciprocals, inverse
  apartness/involution, and positive-denominator quotient inequalities;
- [ ] an appropriate apartness-field package (the library's current `Field`
  asks for inversion from mere inequality, which is constructively stronger);
- [x] Horner polynomial evaluation, rational computation, continuity,
  nonnegative majorants, absolute-value estimates, and bounded Lipschitz
  estimates.

### M3 — analysis

Status: **in progress**.

- [x] generic and real-specialised Cauchy-sequence/limit vocabulary;
- [x] constructive completeness of real Cauchy sequences;
- [x] preservation of limits by continuous algebraic operations and
  polynomials;
- [x] eventual equality, shifts, products of sequence limits, and
  closedness of order under eventual inequalities;
- [x] quantitative preservation of Cauchy sequences, including bounded
  multiplication;
- [x] finite sums of convergent and Cauchy sequences;
- [x] an initial real-series interface with linearity, comparison,
  nonnegativity, vanishing terms, and absolute-sum bounds;
- [x] finite-tail, absolute-convergence, and comparison criteria carrying
  explicit Cauchy moduli;
- [x] a first geometric-series layer separating the algebraic sum identity,
  power decay, and rational-majorant comparison;
- [x] finite convolution, triangular/rectangular reindexing, a selected
  constructive Mertens modulus, and the Cauchy-product sum theorem under
  explicit rational partial-sum bounds;
- [x] convolution commutativity, symmetric Mertens interfaces, reusable
  partial-sum bound algebra, and bounded-coefficient power series with
  coefficient-convolution products;
- [x] finite-prefix/tail bound producers, quantitative finite-modification
  closure, and a bridge from rational partial-sum estimates;
- [x] power-series convergence under an arbitrary nonnegative summable
  coefficient majorant, including eventual boundedness as a consumer;
- [x] geometric and linearly growing coefficient examples, with the latter
  evaluated through coefficient convolution;
- [x] absolute Mertens closure with multiplicative total-variation bounds,
  and an arbitrary finite iterated-geometric convolution family;
- [x] simplex/binomial formulas and polynomial bounds for the
  iterated-geometric coefficients, together with a formal coefficient
  derivative and its complete action on that family;
- [x] topology-free uniform Cauchy series, continuous uniform limits,
  closed-radius power-series convergence, and continuous evaluation for the
  iterated-geometric family and its formal derivative;
- [x] a division-free premetric derivative interface, continuous
  divided-difference criterion, analytic termwise differentiation of power
  series on closed radii (including inner-radius conclusions from derivative
  convergence at a larger radius), and the explicit derivative of the
  iterated-geometric reciprocal-power family;
- [x] derivatives of constants, the identity, natural powers, and finite
  Horner polynomials, together with a zero-padded finite power-series bridge
  and recovery of ordinary pointwise derivatives at strict interior points;
- [x] derivative closure under addition, negation, subtraction, bounded real
  scaling, rational scaling, and products; derivative-to-continuity and the
  chain rule over arbitrary continuous real coordinates; polynomial
  composition; and exact agreement between Horner and coefficientwise formal
  polynomial derivatives;
- [x] uniqueness and proposition-valued packaging of ordinary derivatives;
  reciprocal differentiation on fixed positive-lower-bound, positive,
  negative, and signed-apartness subspaces;
- [x] a chain rule through an arbitrary intermediate premetric space,
  quotient rules for arbitrary differentiated denominators carrying
  pointwise apartness, polynomial rational functions, and the globally
  defined example `x / (1 + x²)`;
- [x] inherited natural domains `{x | 0 # denominator x}` for partial
  rational functions, the conventional quotient-rule normal form, apartness
  closure under products and powers, and shifted/two-pole consumers;
- [x] coordinate-preserving maps between denominator domains, exact transport
  along pointwise denominator equalities, common nonvanishing domains, and
  derivative closure for sums and products of independently denominated
  rational functions;
- [x] nested natural domains and chain-rule differentiation for composition
  of partial rational functions, with a double-reciprocal consumer;
- [x] product-denominator normal forms for common-domain rational sums and
  products, including derivative theorems and exact value equalities;
- [x] bidirectional finite-prefix/tail summability, shifted and scaled
  geometric sums, exact eventually-geometric series values, and power series
  with a finite polynomial prefix followed by a geometric coefficient tail;
- [x] identification of finite-polynomial-plus-geometric-tail power-series
  values with a single differentiable rational function on the natural domain
  of `1 - r·x`;
- [x] ordinary strict-interior derivatives for closed-radius functions that
  agree with an explicit ambient extension, specialised to uniformly summed
  power series and outer-radius derivative majorants;
- [x] an initial topology/interval layer: generic open predicates and balls,
  real open and closed intervals, a non-expanding interval clamp retraction,
  canonical continuous interval extension, open-neighbourhood recovery of
  ambient derivatives, and algebraic pasting at a point;
- [x] closed half-lines and half-open interval domains, completeness of
  closed half-lines and nonempty closed intervals, continuous pasting on the
  whole real line, and continuous closed-lower and strict-lower pasting;
- [ ] total boundedness, connectedness, intermediate- and mean-value results,
  and further compact-interval consequences.

### M4 — elementary and complex analysis

- exponential, logarithmic, trigonometric, and square-root developments;
- complex numbers over `CauchyRealsP`;
- complex algebra, norms, limits, series, exponential/trigonometric theory,
  and selected non-trivial applications.

## Decision ledger

| Date | Decision | Status | Reason / reconsider when |
| --- | --- | --- | --- |
| 2026-07-29 | Keep `CauchyReals` intact and build a parallel `CauchyRealsP`. | accepted | It supplies a working oracle and makes rollback cheap. Reconsider only near final adoption. |
| 2026-07-29 | Define the new real type as `Completion ℚPremetricSpace`, not as a copied HIT. | accepted | The HIT shape and eliminators match the old foundation, while generic closeness and lifting theorems become available. |
| 2026-07-29 | Retain familiar names `ℝ`, `rat`, and `lim` at the real-specific boundary. | trial | They keep formulas readable without hiding the generic origin. Reconsider if name collisions make general proofs awkward. |
| 2026-07-29 | Use the generic completion closeness as the canonical real closeness. | accepted | Avoids maintaining a second relation and immediately connects to `PremetricSpace`. |
| 2026-07-29 | State the first universal property in the category of premetric spaces with complete codomain. | trial | It supports construction of quantitative maps directly. The old set-quotient-style presentation theorem can be recovered later if independently useful. |
| 2026-07-29 | Do not promise source-level compatibility with old eliminator names. | accepted | Mathematical scope matters more than a broad alias layer. Small aliases may still be added when they improve proofs. |
| 2026-07-29 | Construct addition with `liftLipschitzBinaryWith` and negation with `liftNonExpandingExtension`. | accepted | Both constructions compute on rationals and supply exactly the quantitative estimates needed downstream. |
| 2026-07-29 | Prove algebraic laws through quantitative density/extensionality rather than copying old binary-recursion infrastructure. | accepted | Unary, binary, and ternary density arguments proved the full additive group laws with a small reusable interface. Reconsider only if higher-arity proofs become unwieldy. |
| 2026-07-29 | Keep rational operations in a qualified `ℚ` namespace while real operations use conventional notation. | trial | This avoids notation collisions in mixed rational/real proofs. Reconsider alongside the eventual public module style. |
| 2026-07-29 | Lift rational `max` with the generic separately Lipschitz binary lift and define `min x y = - max (-x) (-y)`. | accepted | There is no ordered-completion layer under `Relation.Premetric` to reuse yet. This construction retains quantitative estimates and avoids duplicating a second binary lift. Reconsider if a genuinely generic ordered-premetric completion theory is developed. |
| 2026-07-29 | Define `x ≤ℝ y` by `maxℝ x y ≡ y`. | trial | It immediately supplies a partial order, rational reflection, and translation compatibility. Keep the definition opaque so elaboration does not repeatedly unfold the generic binary completion lift. Reconsider if later locatedness or ordered-ring packaging strongly favours another presentation. |
| 2026-07-29 | Define `x <ℝ y` by propositional truncation of an explicit rational sandwich witness. | superseded | It supported the initial order proofs, but translating a sandwich by an arbitrary real first required a substantial metric-to-one-sided-bound theorem. The positive-gap presentation below gives the same intended real-order content with structural additive compatibility. |
| 2026-07-29 | Prove translation distribution of `max` by quantitative density. | accepted | This yields non-strict additive monotonicity and cancellation from the same generic universal property used by the additive laws. The translating variable is 2-Lipschitz on the `max` side, so the final density step intentionally uses Lipschitz rather than non-expanding extensionality. |
| 2026-07-29 | Define `x <ℝ y` by a truncated positive rational gap: some `δ : ℚ₊` satisfies `x + rat δ ≤ℝ y`. | accepted | Rational preservation/reflection, transitivity, translation, cancellation, mixed monotonicity, and negation reversal become direct ordered-group arguments. This deliberately replaces the rational-sandwich trial. |
| 2026-07-29 | Hide the computed inequality in `PositiveGap` behind an opaque `GapBound` interface. | accepted | Putting `x + rat δ ≤ℝ y` directly in a dependent record made Agda unfold the generic addition and maximum lifts and stall. Explicit introduction/elimination functions retain the theorem while keeping the record elaboration around 1.6 seconds. |
| 2026-07-29 | Construct `absℝ` as the generic non-expanding lift of rational absolute value, then prove `absℝ x = maxℝ x (-x)`. | accepted | Defining it directly by maximum only exposes a 2-Lipschitz estimate from separate arguments. The lifted construction supplies the mathematically sharp 1-Lipschitz theorem, while density recovers the lattice characterization needed by order proofs. |
| 2026-07-29 | Add reflection of base-point closeness as a generic completion theorem, not a real-specific rational lemma. | accepted | The theorem follows from the generic equivalence between completion closeness and its base relation, and is the missing reusable hinge in the metric/order bridge. |
| 2026-07-29 | Use positive-gap strict absolute difference as the order-facing characterization of closeness. | accepted | Approximation proves both directions without changing the canonical premetric relation. This supports one-sided bounds and keeps metric and order reasoning interchangeable. |
| 2026-07-29 | Construct bounded multiplication from symmetric rational clamps and `liftLipschitzBinaryWith`. | accepted | On `[-B,B]`, multiplication is separately `B`-Lipschitz. Clamping makes that estimate global while retaining exact rational computation. |
| 2026-07-29 | Require exact compatibility, not merely asymptotic closeness, when bounded multiplication is enlarged. | accepted | The larger clamp fixes every value already in the smaller interval. Exact equality makes gluing independent of quantitative convergence bookkeeping. |
| 2026-07-29 | Define total multiplication by coherent elimination of truncated natural bounds into the set `ℝ`. | accepted | `PT.rec→Set` can choose a local bounded operation precisely because bound compatibility makes the choice 2-constant. This is substantially smaller than copying the old nested-open-set intersection construction. |
| 2026-07-29 | Factor common-bound arithmetic into `Multiplication.CommonBounds`, naming dependent witnesses before projecting them. | accepted | Associativity needs `max(B,B²)` while distributivity needs `B+B`. Named witnesses and explicit endpoints avoid unstable inference through dependent projections. |
| 2026-07-29 | Prove ring laws on clamped bounded expressions and transfer them with `multiplicationWithin`. | accepted | Rational density remains quantitative and local, while the total operation inherits exact laws without unfolding coherent truncation elimination. |
| 2026-07-29 | Prove nonnegative multiplication first for maximum-clamped bounded inputs, then transfer it to total multiplication. | accepted | This isolates the only density argument. Strict positivity can then be derived constructively from explicit positive gaps and rational positive products. |
| 2026-07-29 | Derive locatedness by halving a positive gap and comparing dense rational approximants. | accepted | The order dichotomy, `x ≤ y ≃ ¬(y < x)`, and weak linearity do not need multiplication and therefore retain the correct dependency direction. |
| 2026-07-29 | Package the real operations as `ℝCommRing` and `ℝOrderedCommRing`, with the rational embedding as the corresponding homomorphism. | accepted | This makes the library's generic ring, order, and exponentiation theory available while retaining the premetric-specific constructions underneath. |
| 2026-07-29 | Derive absolute-value multiplicativity from nonnegative square injectivity in the ordered ring. | accepted | It avoids a second analytic density proof. Explicit associativity/commutativity paths are used because the generic ring solver stalled while normalising opaque multiplication terms. |
| 2026-07-29 | Construct reciprocal at a positive lower bound by lifting `q ↦ 1 / max(η,q)` with Lipschitz constant `1/η²`. | accepted | The source calculation is global and quantitative, so generic completion lifting replaces most of the old inverse-specific limit recursion. |
| 2026-07-29 | Require exact compatibility of lower-bounded reciprocals on inputs above both bounds, then eliminate the truncated positive-gap witness. | accepted | Compatibility follows by composing with a common maximum and using Lipschitz density. It yields a proof-independent positive reciprocal without claiming the inverse law prematurely. |
| 2026-07-30 | Add continuous extensionality for maps out of the generic completion. | accepted | Multiplication is only locally controlled, so rational density at the continuous level is the right uniqueness theorem; forcing a global Lipschitz bound would be false. |
| 2026-07-30 | Prove joint continuity of total multiplication from pointwise bounds and two fixed-factor estimates. | accepted | A natural absolute bound at the base point controls one factor in a neighbourhood. Splitting the target radius into two halves then handles the two product differences without unfolding coherent multiplication. |
| 2026-07-30 | Prove the reciprocal law by continuous density for `max(η,x) · reciprocal(max(η,x))`. | accepted | The clamped product is continuous and is exactly one on rationals. This isolates local continuity once and avoids a second inverse-specific completion induction. |
| 2026-07-30 | Define signed inversion by the two apartness cases rather than through a separate sign function. | accepted | Positive inputs use the positive reciprocal; negative inputs negate the positive reciprocal of `-x`. The disjoint, proposition-valued apartness sum gives proof independence directly. |
| 2026-07-30 | Prove bounded reciprocal antitonicity through the identity `reciprocal(max(x,y)) = min(reciprocal(x),reciprocal(y))`. | accepted | The identity is globally quantitative in both variables and has a direct rational proof, so Lipschitz density transports it without requiring an order induction principle for the completion. |
| 2026-07-30 | Obtain strict positivity of a positive reciprocal from a natural upper bound on the input. | accepted | Antitonicity compares the reciprocal to the positive rational inverse of that bound. This supplies an explicit constructive gap and avoids the invalid inference from nonzero to apartness. |
| 2026-07-30 | Do not package the constructive reals as `Cubical.Algebra.Field` without an additional principle. | accepted | That structure requires an inverse from `¬ (x ≡ 0)`, while the constructive development supplies one from `0 ＃ x`. Treating these as interchangeable would silently add a Markov-style stability principle. A reusable apartness-field interface is the intended package. |
| 2026-07-30 | Represent the first polynomial layer by increasing-degree coefficient lists and Horner evaluation. | accepted | This matches the polynomial interface already used by the complex calculus, gives structural continuity and majorant proofs, and avoids prematurely depending on the substantially heavier generic polynomial HIT and commutative-algebra stack. Reconsider when multivariate or quotient-polynomial results become a real consumer. |
| 2026-07-30 | Generalise pointwise addition, multiplication, and maximum continuity combinators over an arbitrary source premetric. | accepted | Polynomial evaluation first exposed the combinators, while paired sequence limits immediately supplied a second genuinely different source. Keeping the source generic avoids rebuilding the same epsilon argument for products and parameter spaces. |
| 2026-07-30 | Reuse generic premetric sequence notions and add only real-specific completeness and algebraic consequences. | accepted | `PremetricTheory` already contains the correct Cauchy and limit predicates. Product limits, eventual equality, shifts, and quantitative-map preservation were added generically because none depends on real arithmetic. |
| 2026-07-30 | Define `Summable` as the proposition-valued existence of a limit for partial sums, while retaining `IsCauchySeries` as the modulus-carrying sufficient condition. | accepted | A Cauchy proof contains an actual modulus and is not proposition-valued; a convergent sum should be proof-independent. Completeness converts the quantitative witness to summability without conflating these roles. |
| 2026-07-30 | Require an explicit common bound when proving that products of Cauchy sequences are Cauchy. | accepted | Total multiplication is locally, not globally, Lipschitz. Natural bounds on arbitrary reals are merely truncated, so extracting a modulus from them would require an unjustified choice principle. Limit preservation still needs no explicit bound because continuity returns propositionally truncated neighbourhood data. |
| 2026-07-30 | Defer the apartness-field record until a second consumer needs structure-level abstraction. | accepted | Polynomials, sequences, limits, finite sums, and the initial series layer all use the existing ring/order operations directly. Creating a public structure now would still be interface speculation rather than reuse-driven generalisation. |
| 2026-07-30 | Formulate absolute convergence first as a Cauchy modulus for the absolute partial sums. | accepted | This is exactly the constructive information needed to transfer a modulus through the finite-tail inequality. Mere summability remains proposition-valued and cannot supply a modulus without choice. |
| 2026-07-30 | Split geometric series into an algebraic identity, a power-decay interface, and a rational-majorant comparison theorem. | accepted | The reciprocal sum formula needs only `xⁿ → 0`; rational contraction is one producer of that decay, not part of the identity. This keeps the useful core independent of the still-missing pure rational geometric-modulus proof. |
| 2026-07-30 | Use a recursively computed real-valued Horner Lipschitz majorant on a nonnegative radius. | accepted | It gives the sharp structural estimate `|P(x)-P(y)| ≤ L(R)|x-y|` without pretending that an arbitrary real bound is a selected positive-rational Lipschitz constant. A rational-bound corollary can later package a premetric `IsLipschitzWith` witness. |
| 2026-07-30 | Avoid the generic commutative-ring solver for geometric and Horner difference normalisation. | accepted | It stalled on the opaque migrated multiplication. Short explicit associativity, distributivity, cancellation, and translation paths check quickly and expose the relevant algebraic decomposition. |
| 2026-07-30 | Define convolution with recursive natural partial sums and prove triangular reindexing by a first-row recurrence. | accepted | This stays aligned with the series API and avoids repeated transports through finite-index equivalences. The checked identity is still mathematically the usual sum over `i + j < n`. |
| 2026-07-30 | Separate the exact rectangular remainder from its analytic modulus. | accepted | The identity `AₙBₙ = Cₙ + Rₙ` is pure finite algebra. A selected modulus for `|Rₙ| < ε` is precisely the constructive information needed to transfer Cauchy status and limits, and it can be tested independently of any particular producer. |
| 2026-07-30 | State constructive Mertens with an absolute Cauchy modulus for the first series, a Cauchy modulus for the second, and explicit rational bounds on the relevant partial sums. | accepted | Merely existing real bounds cannot be eliminated into a modulus without choice. These hypotheses are sufficient for the standard prefix/tail split and are automatically produced when an absolutely convergent total variation has a supplied rational upper bound. |
| 2026-07-30 | Name proof-dependent canonical convergence and summability witnesses before using them in geometric consumers. | accepted | Repeating their expanded completion proofs inside dependent `seriesSum` types made elaboration stall. Small named witnesses preserve the same theorem and restore roughly two-second checks. |
| 2026-07-30 | Prove convolution commutativity through reversal of recursive partial sums. | accepted | A cutoff-sensitive pointwise equality theorem and the involution `k = n - (n - k)` give a small checked proof without importing finite-index permutations. The symmetric Mertens interface then transports the existing estimate instead of duplicating its prefix/tail argument. |
| 2026-07-30 | Keep uniform partial-sum bound algebra in a separate `Series.Bounds` module. | accepted | Weakening, addition, and scaling apply to both ordinary and total-variation bounds and are useful beyond Mertens. Separating them prevents power-series modules from accumulating one-off rational bound calculations. |
| 2026-07-30 | Formulate the first power-series radius theorem with a uniform rational coefficient bound and a supplied rational contraction bound on the evaluation point. | accepted | The terms are dominated by `Cqⁿ`, giving an explicit total-variation bound `C/(1-q)`. This is constructive, carries a selected modulus, and is already strong enough for coefficient convolution and the product-of-values theorem. More general coefficient growth belongs in a later majorant interface. |
| 2026-07-30 | Give algebraic helper binders explicit real and natural-number types in proof-heavy series modules. | accepted | Leaving four rearrangement variables to overloaded inference made an otherwise elementary ring path exceed a minute. Explicit `(p q r s : ℝ)` binders restored a roughly two-second module check. |
| 2026-07-30 | Pass already named absolute-Cauchy witnesses into proof-dependent sum-bound theorems. | accepted | Asking Agda to unify a local witness with an independently expanded canonical witness caused another minute-scale stall. Generalising the internal bound theorem to accept the witness avoids proof-term comparison without changing the proposition. |
| 2026-07-31 | Separate finite-prefix bounds from uniform tail bounds, and combine them only at the final global-bound boundary. | accepted | A dropped total-variation tail retains the original bound, while an ordinary tail is a difference of two bounded partial sums and therefore receives `B + B`. Keeping these statements distinct prevents an unjustified sharp ordinary bound. |
| 2026-07-31 | State general power-series convergence through an explicit nonnegative coefficient-majorant series. | accepted | The analytic comparison only needs `|aₙ| ≤ mₙ`, `0 ≤ mₙ`, and Cauchy convergence of `Σ mₙrⁿ`. Constant, polynomial-growth, and other coefficient estimates can now be separate producers instead of separate epsilon proofs. |
| 2026-07-31 | Handle eventually bounded coefficients by replacing a finite prefix with zero and transferring convergence through eventual equality. | accepted | Finitely many exceptional coefficients should not be forced into a selected global rational bound. The zero-prefix sequence is globally bounded and the existing finite-modification theorem restores the original series without choice. |
| 2026-07-31 | Obtain the first nonconstant polynomial-growth power series as the self-convolution of the unit coefficient sequence. | accepted | The convolution coefficient is proved to be the embedded natural `n + 1`; the power-series product theorem then gives both summability and the reciprocal-square value without duplicating geometric tail estimates. Iterate this structural route before considering a degree-indexed closed formula. |
| 2026-07-31 | Bundle an absolute-Cauchy witness with its selected rational total-variation bound. | accepted | Passing the two proof-dependent arguments separately made concrete product iteration repeatedly compare expanded convergence witnesses and stall. `AbsoluteCauchySeriesWithBound` and `PowerSeriesAbsoluteWithBound` make product closure atomic; opaque closure functions restore normal checking time and preserve the sharp product bound `A · B`. |
| 2026-07-31 | Represent higher geometric orders by iterated convolution before proving a binomial closed form. | accepted | The structural family already supplies absolute convergence, summability, multiplicative bounds, and reciprocal powers for every finite order. Identifying its coefficients with binomial/falling-factorial formulas is useful but orthogonal and should not block the analytic recursion. |
| 2026-07-31 | Use iterated finite sums (`simplexCoefficient`) as the primary computed coefficient representation and make the binomial formula a corollary. | accepted | The finite-sum recurrence follows the actual convolution definition directly.  The separate hockey-stick proof gives `C(n+d,d)` without forcing Nat combinatorial normalization into convergence or product proofs. |
| 2026-07-31 | Move the recursive natural embedding and its semiring/order laws into `Algebra.Natural`. | accepted | Geometric series happened to be its first consumer, but coefficient combinatorics and formal differentiation also need it.  Keeping it in the algebra layer avoids an artificial dependency on a particular analytic example. |
| 2026-07-31 | Separate formal coefficient differentiation from analytic differentiability. | accepted | The weighted shift `Daₙ = (n+1)aₙ₊₁`, its majorant transport, and its algebraic identities require no topology.  Calling the evaluated function a derivative will wait for local uniform convergence and a checked limit-interchange theorem. |
| 2026-07-31 | Define uniform series convergence by one selected Cauchy modulus shared over an arbitrary index type. | accepted | This is the exact quantitative datum needed for majorant arguments and continuity of the sum.  It does not prematurely require a topology on the parameter type; a premetric is introduced only for the continuity theorem. |
| 2026-07-31 | Treat a closed absolute-value radius as a premetric subspace of the reals. | accepted | The same type carries the coefficient-majorant hypothesis `|x| ≤ r` and the inherited closeness needed for continuity.  This keeps closed-radius convergence constructive and avoids introducing open discs before limit interchange needs them. |
| 2026-07-31 | Prove continuity of uniform series values from continuous terms in the generic series layer. | accepted | The proof uses a shared modulus, an explicit uniform tail estimate, and one continuous finite partial sum.  Power-series continuity is then an instance, rather than a separate epsilon argument. |
| 2026-07-31 | Do not restate reciprocal-power value formulas through the new closed-radius canonical summability witness. | superseded | Two direct attempts made Agda normalize proof-dependent `seriesSum` witnesses for more than 30 seconds.  The later `seriesSumPresPath` and finite-difference sum bridge avoid comparing those witnesses, so the useful restatement now checks quickly. |
| 2026-07-31 | Define differentiability by a division-free first-order remainder estimate along a real coordinate on an arbitrary premetric parameter space. | accepted | The statement works directly on inherited subspaces, needs no apartness or quotient by an increment, and retains the quantitative content `|f(y)-f(x)-f'(x)(y-x)| ≤ ε|y-x|` of the legacy calculus. |
| 2026-07-31 | Prove power-series differentiation through a continuous divided difference rather than a literal difference quotient or a separate limit-interchange theorem. | accepted | The finite identity factors every difference by `y-x`; the remaining factor series is dominated by the formal-derivative majorant and converges uniformly on the pair of closed-radius subspaces.  Continuity at the diagonal then gives the derivative remainder estimate directly. |
| 2026-07-31 | Transport sums across term-sequence paths and prove value factorization by uniqueness of limits. | accepted | This keeps summability witnesses opaque.  It supplies the cheap proof-independent bridge that was missing from the first uniform-value attempt and prevents elaboration from comparing expanded completion proofs. |
| 2026-07-31 | Represent finite polynomial differentiation by a Horner derivative evaluator and a matching Horner divided difference. | accepted | Their factorization and diagonal laws are structural, and continuity follows for any continuous real coordinate.  This proves the full polynomial theorem without accumulating product-rule bounds. |
| 2026-07-31 | Embed finite coefficient lists into the power-series interface by padding them with zero. | accepted | Partial sums then stabilize exactly at the list length, giving an immediate uniform Cauchy modulus and an exact agreement theorem with Horner evaluation, without invoking an infinite majorant. |
| 2026-07-31 | Keep closed-radius differentiation relative, and recover an ordinary pointwise derivative only from a strict interior gap. | accepted | Taking the minimum of the analytic modulus and the gap to the boundary produces the required real neighbourhood.  This preserves the correct boundary statement without requiring an open-set calculus yet. |
| 2026-07-31 | Prove the first derivative closure rule directly from the remainder predicate. | accepted | Addition splits the target error into two half-radius estimates and takes the minimum of their moduli.  This validates that the public derivative predicate composes independently of the stronger divided-difference criterion. |
| 2026-07-31 | State real scaling first with an explicit positive rational bound on the scalar. | accepted | The derivative modulus is evaluated at `ε/B`, and rational scaling supplies a canonical bound.  The theorem also applies to arbitrary real scalars whenever the caller already has quantitative bound data. |
| 2026-07-31 | Prove the product rule from two derivative remainders and continuity of either one factor. | accepted | Continuity controls both the nearby value multiplying one remainder and the cross term.  Local Archimedean bounds are eliminated only into the proposition-valued modulus result; no global Lipschitz hypothesis or selected global bound is introduced. |
| 2026-07-31 | Represent the formal derivative of a finite polynomial by a consecutive natural weighting of its coefficient tail. | accepted | The weighted list agrees pointwise with the infinite formal derivative after zero padding, while a structural Horner calculation proves equality of evaluations.  The finite termwise and Horner derivative theorems therefore commute exactly. |
| 2026-07-31 | Derive continuity from an along-coordinate derivative only when the coordinate map is continuous. | accepted | The derivative gives a local estimate relative to coordinate displacement, not directly to source closeness.  A selected rational bound on the derivative value yields coefficient `1+B`; continuity of the coordinate then converts this estimate into ordinary premetric continuity. |
| 2026-07-31 | Prove the chain rule by decomposing the composite remainder rather than introducing difference quotients. | accepted | The outer remainder is controlled by a local linear bound for the inner function, while the inner remainder is scaled by a local bound on the outer derivative.  This works for arbitrary premetric sources with continuous real coordinates and reuses the same local estimate as derivative-to-continuity. |
| 2026-07-31 | Prove uniqueness only for ordinary real derivatives, not for arbitrary along-coordinate derivatives. | accepted | A common explicit rational increment cancels the positive displacement between two remainder estimates.  An arbitrary coordinate can be locally constant, so the analogous relative statement would be false without a local injectivity or lower-expansion hypothesis. |
| 2026-07-31 | Differentiate reciprocal first on the subspace `rat η ≤ x` for a fixed `η : ℚ₊`. | accepted | On this domain the globally Lipschitz bounded reciprocal satisfies the exact inverse law and its two-point factor `-(inv x · inv y)` is continuous.  This exposes all constructive quantitative data, avoids choosing a positive gap from mere existence, and gives a stable base for later positive/apartness-domain gluing. |
| 2026-07-31 | Obtain differentiation on the full positive subspace by local gluing from the fixed-bound theorem. | accepted | At a point, halve a representative of its truncated positive gap.  Closeness within that half-gap keeps every nearby point above the same fixed bound, after which proof irrelevance identifies the bounded implementation with `positiveReciprocal`.  The derivative modulus is proposition-valued, so eliminating the original gap is coherent and requires no global choice. |
| 2026-07-31 | Derive negative reciprocal differentiation by pulling the positive theorem through coordinate negation. | accepted | Negation is non-expanding and converts a negative point into a positive one.  Separate source pullback, coordinate reversal, output negation, and named equality transports keep the proof modular and prevent opaque `subst2` terms from leaving blocked constraints. |
| 2026-07-31 | Glue signed reciprocal differentiation pointwise with the nondependent apartness eliminator. | accepted | A half-gap neighbourhood preserves the selected sign and reduces each branch to the checked positive or negative theorem.  The result type is proposition-valued and does not depend on the particular sign witness; using nondependent `⊎.rec` avoids an elaboration stall observed with a dependent `with` split. |
| 2026-07-31 | Generalise the chain rule to an arbitrary intermediate premetric target. | accepted | Differentiating reciprocal after a denominator naturally factors through the apart-real subspace rather than through the whole real line.  The remainder calculation still only uses the real coordinate of that target, so no target-specific analytic machinery is needed. |
| 2026-07-31 | Represent an everywhere-apart denominator as a map into the apart-real premetric subspace. | accepted | This packages exactly the constructive domain evidence required by reciprocal.  The general chain rule and product rule then yield quotient differentiation without selecting a global sign or lower bound; ordinary real functions and polynomial quotients are specialisations. |
| 2026-07-31 | Give every denominator its inherited natural domain `Σ x , 0 # denominator x`. | accepted | Denominators with roots cannot supply global apartness, but their nonvanishing locus is an ordinary premetric subspace.  Pullback restricts ordinary numerator and denominator derivatives to this source, after which the existing quotient theorem applies without adding topology or a partial-function primitive. |
| 2026-07-31 | Expose the conventional quotient derivative `(f'g - fg') / g²` and prove it equal to the internal product/inverse derivative. | accepted | The internal form follows composition directly, while the conventional form is substantially better for consumers.  Equality uses the signed inverse law and explicit ring paths; the first generic ring-solver attempt was stopped after exceeding the normal check window. |
| 2026-07-31 | Add apartness closure under natural powers at the ordered-algebra layer. | accepted | It follows structurally from apartness of one and closure under multiplication, is independent of differentiation, and lets denominator-domain certificates for products and powers compose without reproving sign cases. |
| 2026-07-31 | Treat root exclusions as constructors into a denominator's natural domain. | accepted | For `x/((x-a)(x-b))`, witnesses `x # a` and `x # b` construct apartness of both differences and hence their product.  The natural domain remains canonical while factored presentations can expose useful, readable sufficient conditions. |
| 2026-07-31 | Put reflection of convergence across a finite sequence shift in generic premetric theory. | accepted | Recovering a whole series from a convergent dropped tail is not real- or series-specific.  The proof raises the threshold by the shift and reconstructs each sufficiently late index by subtraction; every premetric sequence can now use it. |
| 2026-07-31 | Represent an exact eventual geometric tail by equality of the dropped sequence with a scaled geometric sequence. | accepted | Sequence equality composes directly with `HasSum`, exposes the finite cutoff, coefficient, and ratio without an additional wrapper record, and makes the evaluated power-series ratio visibly change from `r` to `r·x`.  The convergence hypothesis remains the constructive rational contraction bound on that actual evaluated ratio. |
| 2026-07-31 | Derive strict-inner-radius differentiation through monotonicity of nonnegative power-series majorants. | accepted | A derivative majorant Cauchy at an outer radius dominates its value at every nonnegative inner radius.  The existing closed-boundary theorem remains the sharp same-radius interface; the new theorem trades the larger convergence radius for an inner closed-radius conclusion and still leaves original-series convergence explicit because derivative convergence cannot control the constant coefficient. |
| 2026-07-31 | Keep the derived inner-radius formal-derivative uniform witness named and opaque. | accepted | Repeating its expanded proof in the dependent derivative-function target caused a check to exceed one minute.  A named opaque producer records the same constructive modulus, makes the result type stable, and restored a roughly two-second complete check. |
| 2026-07-31 | Represent a polynomial-prefix/geometric-tail sum as one quotient over `1-r·x`. | accepted | The numerator `P(x)(1-r·x)+c·xˡᵉⁿᵍᵗʰ P` makes the existing quotient calculus apply directly.  On a rational-contraction point the denominator is positive, and the quotient expands definitionally to the previously proved series value.  No parallel derivative proof for infinite sums is needed. |
| 2026-07-31 | Model operations on differently denominated rational functions over the intersection of their natural domains. | accepted | Addition and multiplication require both denominators apart at the same coordinate.  This evidence is explicit and sufficient for non-expanding projections to each individual domain.  Identifying the intersection with the nonvanishing domain of the product denominator would additionally require reflection of apartness from a product, so it is not assumed prematurely. |
| 2026-07-31 | Treat denominator-domain transports as coordinate-preserving maps whose proof components are propositionally irrelevant. | accepted | A pointwise implication of apartness predicates induces a non-expanding subspace map; pointwise equality gives transports in both directions.  Concrete factorizations may use different equality proofs, so inverse laws are established by `Σ≡Prop`, not by expecting those path terms to be definitionally identical. |
| 2026-08-01 | Model rational composition by a nested natural domain carrying both denominator-apartness obligations. | accepted | The outer denominator is evaluated at the proof-dependent inner quotient, so its witness genuinely depends on the inner-domain point.  A subspace of the inner natural domain expresses this dependency exactly and lets the chain rule factor through the outer natural domain without a premature category of partial maps. |
| 2026-08-01 | Keep function parameters explicit in maps out of nested dependent rational domains. | accepted | An initial implicit presentation typechecked only with twenty metas and blocked constraints inside expanded completion arithmetic.  Explicit numerator and denominator parameters make coordinate, inner-point, and outer-point maps elaborate in the normal two-second range. |
| 2026-08-01 | Relate a common two-denominator domain to the product-denominator domain only in the constructively available direction. | accepted | Apartness of each factor constructs apartness of their product, so the forward coordinate-preserving map and normalized quotient values are immediate.  The reverse direction would require reflecting apartness from a product and remains intentionally absent. |
| 2026-08-01 | Turn a relative closed-radius derivative into an ordinary derivative only through agreement with an explicit ambient function. | accepted | Strict interior supplies the neighbourhood, but it does not manufacture values outside the closed radius.  Requiring a genuine extension prevents the canonical power-series sum from being treated as globally defined where summability is unknown; no ambient extension of the derivative is needed. |
| 2026-08-01 | Put open predicates, their finite intersections, continuous preimages, and open balls in generic premetric theory. | accepted | None of these constructions uses real arithmetic or completion induction.  This is intentionally a neighbourhood-level API rather than a premature topological-space record; arbitrary unions and topology equivalences can be added when a consumer needs them. |
| 2026-08-01 | Keep the general interval clamp in order algebra and package its subspace retraction in analysis. | accepted | `min (max a x) b` and its non-expansion/fixpoint laws are algebraic.  The closed-interval type, inherited premetric, and retraction/extension interpretation belong to the analytic domain layer. |
| 2026-08-01 | Recover ambient differentiation from any open neighbourhood contained in the relative derivative domain. | accepted | The differentiated domain itself need not be open: a closed interval has its strict interior as an open neighbourhood.  Pulling the derivative back to that neighbourhood separates local calculus from the particular representation of interval endpoints. |
| 2026-08-01 | Use clamp precomposition as the canonical extension of a map on a nonempty closed interval. | accepted | The extension agrees exactly on the interval and preserves non-expansion, uniform continuity, and continuity.  It gives relative interval derivatives a genuine ambient function without pretending that an unrelated analytic definition exists outside its proven domain. |
| 2026-08-01 | Port the min/max pasting formula before its continuity wrappers. | accepted | The algebraic left/right laws require only proposition-valued order and the additive group.  Keeping continuity separate makes the next step an ordinary composition theorem over half-line subspaces rather than entangling the basic equality proof with legacy predicate machinery. |
| 2026-08-01 | Prove completeness through a generic non-expanding retraction theorem rather than a real-specific order-limit argument. | accepted; supersedes the initial closedness plan | A Cauchy approximation in the retract embeds into the complete ambient space, acquires an ambient limit, and is sent back by the retraction.  This proves completeness of both closed half-lines and every nonempty closed interval, and the theorem applies to arbitrary premetric spaces. |
| 2026-08-01 | Move absolute-radius domains from power-series uniform convergence into metric geometry. | accepted | Closed and strict absolute-radius predicates are interval-like metric domains, not power-series concepts.  The strict predicate is a continuous preimage under non-expanding absolute value, so the generic open-neighbourhood derivative theorem replaces the bespoke boundary-distance calculation. |
| 2026-08-01 | Represent strict-lower pasting over an explicit left-open/right-closed interval. | accepted | The excluded lower endpoint need not, and generally cannot, receive a continuous value.  Min maps the open half-line into the half-open bounded piece, max maps it into the closed right piece, and the algebraic paste is continuous directly on the open source without inventing an endpoint extension. |

Possible future entries include choices for the apartness-field interface,
transport between the old and new real types, and the eventual replacement or
retirement strategy.

## Progress log

### 2026-07-29 — initial survey

- Compared the old `Foundation.Base`, `Foundation.Closeness`,
  `Foundation.Rationals`, and `Foundation.UniversalProperty` with the generic
  completion.
- Confirmed that the old and generic constructions have the same essential
  generators: rational/base inclusion, Cauchy limits, extensional equality,
  and four forms of closeness constructors.
- Identified reusable generic results for reflexivity, symmetry,
  triangularity, roundedness, sethood, completeness, approximation, injectivity
  of the inclusion, unary lifting, binary lifting, and uniqueness of
  quantitative extensions.
- Chose the initial module split under `Foundation`.

### 2026-07-29 — foundation and additive vertical slice

- Added `Foundation.Rationals`, specialising Lorenzo's rational premetric
  instance without depending on the old real development.
- Added `Foundation.Base` as a thin renaming/specialisation of the generic
  completion.  The real HIT and its eliminators are therefore not duplicated.
- Specialised the generic closeness development to obtain the real premetric
  space, sethood, reflexivity, symmetry, triangle and roundedness laws,
  injectivity of rational inclusion, limit correctness, and completeness.
- Specialised generic approximation to obtain arbitrarily close rational
  approximants.
- Added complete-codomain non-expanding extension, its contractible universal
  property, and non-expanding/Lipschitz density principles.
- Constructed real addition with the generic separately Lipschitz binary lift.
  It computes on rational pairs and is non-expanding separately in both
  variables; the combined triangle estimate is also exposed.
- Constructed negation with the generic non-expanding lift and proved its
  rational computation rule.
- Added reusable binary and ternary extensionality principles for separately
  non-expanding functions.
- Proved addition commutative and associative with left/right identities.
  Proved additive inverses using Lipschitz density, defined subtraction, and
  packaged the result as `ℝAbGroup`.
- Added `Foundation`, `Algebra`, and root umbrella modules.

All Agda modules in the new directory check with no holes, unsolved metas, or
unsolved constraints at this point.

Validation on 2026-07-29:

- all 13 new Agda modules were checked directly with `agda-codex` and returned
  exit code 0;
- the unchanged generic completion facade, closeness properties, and lift
  properties returned exit code 0;
- the unchanged old `CauchyReals.Foundation` and `CauchyReals.Algebra`
  umbrella modules returned exit code 0.

#### Approaches corrected during implementation

- A rational reflection proof with implicit equality endpoints left
  non-interaction metas.  Giving the source and target rational expressions
  explicitly made the proof robust.  Future uses of reflection under `cong`
  should follow that pattern.
- Negation does not preserve the raw difference by equality:
  `(-x)-(-y)` is `y-x`, not `x-y`.  Its distance proof must first use symmetry
  of absolute difference and only then ring normalisation.  This distinction
  should be retained when order/apartness proofs are ported.
- The additive inverse map `x ↦ x + (-x)` is not non-expanding under the
  available separate estimates; it is 2-Lipschitz.  Adding a Lipschitz density
  principle was the correct abstraction instead of weakening a
  non-expanding claim.

### 2026-07-29 — additive laws, lattice, and order foundation

- Added the standard negation and subtraction laws: involution, distribution
  over addition, rational computation, non-expanding estimates for
  subtraction, cancellation, and the usual zero/self calculations.
- Surveyed `Cubical.Relation.Premetric` for an ordered-completion abstraction.
  None currently constructs an order on a completion from ordered dense data,
  so this migration does not pretend such an abstraction already exists.
- Lifted rational maximum to `maxℝ`, retaining separate non-expanding and
  combined closeness estimates.  Proved commutativity, associativity, and
  idempotence by quantitative density.
- Derived `minℝ` from maximum and negation, including its rational computation
  rule, quantitative estimates, commutativity, associativity, and idempotence.
- Defined non-strict order by the maximum equation and proved proposition
  valuedness, reflexivity, transitivity, antisymmetry, rational preservation
  and reflection, maximum bounds, and a `Poset` package.
- Defined strict order by a truncated `StrictWitness` record containing
  rational lower and upper separators.  Proved rational preservation and
  reflection, strict and mixed transitivity, weakening to non-strict order,
  asymmetry, irreflexivity, and a `Quoset` package.
- Proved that maximum commutes with real translation.  Derived non-strict
  monotonicity in either or both summands, additive cancellation, order
  reversal by negation, and the equivalence between an inequality and its
  right translate.

Validation on 2026-07-29:

- all 18 Agda modules/entry points in the new development were checked
  directly with `agda-codex` and returned exit code 0;
- the unchanged generic completion facade, generic closeness properties, and
  generic lift properties returned exit code 0;
- the unchanged old `CauchyReals.Foundation` and `CauchyReals.Algebra`
  umbrella modules returned exit code 0.

#### Approaches corrected during the order implementation

- Encoding the dependent rational sandwich as nested dependent pairs caused
  Agda to lose endpoint information while destructuring witnesses.  Replacing
  it with the explicit `StrictWitness` record made those dependencies stable
  and makes later witness transformations readable.
- Leaving `_≤ℝ_` transparent allowed typechecking a strict-witness record to
  unfold the entire generic binary lift for `maxℝ`; one check stalled for over
  two minutes.  Making the relation and its foundational proofs opaque reduced
  the complete order-base check to about 1.5 seconds.
- After opacity fixed the stall, `≤ratEquiv` still left four non-interaction
  metas because `propBiimpl→Equiv` tried to infer its proposition endpoints
  through the opaque relation.  Supplying its `A` and `B` parameters
  explicitly removed all metas.  Equivalences over opaque relations should
  follow this pattern.
- An initial concern that rational order reflection itself caused the
  elaboration problem was disproved by isolating and checking that proof.  The
  problem was interface inference around the opaque relation, not the
  reflection argument.

### 2026-07-29 — strict additive order and absolute value

- Compared generic rational approximation with the old one-sided rational
  bounds.  Generic approximation supplies symmetric metric closeness, but a
  conversion to one-sided order bounds has not yet been proved.  Building that
  conversion solely to translate strict-order witnesses would invert the
  natural dependency direction.
- Replaced the trial rational-sandwich strict order with a positive-rational-
  gap relation: `x <ℝ y` means merely that some `δ : ℚ₊` satisfies
  `x + rat (fst δ) ≤ℝ y`.
- Split strict order from `Order.Base`.  `Order.Base` now contains only
  `≤ℝ` and its `Poset`; `Order.Addition` contains non-strict ordered-group
  compatibility; and `Order.Strict` builds on both without an import cycle.
- Reproved rational preservation/reflection, strict and mixed transitivity,
  weakening, asymmetry, irreflexivity, and the `Quoset` package.
- Added strict translation on either side, strict and mixed additive
  monotonicity, translation cancellation/equivalence, and order reversal by
  negation.
- Constructed absolute value as a generic non-expanding lift of rational
  absolute value and proved its rational computation rule.
- Proved that this quantitative construction equals `maxℝ x (-x)`.  Derived
  the two canonical bounds, nonnegativity, invariance under negation, zero and
  idempotence laws, simplification on nonnegative/nonpositive inputs, and
  reflection of zero.
- Proved the triangle inequality, the subtraction triangle estimate, and
  symmetry of absolute difference.

Validation on 2026-07-29:

- all 20 Agda modules/entry points in the new development were checked
  directly with `agda-codex` and returned exit code 0;
- the unchanged generic completion facade, approximation, closeness, and lift
  properties returned exit code 0;
- the unchanged old `CauchyReals.Foundation` and `CauchyReals.Algebra`
  umbrella modules returned exit code 0.

#### Approaches corrected during this slice

- The rational-sandwich strict order was not wrong, but it put arbitrary-real
  translation behind an order/metric approximation theorem that the
  development does not yet have.  Replacing this trial interface was smaller
  and produced a more algebraic strict order.
- A `PositiveGap` field written directly as
  `x + rat (fst δ) ≤ℝ y` reproduced the earlier elaboration stall even though
  `_≤ℝ_` itself is opaque.  Bisection localized the problem to the record
  declaration.  The opaque `GapBound` wrapper is therefore a performance
  boundary, not a mathematical abstraction claim.
- Constructing absolute value as `maxℝ x (-x)` initially appears simplest,
  but the available separate non-expansion estimates only prove that diagonal
  expression 2-Lipschitz.  Lifting rational absolute value first preserves the
  sharp non-expanding estimate and still recovers the maximum formula.

### 2026-07-29 — metric/order completion and multiplication construction

- Added generic reflection from closeness of two embedded base points back to
  the source premetric relation, and specialised it to rational absolute
  distance.
- Proved that real closeness at radius `ε` is equivalent to a strict
  `absℝ (x - y) <ℝ rat ε` bound.  The forward direction derives both
  one-sided order bounds; the reverse direction reconstructs closeness from a
  positive residual gap.
- Added strict rational lower and upper bounds for every real, rational
  density between strictly ordered reals, additive apartness, and positivity
  of absolute difference for apart points.
- Added natural upper, lower, absolute, and two-sided bounds.  These are
  deliberately independent of multiplication and are therefore available to
  construct it.
- Added symmetric real clamps, including rational computation,
  non-expansion, endpoint bounds, fixpoint/idempotence laws, and an absolute
  bound.
- Constructed `boundedMulℝ B` by lifting rational multiplication after
  symmetric clamping.  It computes on rational inputs, is separately
  `B`-Lipschitz, is commutative, and absorbs real clamps.
- Proved exact compatibility: if `B ≤ C`, then the `C`-bounded operation on
  `B`-clamped inputs is the `B`-bounded operation.  Consequently the two
  operations agree on any pair whose absolute values are bounded by `B`.
- Defined total multiplication by using coherent set elimination on the
  truncated existence of a joint natural absolute bound.  Proved that it can
  be evaluated at any sufficiently large explicit bound, computes as rational
  multiplication on embedded rationals, and is commutative.
- Extended binary quantitative extensionality to separately Lipschitz
  functions whose witnesses and constants need not be identical.

Validation on 2026-07-29:

- all 30 Agda modules/entry points in `CauchyRealsP` were checked directly
  with `agda-codex` and returned exit code 0;
- the generic completion closeness, approximation, and lift modules returned
  exit code 0;
- the old `CauchyReals.Foundation` and `CauchyReals.Algebra` umbrellas
  returned exit code 0.

#### Approaches corrected during this slice

- Using the rational inequality automation tactic for the quarter-gap
  arithmetic in the metric/order bridge caused elaboration to run for over a
  minute.  Named, explicitly typed rational inequalities check quickly.
- A single composite apartness-to-positive-absolute-value proof also caused a
  long elaboration.  Splitting the positive and negative cases into named
  helpers retained the proof and removed the stall.
- Dependent endpoint information in joint-bound proofs was not reliably
  inferred through projections.  Explicit `ℝ` annotations, explicit
  completion endpoints, and named intermediate bounds removed all
  non-interaction metas.
- Proving the computation of `PT.rec→Set` by an ordinary proposition
  eliminator made Agda unfold the complete coherence construction and stall.
  The set eliminator already exposes its coherence path; using that named path
  checks in about two seconds.
- Similarly, combining a non-trivial bound-comparison callback directly with
  truncation elimination was expensive.  Proving the callback first for an
  explicit witness and applying the small `PT.rec` step separately is stable.

### 2026-07-29 — ring laws, ordered structure, powers, and reciprocal base

- Proved bounded and total zero/unit laws and a uniform `B²` absolute bound
  for bounded products.
- Factored the common-bound infrastructure shared by associativity and
  distributivity.  Associativity expands a joint bound to `max(B,B²)`;
  distributivity uses `B+B` for the input sum while its two output products
  remain bounded by `B`.
- Proved total associativity and both distributive laws, packaged `ℝCommRing`,
  and packaged the rational inclusion as a commutative-ring homomorphism.
- Proved bounded nonnegativity by separately Lipschitz density, transferred it
  to total multiplication, and derived non-strict monotonicity in one or both
  factors.
- Derived strict product positivity from explicit positive-gap widths and
  rational positivity, then obtained strict monotonicity.
- Proved the located-order dichotomy from two half-gap rational
  approximations.  Derived the equivalence `x ≤ℝ y ≃ ¬ (y <ℝ x)`, weak
  linearity of strict order, and the positive-sum alternative.
- Packaged the complete structure as `ℝOrderedCommRing` and the rational
  inclusion as an ordered-ring homomorphism.
- Connected the lifted absolute value to generic ordered-ring theory.  Proved
  `absℝ (x · y) = absℝ x · absℝ y` using injectivity of squaring on
  nonnegative reals.
- Added natural powers from generic commutative-ring exponentiation, including
  rational computation, positivity/nonnegativity, monotonicity, absolute
  values of powers, and an absolute-bound comparison.
- Lifted the rational function `q ↦ 1 / max(η,q)` to a globally
  `1/η²`-Lipschitz real function.  Proved exact agreement of any two such
  functions on inputs above both positive lower bounds.
- Used that agreement to coherently eliminate a truncated positive-gap
  witness.  The resulting positive reciprocal is independent of the chosen
  gap and computes as rational reciprocal on positive rationals.

#### Approaches corrected during this slice

- Dependent projections from a triple-bound witness left non-interaction
  metas in associativity.  Naming the pair witness and third-coordinate
  witness, then supplying endpoints explicitly, made the proof stable.
- Because `_≤ℝ_` is opaque, an external maximum equality is not
  definitionally accepted as an inequality.  The small `maxPath→≤ℝ` boundary
  keeps this conversion explicit.
- Difference characterisations of non-strict and strict order belong in the
  additive order modules.  Moving them there removed a prospective cycle from
  multiplication monotonicity.
- A ring-solver proof of the two four-factor rearrangements needed for
  absolute-value multiplicativity ran for more than 30 seconds.  Six explicit
  associativity/commutativity steps check in under two seconds and make the
  opacity boundary visible.
- The reciprocal compatibility proof initially reversed the arguments to the
  rational maximum-distance lemma.  An explicit transport by symmetry of
  absolute difference fixed the orientation without automation.
- The next positive-inverse law is intentionally deferred to a dedicated
  local-continuity proof.  The composite
  `max(η,x) · boundedReciprocal η x` is mathematically constant, but the
  available separate multiplication estimates do not by themselves make it
  globally Lipschitz; pretending otherwise would hide the main remaining
  proof obligation.

Validation on 2026-07-29:

- all 44 Agda modules/entry points in `CauchyRealsP` were checked directly
  with `agda-codex` and returned exit code 0;
- the changed generic completion closeness module, the generic completion
  facade, approximation module, and lift module returned exit code 0;
- the unchanged legacy `CauchyReals.Foundation` and `CauchyReals.Algebra`
  umbrellas returned exit code 0;
- every check reported zero holes, unsolved metas, unsolved constraints, and
  warnings.

### 2026-07-30 — local multiplication continuity and constructive division

- Added continuous extensionality for functions out of `ℝ`: two continuous
  maps agreeing on embedded rationals agree everywhere.  This specialises the
  generic completion uniqueness theorem and complements the existing
  non-expanding and Lipschitz variants.
- Proved sharp fixed-factor multiplication estimates.  Multiplication by a
  factor whose absolute value is at most `B` is `B`-Lipschitz, on either side.
  The proof passes through strict absolute difference and uses
  `absℝ (x · y) = absℝ x · absℝ y`.
- Proved joint continuity of pointwise products of continuous real-valued
  functions.  At each point, a truncated natural absolute bound controls the
  values; continuity also controls one factor in a neighbourhood.  Two
  fixed-factor Lipschitz estimates then give half of the requested error each.
- Defined the positive clamp `x ↦ max(η,x)` and showed that the clamped
  reciprocal product is continuous.  Its rational values reduce to
  `q · q⁻¹ = 1`, so continuous extensionality proves it constantly one.
- Derived `x · boundedReciprocalℝ η x = 1` whenever `rat η ≤ℝ x`.
  Eliminating the positive-gap witness then proves both left and right inverse
  laws for the existing proof-independent `positiveReciprocal`.
- Added closure of apartness from zero under multiplication, with all four
  sign combinations proved from strict product positivity.
- Added signed inversion on `0 ＃ x`, proof independence, left and right
  inverse laws, uniqueness, preservation of multiplication, and basic
  left/right division cancellation.
- Proved that bounded reciprocal exchanges real maximum with real minimum.
  This rational-density identity yields non-strict antitonicity on all reals,
  independently of the later inverse law.
- Combined antitonicity with a natural upper bound to bound a positive
  reciprocal below by an explicitly positive rational reciprocal.  Derived
  strict positivity, non-strict and strict order reversal for positive
  reciprocals, and hence apartness of every signed inverse.
- Added sign preservation for signed inverses, inverse involution, negation,
  and rational computation against `Cubical.Data.Rationals.Inverse`.
- Added positive-denominator division, multiplication cancellation, and the
  four strict/non-strict order equivalences for clearing a positive
  denominator on either side of an inequality.

#### Approaches corrected during this slice

- The first joint-continuity draft attempted to return an unparenthesised
  dependent pair from propositional-truncation `do` notation.  Agda parsed the
  pair outside `return`; keeping the pair explicitly parenthesised makes the
  monadic boundary clear.
- Product closeness types need parentheses around product endpoints because
  multiplication binds less predictably against the custom closeness syntax.
  The explicit endpoint style is retained in the checked theorem.
- Standard `Field` packaging was inspected and deliberately not attempted.
  Its nonzero argument is negative equality, not apartness.  The signed
  inverse developed here is the constructively valid operation and does not
  justify converting every `¬ (x ≡ 0)` into `0 ＃ x`.
- Positivity cannot be recovered merely from the inverse identity and
  non-negativity: doing so would again collapse negative nonzero information
  into positive apartness.  The checked proof instead retains quantitative
  content by comparing with a rational inverse at an Archimedean upper bound.

Validation on 2026-07-30:

- all 49 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the changed generic completion closeness module, the generic completion
  facade, approximations module, and lift module returned exit code 0;
- the unchanged legacy `CauchyReals.Foundation` and `CauchyReals.Algebra`
  umbrellas returned exit code 0;
- every successful check reported zero holes, unsolved metas, unsolved
  constraints, and warnings.

### 2026-07-30 — polynomials, sequences, finite sums, and initial series

- Added increasing-degree Horner polynomial evaluation over the new reals and
  rationals.  Embedded rational coefficients and arguments compute to the
  embedded rational Horner value.
- Proved continuity of every polynomial structurally from domain-polymorphic
  addition and multiplication continuity combinators.
- Defined the absolute-coefficient polynomial majorant.  Proved that it is
  nonnegative on nonnegative radii and bounds the absolute value of the
  original polynomial at `x` when evaluated at `absℝ x`.
- Specialised the generic premetric sequence vocabulary without copying its
  definitions.  Proved that every modulus-carrying real Cauchy sequence has a
  limit by converting it to a rational-radius approximation and applying
  generic completion completeness.
- Added a proof-independent chosen limit for a supplied Cauchy witness and
  proved independence from the particular modulus/proof.
- Added generic eventual equality for sequences, with preservation of Cauchy
  status and limits, and generic preservation by finite shifts.
- Added generic Cauchy-sequence preservation by non-expanding maps and by
  maps equipped with explicit uniform-continuity or Lipschitz moduli.
- Added generic product-sequence limit and Cauchy theorems.
- Generalised pointwise addition, multiplication, and maximum continuity over
  arbitrary source premetrics.  Used product sequences to derive real limit
  laws for addition, subtraction, multiplication, maximum, negation,
  absolute value, and polynomial evaluation.
- Proved that eventual termwise inequalities pass to real sequence limits.
  The proof uses continuity of maximum, eventual equality, and uniqueness of
  limits, keeping order closedness separate from epsilon arithmetic.
- Proved preservation of Cauchy sequences by negation, absolute value,
  addition, subtraction, maximum, and minimum.  Proved bounded multiplication
  preserves Cauchy sequences with an explicit modulus derived from the common
  bound.
- Proved that finite `FinVec` sums preserve both limits and Cauchy status.
- Added recursive partial sums, `HasSum`, proposition-valued `Summable`,
  modulus-carrying `IsCauchySeries`, and conversion of Cauchy series to
  summable series.
- Proved partial-sum and infinite-sum laws for zero, negation, addition, and
  subtraction; proof independence of the sum; comparison and nonnegativity;
  the necessary condition that summable terms tend to zero; and
  `abs(sum terms) ≤ sum (abs ∘ terms)` when both series are summable.

#### Constructive boundary exposed by this slice

- A real Cauchy sequence carries a selected modulus, whereas `isLimitSeq`
  deliberately truncates each eventual index.  Consequently convergence
  cannot in general be turned back into a selected Cauchy modulus without a
  choice principle.  The APIs keep these notions distinct.
- For the same reason, a proof that the absolute-value series merely has a
  limit is not yet enough to manufacture an `IsCauchySeries` witness for the
  original series.  The next absolute-convergence theorem will start from a
  modulus-carrying absolute Cauchy series (or an equivalent explicit tail
  criterion).
- Total multiplication preserves limits by local continuity, but preservation
  of Cauchy moduli needs a supplied common bound.  This is reflected directly
  in `boundedMulPresIsCauchySeq`.
- No analysis consumer required a structure-valued apartness field.  Its
  design remains deferred instead of introducing an abstraction with only
  one instance and no generic theorem.

Validation on 2026-07-30:

- all 56 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the changed generic completion closeness, premetric properties, mappings,
  and product modules returned exit code 0;
- the legacy `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero holes, unsolved metas, unsolved constraints, and
  warnings.

### 2026-07-30 — explicit tails, absolute convergence, geometric series, and polynomial bounds

- Proved the exact shifted-partial-sum identity and its absolute-value
  estimate.  Derived ordered and unordered bounds for the distance between
  two partial sums, both for the absolute term sequence and for an arbitrary
  pointwise dominating sequence.
- Used those estimates to transfer the actual Cauchy modulus of a dominating
  series to the dominated series.  Specialised this to show that an
  absolutely Cauchy series is Cauchy, summable, and absolutely summable, with
  the expected bound on the absolute value of its sum.
- Added reflection of convergence to zero through absolute value.  This is a
  sequence theorem, not a geometric special case, and uses the exact bridge
  between closeness and strict absolute difference.
- Defined real geometric terms and proved
  `(1-x) · partialSum(xⁿ,n) = 1-xⁿ` by explicit ring laws.  When `x < 1`,
  any supplied proof that `xⁿ → 0` now gives the sum
  `(1-x)⁻¹`, using the constructive positive reciprocal.
- Proved that a Cauchy modulus for the series of `|x|ⁿ` yields absolute
  Cauchy convergence, ordinary summability, and power decay for the series of
  `xⁿ`.
- Added `RationalContractionBound` and the comparison layer: if
  `|x| < q < 1` and the embedded rational `q`-geometric series has a Cauchy
  modulus, that same analytic input yields absolute convergence and the
  reciprocal sum formula for `x`.
- Kept the remaining pure rational theorem explicit: constructing a Cauchy
  modulus for every positive rational `q < 1` is now the only missing link
  between a rational contraction bound and the unconditional geometric
  convergence theorem.  It no longer requires any changes to the real
  finite-tail, comparison, or sum layers.
- Proved monotonicity of the polynomial majorant in its nonnegative radius.
  Defined the recursive Horner Lipschitz majorant
  `L(a :: p,R) = M(p,R) + R·L(p,R)` and proved
  `|P(x)-P(y)| ≤ L(P,R)·|x-y|` whenever both inputs lie in the absolute
  `R`-ball.

#### Approaches corrected during this slice

- The generic commutative-ring solver did not finish the first geometric
  normalisation within a minute.  It was stopped and replaced by explicit
  distributivity and additive-cancellation paths; the resulting module checks
  in under two seconds.
- The geometric convergence theorem was initially tempting to state only
  under a rational bound.  Separating `xⁿ → 0` from its producers gives a
  stronger theorem and leaves rational decay as a small, auditable arithmetic
  obligation.
- The polynomial estimate must use a real-valued majorant first.  Turning it
  directly into a positive-rational Lipschitz record would require selecting
  a rational upper bound for a real coefficient expression, which is only
  merely available in the current constructive interface.

Validation on 2026-07-30:

- all 62 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero holes, unsolved metas, unsolved constraints, and
  warnings.

### 2026-07-30 — selected rational decay and stable series operations

- Closed the rational arithmetic boundary left by the first geometric-series
  slice.  For `0 ≤ q < 1`, proved the Bernoulli-style estimate
  `qⁿ · (1 + n·(1-q)) ≤ 1`.
- Selected a positive block length from the ceiling of `(1-q)⁻¹` and used the
  factor estimate to prove `qᵏ ≤ 1/2` at that block.  Combining this with the
  existing dyadic decay theorem gives the explicit modulus
  `k · N(ε)` and the checked estimate `qⁿ < ε` above that modulus.
- Kept the inductive natural coefficient in a recursive rational form and
  converted it to `ℚ.fromNat` at a single boundary.  This avoids exposing the
  quotient implementation's non-definitional `n · 1 = n` reductions inside
  every induction step.
- Lifted the selected modulus to convergence and Cauchy status of the embedded
  rational powers.  Rewrote rational geometric partial sums as
  `(1-q)⁻¹ · (1-qⁿ)` and obtained a selected Cauchy modulus using rational
  scalar preservation.
- Removed the assumed-rational-majorant premise from the comparison
  endpoint.  A `RationalContractionBound x` now directly yields absolute
  Cauchy convergence, ordinary Cauchy convergence, summability, and the
  reciprocal sum formula for the geometric series of `x`.
- Added constant Cauchy sequences and preservation of Cauchy moduli by a
  fixed rational scalar.  The scalar theorem uses a concrete rational
  Lipschitz bound, so it does not attempt to eliminate a merely available
  real bound into modulus-carrying data.
- Added general series operations:
  arbitrary real scalar multiplication preserves sums; rational scalar
  multiplication preserves Cauchy series; dropping a finite prefix preserves
  both Cauchy status and summability; and the tail sum is the original sum
  minus the prefix partial sum.
- Proved invariance under arbitrary finite term modifications.  If two term
  sequences are eventually equal, Cauchy status and summability transfer, and
  the new sum differs by the exact difference of their partial sums at the
  eventual-equality index.
- Added pointwise products under an explicit uniform bound.  A uniformly
  bounded factor times an absolutely Cauchy series is absolutely Cauchy,
  absolutely summable, and summable.
- Packaged the Horner estimate with explicit rational radius and Lipschitz
  bounds.  Polynomial evaluation now transports a selected Cauchy modulus for
  any sequence that remains in the supplied rational ball.

#### Performance and proof-engineering decisions

- The nonlinear ordered rational solver was stopped after it failed to finish
  the first factor-step attempt.  The replacement decomposes the estimate
  into monotonicity of two products and a final additive bound.
- A second stall was isolated definition by definition.  Its mathematical
  content was only `1 + 1 = 2`, but the rational equality solver attempted to
  normalise it in a context containing a symbolic quotient-valued block.
  Replacing that invocation with the explicit `ℕ+→ℚ+ 1 1` path restored
  roughly two-second checks for the full rational geometric module.
- A temporary commented duplicate used during that isolation was removed
  after the explicit proof checked.  The finished module contains no
  diagnostic scaffold, holes, or solver-blocked constraints.
- The full Cauchy product has deliberately not been claimed from the
  pointwise-product result.  It needs a triangular finite-convolution
  reindexing theorem and a two-dimensional tail estimate; those should be
  established explicitly before the analytic convergence argument.

Validation on 2026-07-30:

- all 66 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero holes, unsolved metas, unsolved constraints, and
  warnings.

### 2026-07-30 — constructive Cauchy products and Mertens estimates

- Added generic selected asymptotic closeness for real sequences.  Such a
  witness transfers both a selected Cauchy modulus and a limit; the latter
  proof keeps the pre-existing propositional truncation at the limit
  boundary.
- Added reusable finite-sum infrastructure: pointwise equality was moved to
  the series base, monotonicity may now be restricted to indices below the
  finite cutoff, and nonnegative partial sums are monotone in their cutoff.
- Defined the finite Cauchy convolution
  `cₙ = Σ_{k≤n} aₖ b_{n-k}` recursively through the existing `partialSum`
  interface.  Proved:
  - first-row and singleton identities;
  - the rectangular finite-product identity;
  - the triangular reindexing
    `partialSum (cauchyProduct a b) n = Σ_{i<n} aᵢ B_{n-i}`;
  - `|cₙ|` bounded by the convolution of the absolute terms.
- Isolated the exact missing-rectangle term
  `Rₙ = Σ_{i<n} aᵢ(Bₙ-B_{n-i})` and checked
  `AₙBₙ = Cₙ + Rₙ`.  Selected vanishing, an explicit strict-absolute-value
  modulus, and asymptotic rectangular approximation were proved equivalent
  in the directions needed by the convergence theory.
- Proved the constructive Mertens estimate.  Given:
  - an absolute Cauchy modulus for `a`;
  - a Cauchy modulus for `b`;
  - a rational bound on all absolute partial sums of `a`; and
  - a rational bound on all ordinary partial sums of `b`,

  the selected remainder modulus uses
  `N(ε) = N_b(ε/(4A)) + N_|a|(ε/(4·2B))`.
  Below the split, the `b` modulus controls the finite prefix; above it, the
  absolute tail of `a` is multiplied by the global `2B` difference bound.
  The resulting estimate is actually `< ε/2`, leaving a stable margin.
- Derived Cauchy status, summability, and the product-of-sums formula for the
  convolution.  A second interface accepts rational upper bounds on the two
  total-variation sums and automatically turns them into uniform absolute
  partial-sum bounds.
- Added a nontrivial geometric consumer.  Every rational contraction bound
  now produces an explicit rational total-variation bound
  `(1-q)⁻¹`; hence convolutions of two geometrically contracting real power
  sequences are Cauchy and summable, with sum
  `(1-x)⁻¹ · (1-y)⁻¹`.

#### Performance and proof-engineering decisions

- The initial geometric consumer did not finish checking after 90 seconds.
  Definition-by-definition isolation found the first slow definition to be
  the comparison between the absolute geometric sum and its rational
  majorant.
- The mathematics and the Mertens module were not responsible: the latter
  continued to check in about two seconds.  The slowdown came from unifying
  repeated, expanded proof-dependent arguments of `seriesSum`.
- Factoring the rational Cauchy/summability proof, geometric absolute-Cauchy
  proof, canonical summability proof, and contraction sum bound into named
  definitions removed that expansion.  The complete geometric convolution
  module then returned to roughly two-second checks.  All temporary block
  comments used during isolation were removed.

Validation on 2026-07-30:

- all 69 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero explicit holes, unsolved metas, unsolved
  constraints, and warnings.

### 2026-07-30 — convolution symmetry and bounded-coefficient power series

- Proved that a finite partial sum is invariant under reversal of its first
  `n + 1` terms.  Combined with bounded subtraction involutivity, this gives
  pointwise commutativity of the recursively defined Cauchy product.
- Exposed symmetric Mertens approximation, Cauchy, summability, and sum
  theorems.  They reuse convolution commutativity and the original asymmetric
  estimate; no second two-dimensional remainder proof was introduced.
- Added cutoff-sensitive pointwise equality and nonnegativity of partial sums
  to the series base.
- Added `Series.Bounds`, providing:
  - monotone weakening of rational partial-sum bounds;
  - additive closure of ordinary and total-variation bounds;
  - scalar closure when the scalar has a supplied rational absolute bound.
- Introduced a bounded-coefficient power-series layer:
  - `powerSeriesTerms`, summability at a point, and evaluation;
  - absolute convergence whenever `|aₙ| ≤ C` and `|x| < q < 1`;
  - termwise domination by `Cqⁿ`;
  - the explicit total-variation bound `C/(1-q)`;
  - coefficient-bound, summability, and value closure under addition and
    scalar multiplication.
- Proved the exact coefficient identity
  `(a * b)(x) = cauchyProduct (a(x)) (b(x))` term by term, using
  `xᵏxⁿ⁻ᵏ = xⁿ` below the finite cutoff.  Mertens then gives:
  - summability of the power series whose coefficients are the Cauchy
    convolution of two bounded coefficient sequences; and
  - evaluation of that convolution as the product of the two evaluations.

#### Performance and proof-engineering decisions

- The initial coefficient-product module exceeded one minute.  Incremental
  isolation located the first expensive declaration in a local four-factor
  ring rearrangement, before any analytic theorem.  Explicitly typing all
  helper binders as reals and all indices as naturals removed overloaded
  structure search and restored a roughly two-second check.
- A later product-bound proof showed the same outward symptom for a different
  reason: a dependent sum-bound type forced comparison of two expanded
  absolute-Cauchy witnesses.  Reusing the already named local witness through
  the general majorant-bound theorem avoided the comparison and again
  restored the normal check time.
- All temporary block comments used to locate these declarations were
  removed.

Validation on 2026-07-30:

- all 75 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero explicit holes, unsolved metas, unsolved
  constraints, and warnings.

### 2026-07-31 — finite-tail bounds and coefficient-majorized power series

- Extended `Series.Bounds` with separate interfaces for:
  - a bound on a finite prefix;
  - a uniform bound on all partial sums of a tail;
  - the corresponding two total-variation notions.
- Added prefix-and-tail combiners.  Dropping a prefix preserves a supplied
  total-variation bound exactly.  For ordinary partial sums, a dropped tail is
  the difference of two bounded partial sums and is therefore bounded by
  `B + B`.
- Quantified finite-modification closure.  An eventually equal replacement
  with finite-prefix bound `F` inherits:
  - total-variation bound `F + A` from an original bound `A`; and
  - ordinary partial-sum bound `F + (A + A)`.
- Added `Series.Rational`, connecting rational-valued sequences and their
  rational partial sums to the real series interface.  Rational ordinary and
  absolute partial-sum inequalities now directly produce the selected real
  bounds required by Mertens and tail arguments.
- Added `PowerSeries.Majorant`.  If `|aₙ| ≤ mₙ`, the majorant coefficients are
  nonnegative, `|x| ≤ r`, and `Σ mₙrⁿ` is Cauchy, then the power series for
  `a` at `x` is absolutely Cauchy and summable.  The module also transports
  total-variation comparisons and rational upper bounds.
- Added `PowerSeries.FiniteModification`.  A sequence whose coefficients are
  bounded after some finite index has an absolutely convergent power series
  at every supplied rational contraction.  The proof zeros the exceptional
  prefix, applies the bounded-coefficient theorem, and transfers convergence
  back by eventual equality.
- Added concrete geometric consumers:
  - the unit coefficient sequence evaluates to `(1 - x)⁻¹`;
  - its self-convolution has coefficient equal to the real natural `n + 1`;
  - the resulting linearly growing power series is summable and evaluates to
    `(1 - x)⁻¹ · (1 - x)⁻¹`.
- Strengthened Mertens at the absolute boundary.  The Cauchy product of two
  absolutely Cauchy series with selected total-variation bounds `A` and `B`
  is absolutely Cauchy and has total variation bounded by `A · B`.
- Added the corresponding power-series product layer, including:
  - absolute convergence and a multiplicative bound for coefficient
    convolution;
  - summability and the product-of-values theorem without coefficient
    boundedness;
  - bundled `AbsoluteCauchySeriesWithBound` and
    `PowerSeriesAbsoluteWithBound` interfaces.
- Added an arbitrary finite iterated-geometric family.  Order zero is the
  unit coefficient sequence and each successor is one more convolution with
  it.  For every rational contraction the family has:
  - a selected absolute-Cauchy witness;
  - the recursively multiplied rational total-variation bound;
  - summability; and
  - value equal to the corresponding iterated product of `(1 - x)⁻¹`.
  Order one is definitionally the previously proved linear-growth sequence.

#### Performance and proof-engineering decisions

- The new modules checked at the normal scale for this development; no new
  elaboration stall was found.
- The ordinary dropped-tail proof initially supplied an equality of
  differences where an equality of absolute values was required.  Transport
  through `cong absℝ` made the intended boundary explicit.
- The linear-growth theorem deliberately uses the checked convolution
  algebra.  This avoids a second analytic convergence proof and establishes
  a path toward higher polynomial growth by iterated convolution.
- The first degree-indexed implementation passed convergence witnesses and
  their dependent sum bounds separately.  Both its recursive version and an
  explicitly unrolled quadratic consumer stalled for more than 30 seconds at
  the first concrete absolute-product application.
- Splitting definitions alone did not fix that stall.  Bundling the witness
  and bound, and making generic series/power-series product closure opaque,
  removed proof-witness normalization.  The complete recursive family,
  including its value theorem, then checked in about two seconds.  The
  temporary unbundled and unrolled implementations were removed.

Validation on 2026-07-31:

- all 82 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero explicit holes, unsolved metas, unsolved
  constraints, and warnings.

### 2026-07-31 — closed iterated coefficients and formal differentiation

- Added the natural finite-sum family `simplexCoefficient`.  Its successor
  order is the prefix sum of the preceding order, exactly mirroring
  convolution with the unit coefficient sequence.
- Proved that the real iterated-geometric coefficient is the natural
  embedding of the corresponding simplex coefficient.  This proof uses
  convolution commutativity and finite-sum transport, without binomial
  arithmetic.
- Proved the natural hockey-stick identity and obtained the closed formula
  `simplexCoefficient d n = C(n+d,d)`.  Consequently the real coefficient at
  order `d` is the embedded binomial coefficient.
- Proved nonnegativity and the explicit polynomial estimate
  `C(n+d,d) ≤ (n+1)^d`.  The transported real estimate is packaged as a
  `CoefficientMajorizedBy` witness, so later convergence arguments can use
  the general majorant interface.
- Moved `realNatural` out of the geometric-series example into
  `Algebra.Natural`, and added its preservation of addition and
  multiplication, nonnegativity, and monotonicity.
- Added the generic formal coefficient derivative
  `Daₙ = (n+1)aₙ₊₁`, including:
  - linearity under coefficient addition and scalar multiplication;
  - its term-level power-series formula;
  - transport of arbitrary nonnegative coefficient majorants.
- Proved the structural identity
  `(n+1)S_d(n+1) = (d+1)S_{d+1}(n)` for simplex coefficients.  It yields the
  complete formal-derivative law
  `D(iteratedGeometric d) = (d+1) · iteratedGeometric(d+1)`.
- As analytic consequences already justified by the existing series theory,
  the formally differentiated series is summable at every rational
  contraction and evaluates to `(d+1)` times the next reciprocal power.
  This is deliberately not yet presented as a derivative of a real
  function.

#### Performance and proof-engineering decisions

- All new coefficient and derivative modules remain at the normal
  approximately two-second direct-check scale.
- The Nat solver initially unfolded locally named simplex expressions and
  attempted to treat an unsaturated sequence as a natural.  Moving the two
  pure semiring rearrangements to helpers quantified only over naturals kept
  reflection independent of the recursive coefficient definition.
- The value theorem is opaque.  Its proof transports a scaled summability
  witness through coefficient equality once; downstream users see only the
  mathematical equality and do not normalize proof-dependent `seriesSum`
  arguments.

Validation on 2026-07-31:

- all 86 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero explicit holes, unsolved metas, unsolved
  constraints, and warnings.

### 2026-07-31 — local uniform convergence and continuous evaluation

- Added `Analysis.Series.Uniform`, with:
  - ordinary and absolute uniform Cauchy series over an arbitrary parameter
    type;
  - pointwise Cauchy and summability projections;
  - uniform domination by one fixed Cauchy majorant;
  - an explicit estimate from sufficiently late partial sums to the selected
    series value;
  - the theorem that a uniformly Cauchy series of continuous terms has a
    continuous value function.
- The continuity theorem remains premetric rather than topological.  Its
  parameter type acquires a premetric only at the final theorem, while the
  uniform modulus and domination machinery remain usable for arbitrary
  families.
- Added `PowerSeries.Uniform`.  A closed absolute-value radius is represented
  both as the type `Σ x, |x| ≤ r` and as the corresponding inherited
  premetric subspace.  A nonnegative coefficient-majorant series that is
  Cauchy at the boundary supplies one common absolute Cauchy modulus for all
  points in the closed radius.
- Proved continuous closed-radius evaluation for every uniformly Cauchy power
  series.  The proof factors through continuity of natural powers, individual
  power-series terms, finite partial sums, and the generic uniform-limit
  theorem.
- Added general local-uniform consumers for formal derivatives.  If
  `|aₙ| ≤ mₙ`, the majorant coefficients are nonnegative, and the formal
  derivative of the majorant is Cauchy at the boundary, then the formal
  derivative of the original power series is uniformly absolutely Cauchy on
  the closed radius.
- Added `IteratedGeometric.Uniform`.  For every finite order and every
  contraction boundary:
  - the iterated-geometric series is uniformly absolutely Cauchy and uniformly
    Cauchy throughout the closed radius;
  - its formal derivative has the same two properties;
  - both canonical closed-radius value functions are continuous.
- Added two supporting reusable facts: rational scaling preserves absolute
  Cauchy convergence, and a contraction bound on a radius induces a
  contraction bound at every point inside that radius.
- Extended the natural embedding by
  `realNatural n = rat (fromNat n)`.  This makes the derivative scale
  `(d+1)` available to the rational-scaling Cauchy theorem without selecting
  an arbitrary real bound.

#### Performance and proof-engineering decisions

- The uniform series, generic power-series uniformity, and specialised
  iterated-geometric uniformity modules check at the normal approximately
  two-second scale.
- A direct theorem restating the existing reciprocal-power value formula for
  the new canonical closed-radius function was tried twice: first by direct
  witness alignment, then through an explicit `seriesSumIndependent` bridge.
  Each version still ran beyond 30 seconds.  Bisection showed that even the
  non-derivative restatement was enough to trigger the stall.  The redundant
  declarations were removed; the pointwise value theorems and the new
  continuity theorems remain independently available and fast.

Validation on 2026-07-31:

- all 89 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero explicit holes, unsolved metas, unsolved
  constraints, and warnings.

### 2026-07-31 — divided differences and analytic differentiation

- Added the generic premetric derivative predicate `IsDerivativeAlong`.
  Its domain may be any premetric parameter space equipped with a real
  coordinate, and its conclusion is the division-free first-order remainder
  estimate.  This makes relative differentiation on closed-radius subspaces
  a direct instance instead of forcing a premature open-set API.
- Proved that a continuous divided difference `Q(x,y)` with
  `f(y)-f(x) = (u(y)-u(x))Q(x,y)` and `Q(x,x)=f'(x)` supplies such a
  derivative.  The proof uses continuity only at diagonal pairs and turns
  output closeness into an absolute-value bound.
- Developed the algebraic divided difference of natural powers and proved:
  - exact factorization of `y^(n+1)-x^(n+1)`;
  - its diagonal value `(n+1)x^n`;
  - continuity under continuous parameter maps; and
  - the sharp closed-radius bound `(n+1)r^n`.
- Lifted the construction coefficientwise to power series.  The resulting
  term is dominated by the formal-derivative majorant, and finite partial
  sums satisfy the exact factored difference identity.
- Added uniform convergence of the divided-difference series over pairs of
  points in a closed radius.  One Cauchy witness for the formal-derivative
  majorant controls every pair simultaneously, and continuity of the value
  follows from the generic uniform-limit theorem.
- Proved the infinite-sum factorization by uniqueness of sequence limits.
  A new `seriesSumPresPath` helper transports a sum across equality of term
  sequences without asking Agda to compare proof-dependent summability
  witnesses.
- Combined these layers into the analytic theorem: a uniformly convergent
  power series whose formal-derivative majorant converges at the radius has
  the uniformly summed formal derivative as its derivative on that closed
  radius.
- Instantiated the theorem for every iterated-geometric order.  The canonical
  reciprocal-power value has derivative `(d+1)` times the next reciprocal
  power.  Both the power-series formulation and the explicit closed form are
  checked.

#### Performance and proof-engineering decisions

- The new generic derivative and divided-difference modules remain at the
  normal roughly two-to-four-second direct-check scale.
- The formerly stalled canonical closed-radius value restatement now checks
  quickly because the proof goes through equality of sequences and uniqueness
  of limits rather than dependent equality of summability witnesses.
- The derivative proof does not separately exchange a derivative and an
  infinite limit.  Uniform convergence of the divided difference packages
  exactly the needed remainder control and avoids division at zero.

Validation on 2026-07-31:

- all 94 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all checks reported zero holes, unsolved metas, unsolved constraints, and
  warnings.

### 2026-07-31 — finite polynomials and derivative locality

- Specialised the derivative interface to ordinary real functions with
  `IsDerivative`, and added the pointwise form `IsDerivativeAt`.  Global
  derivatives now project to pointwise derivatives without repackaging the
  remainder estimate at every consumer.
- Added checked derivative theorems for constant functions, the identity, and
  every natural power.  The power theorem reuses the existing algebraic power
  divided difference, so its derivative is the explicit real natural
  coefficient `(n + 1)xⁿ`.
- Added the first closure theorem for the derivative predicate itself:
  pointwise addition preserves `IsDerivativeAlong` and `IsDerivative`.  Its
  proof divides the requested error between the two summands and retains the
  selected quantitative moduli.
- Developed a Horner divided difference for increasing-degree coefficient
  lists.  It satisfies the exact factorization of `P(y) - P(x)`, has the
  formal Horner derivative on the diagonal, and is continuous for every
  continuous real coordinate on an arbitrary premetric parameter space.
  Consequently every finite Horner polynomial has its expected derivative,
  both relatively and as an ordinary real function.
- Embedded finite coefficient lists into the infinite power-series interface
  by zero padding.  Proved the exact partial-sum/Horner recurrence, vanishing
  beyond the list length, stabilization of partial sums, summability, and
  equality of the selected power-series value with Horner evaluation.
- Strengthened that bridge uniformly on every closed radius.  Finite power
  series have the list length itself as a uniform Cauchy modulus; their
  canonical uniform value is the Horner polynomial and inherits the checked
  relative derivative theorem.
- Added the locality bridge from a derivative on a closed absolute-value
  radius to an ordinary derivative at each strict interior point.  A positive
  margin to the boundary supplies a neighbourhood which stays in the closed
  radius, and the proof combines that margin with the relative derivative's
  own modulus.
- Generalised polynomial continuity from the identity coordinate to any
  continuous real coordinate, which is the reusable fact needed by the
  Horner divided difference rather than a derivative-specific duplicate.

#### Performance and proof-engineering decisions

- All new modules check at the normal roughly two-to-four-second direct-check
  scale; no new elaboration stall was observed.
- Exact stabilization is preferable to applying the general coefficient
  majorant machinery to a finite sequence.  It gives the sharp uniform
  modulus immediately and keeps proof-dependent convergence witnesses small.
- The polynomial derivative proof deliberately follows one recursive divided
  difference.  Repeatedly applying a future product rule to Horner evaluation
  would produce weaker local bounds and larger elaboration terms for no
  mathematical benefit.

Validation on 2026-07-31:

- all 101 Agda modules inside `CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` entry point were checked directly with
  `agda-codex` and returned exit code 0;
- the four changed generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas returned exit code 0;
- all 109 checks reported zero holes, unsolved metas, unsolved constraints,
  and warnings.

### 2026-07-31 — derivative algebra and finite formal derivatives

- Extended the remainder-based derivative algebra with negation and
  subtraction.  Both reuse exact error identities, so their proofs preserve
  the original modulus without introducing additional estimates.
- Added scaling by any real scalar equipped with an explicit positive
  rational absolute bound.  The proof requests the original derivative at
  the divided radius `ε/B`; rational scaling is a direct specialization using
  a canonical rational maximum bound.
- Proved a constructive product rule on an arbitrary premetric source.  Two
  derivative remainders and continuity of the right factor suffice; a
  symmetric theorem accepts continuity of the left factor.  The proof:
  - extracts local bounds for the two function values and the relevant
    derivative value;
  - uses continuity to bound the nearby value and function increment;
  - decomposes the product remainder into two linear errors and one cross
    term; and
  - assigns quarter, quarter, and half of the target error to those terms.
- Added consecutive natural weighting of finite coefficient lists and defined
  `polynomialDerivativeCoefficients` by dropping the constant coefficient and
  weighting the tail from one.
- Proved structurally that evaluation of this list is the existing Horner
  derivative evaluator.  This proof remains finite algebra and does not rely
  on analytic derivative uniqueness.
- Added `PowerSeries.Polynomial.Derivative`, proving that zero padding the
  derivative coefficient list is exactly the formal derivative of the
  zero-padded original list.
- Derived finite summability and uniform closed-radius convergence for that
  formal derivative, identified its canonical value with the Horner
  derivative, and restated the finite power-series derivative theorem with
  the canonical termwise derivative function as its target.

#### Performance and proof-engineering decisions

- The product algebra was isolated as an equality over explicitly named real
  values before quantitative bounds were introduced.  This avoids asking
  normalization to unfold function applications or the coherent definition
  of multiplication.
- The product proof remains asymmetric internally because this yields a
  smaller error decomposition.  Commutativity transports it to the symmetric
  left-continuous interface without duplicating estimates.
- Finite formal differentiation is proved by structural list recursion and
  exact equality of coefficient sequences.  No comparison of expanded
  summability witnesses is needed; series values are transported through
  `seriesSumPresPath`.
- Direct checks of all changed modules remained at the normal approximately
  two-to-three-second scale, with no elaboration stall.

Validation on 2026-07-31:

- all 102 Agda modules inside `Cubical/HITs/CauchyRealsP/` and the
  `Cubical.HITs.CauchyRealsP` root umbrella returned exit code 0 from direct
  `agda-codex` checks;
- the four modified generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas also returned exit code 0;
- all 110 checks completed in 206 seconds, with no holes, unsolved metas,
  unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-07-31 — derivative continuity and composition

- Added `derivativeAlongLocalLinearBoundAt`.  Given
  `|f'(x)| ≤ B`, it obtains a derivative neighbourhood on which
  `|f(y)-f(x)| ≤ (1+B)|coordinate(y)-coordinate(x)|`.
- Proved that an along-coordinate derivative makes its function continuous
  whenever the coordinate map is continuous.  The ordinary real derivative
  therefore implies ordinary premetric continuity without an additional
  hypothesis.
- Used the new theorem to expose product differentiation without separately
  supplied factor continuity.  The more primitive asymmetric product rules
  remain available because they are useful when continuity is already known
  independently.
- Added a chain rule for an arbitrary premetric source and continuous
  real-valued coordinate.  The derivative of `outer (inner x)` is
  `outer' (inner x) · inner' x`.
- Added finite Horner polynomial composition as the first concrete chain-rule
  consumer, both along an arbitrary continuous coordinate and for ordinary
  real functions.

#### Proof-engineering decisions

- The continuity proof separates a reusable local linear estimate from the
  final conversion to source continuity.  This avoids hiding the necessary
  coordinate-continuity premise in the definition of differentiation.
- The chain proof first establishes the exact identity
  `E(outer ∘ inner) = E(outer) + outer' · E(inner)`.  It then allocates half
  the target error to each term and eliminates local Archimedean bounds only
  inside the proposition-valued derivative modulus.
- The chain implementation shares the local inner-function estimate with the
  continuity theorem.  No inverse increment, apartness case, or selected
  global derivative bound is introduced.
- Direct checks of the new continuity, chain, algebra, polynomial, and
  analysis-umbrella modules completed at the normal two-to-three-second
  scale, with no holes, metas, warnings, or elaboration stalls.

Validation on 2026-07-31:

- all 104 Agda modules inside `Cubical/HITs/CauchyRealsP/` and the
  `Cubical.HITs.CauchyRealsP` root umbrella returned exit code 0 from direct
  `agda-codex` checks;
- the four modified generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas also returned exit code 0;
- all 112 checks completed in 210 seconds, with no holes, unsolved metas,
  unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-07-31 — uniqueness and positive-domain reciprocal calculus

- Proved that ordinary derivative values are unique.  Given two derivative
  moduli at a point, the proof evaluates both remainders at the common
  rational increment `min(δ₁,δ₂)/2`, bounds their difference, and
  cancels the resulting explicitly positive distance.
- Derived proposition-valuedness of `IsDerivative`, `IsDerivativeAt`, and
  their existential packages `HasDerivative` and `HasDerivativeAt`.
  Function-level uniqueness follows by pointwise uniqueness and function
  extensionality.
- Added polynomial consumers showing that any derivative assigned to Horner
  evaluation equals the structural Horner derivative, both pointwise and as
  a derivative function.
- Introduced the premetric subspace of reals satisfying
  `rat η ≤ x` for a fixed positive rational `η`.  The existing bounded
  reciprocal is continuous there, satisfies the exact inverse law, and has
  derivative `-(inv x · inv x)` relative to the inherited real coordinate.
- Proved reciprocal differentiation through the exact continuous two-point
  factor `-(inv x · inv y)`.  No difference quotient, nonzero-to-apartness
  inference, or choice of a hidden local lower bound is used.
- Identified the bounded implementation with the existing proof-independent
  `positiveReciprocal` on each fixed-bound subspace.
- Extended the result to the full positive-real premetric subspace.  At each
  point the proof halves a positive-gap representative, restricts to a
  neighbourhood which remains above that half-gap, and eliminates the
  truncated witness only into the proposition-valued derivative modulus.
- Added division of an arbitrary differentiated numerator by the positive
  coordinate, both on fixed-bound slices and on the full positive subspace,
  as direct product-rule consumers with derivative
  `f' · inv + f · (-inv²)`.

#### Performance and proof-engineering decisions

- The first uniqueness draft appeared to stall because several algebraic
  helper binders were left to overloaded inference.  Prefix isolation exposed
  blocked real-type constraints; explicit `(a b c : ℝ)` annotations restored
  a roughly three-second complete check.  No mathematical definition was
  weakened.
- The reciprocal coordinate takes its lower-bound parameter explicitly.
  Inferring `η` from the subspace predicate leaves the proof component of
  `ℚ₊` undetermined even though it is propositionally irrelevant.  Making it
  explicit removes four non-interaction metas and keeps composition stable.
- The fixed-lower-bound theorem intentionally precedes the theorem on all
  positive reals.  The later gluing layer eliminates a truncated positive-gap
  witness only after halving it and proving that the selected neighbourhood
  remains inside one fixed-bound subspace.  Keeping these stages separate
  makes the coherence argument and its use of proposition-valued elimination
  explicit.

Validation on 2026-07-31:

- all 106 Agda modules inside `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` umbrella returned exit code 0 from direct
  `agda-codex` checks;
- the four modified generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas also returned exit code 0;
- all 114 checks reported no holes, unsolved metas, unsolved constraints,
  warnings, failures, or elaboration stalls.  The reciprocal module and the
  affected umbrellas were checked again after the final positive-domain
  gluing edit.

### 2026-07-31 — signed reciprocal and general rational-function calculus

- Added source reparameterisation for along-coordinate derivatives and a
  coordinate-negation rule.  Together they transport the positive reciprocal
  theorem to the negative-real subspace without duplicating its analytic
  remainder estimate.
- Added the negative-real premetric subspace and proved that its canonical
  reciprocal has derivative `-inv²`, is continuous, and agrees with the
  existing signed inverse.
- Added the subspace of reals apart from zero.  A positive or negative
  half-gap neighbourhood preserves the point's sign, so the two local
  reciprocal theorems glue to differentiation and continuity of signed
  inverse on the whole apart-real subspace.
- Generalised the chain rule so that the intermediate space may be any
  premetric space equipped with a real coordinate.  This is the structural
  bridge needed to compose with the apart-real subspace rather than
  pretending reciprocal is total on all reals.
- Packaged a pointwise-apart denominator as a continuous map into that
  subspace.  The general chain rule gives the derivative of its reciprocal;
  the product rule then gives quotient differentiation for an arbitrary
  differentiated numerator and denominator.
- Added polynomial rational functions as a direct consumer, including
  uniqueness of their canonical derivative.
- Added the closed example `x ↦ x / (1 + x²)`.  Ordered-ring
  nonnegativity of `x²` proves the denominator positive everywhere, so its
  differentiability theorem has no domain premise.

#### Performance and proof-engineering decisions

- Transporting the negative proof with one anonymous `subst2` term left
  several opaque completion-valued constraints.  Naming the raw derivative
  and its function and derivative paths made the transports exact and kept
  normal checking time.
- The positive and negative local branches of signed reciprocal each checked
  independently in roughly two seconds, while the first final dependent
  `with` split exceeded one minute.  The theorem's target is independent of
  the apartness witness, so replacing that split by nondependent sum
  elimination both expresses the actual dependency and restores the normal
  check time.
- Denominator apartness remains explicit data.  It is not weakened to
  negative equality and no global choice of sign or lower bound is made.

Validation on 2026-07-31:

- all 109 Agda modules inside `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` umbrella returned exit code 0 from direct
  `agda-codex` checks;
- the four modified generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas also returned exit code 0;
- all 117 checks completed in 218 seconds, with no holes, unsolved metas,
  unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-07-31 — natural rational-function domains and quotient normal form

- Defined the natural domain of a denominator as the inherited premetric
  subspace `Σ x , 0 # denominator x`.  Its coordinate projection is
  non-expanding, hence continuous.
- Proved that every ordinary real derivative restricts along this coordinate.
  A differentiable numerator and denominator therefore give a differentiable
  quotient on the denominator's natural domain, even when the denominator has
  roots.
- Added the conventional quotient-rule numerator `f'g - fg'`, proved the raw
  derivative equal to `(f'g - fg') / g²`, and exposed both ordinary and
  along-coordinate theorems with that derivative.
- Added reusable apartness certificates for constant, positive, negative,
  negated, product, power, and difference denominators.  The underlying
  `apartPow` theorem lives with multiplicative apartness rather than in the
  derivative layer.
- Extended arbitrary polynomial quotients to their natural nonvanishing
  domains, using their structural Horner derivatives and the conventional
  quotient formula.
- Added two domain-sensitive consumers:
  - reciprocal shifted to an arbitrary centre, on points carrying `x # c`;
  - `x / ((x-a)(x-b))`, with a constructor from the two explicit root
    exclusions and a checked quotient derivative on the resulting domain.

#### Performance and proof-engineering decisions

- The first four-factor normalization used the generic commutative-ring
  solver over explicitly typed real variables, but still exceeded the normal
  checking window and was stopped.  Explicit associativity, commutativity,
  distributivity, and negation paths check in roughly two seconds and keep
  inverse opacity entirely outside normalization.
- Natural domains retain their apartness proofs as proposition-valued second
  components.  No proof-dependent equality is exposed in function values;
  signed inverse proof irrelevance remains the sole bridge where required.
- The development does not claim that a denominator's nonvanishing locus is
  complete or globally closed.  It is used only as the inherited premetric
  source appropriate for local differentiation.

Validation on 2026-07-31:

- all 112 Agda modules inside `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` umbrella returned exit code 0 from direct
  `agda-codex` checks;
- the four modified generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas also returned exit code 0;
- all 120 checks completed in 238 seconds, with no holes, unsolved metas,
  unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-07-31 — geometric tails and polynomial-prefix power series

- Added the generic converse to finite-shift preservation of sequence limits.
  If `shiftSeq k x` converges, then `x` converges to the same limit; the proof
  only changes the eventual threshold and therefore belongs in
  `Relation.Premetric.Properties`.
- Used that theorem to make series tail removal bidirectional.  A sum for
  `dropSeries start terms` now reconstructs a sum for `terms`, and the exact
  value is the finite partial sum through `start` plus the tail value.
- Added scaled geometric sums, dropped/shifted geometric sums, and a general
  exact eventually-scaled-geometric interface.  Under a rational contraction
  bound, an arbitrary finite prefix followed by `c rⁿ` sums to its prefix
  partial sum plus `c/(1-r)`.
- Lifted exact eventual geometric tails coefficientwise to power series.
  Evaluation at `x` changes the tail coefficient to `c·xˢᵗᵃʳᵗ` and the
  ratio to `r·x`; consequently the natural convergence premise is a rational
  contraction bound for `r·x`, not separately for `r` and `x`.
- Added `polynomialGeometricCoefficients`, an explicit sequence formed from
  any finite increasing-degree coefficient list followed by `c rⁿ`.  Its
  prefix partial sum is proved equal to Horner evaluation, producing the
  closed value

  `P(x) + (c · xˡᵉⁿᵍᵗʰ P) · (1 - r·x)⁻¹`.

#### Proof-engineering decisions

- Finite prefix reconstruction is derived from a shifted limit rather than
  by constructing a new Cauchy modulus.  This preserves ordinary blocking
  and limit semantics and avoids duplicating the completeness argument.
- The coefficient-tail hypothesis is exact equality after dropping the
  prefix.  Eventual equality remains the appropriate interface when only
  convergence is relevant, while exact equality is what makes the closed
  sum formula canonical.
- Power reassociation uses short explicit paths, including distribution of
  powers over products.  No ring solver or normalization-heavy comparison of
  proof-dependent summability witnesses is needed; all new direct module
  checks remain at the normal two-to-three-second scale.

Validation on 2026-07-31:

- all 114 Agda modules inside `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` umbrella returned exit code 0 from direct
  `agda-codex` checks;
- the four modified generic premetric modules and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` umbrellas also returned exit code 0;
- all 122 checks completed in 230 seconds, with no holes, unsolved metas,
  unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-07-31 — derivative convergence beyond an inner radius

- Added a general radius-restriction theorem for a power series with
  nonnegative coefficients.  Cauchy convergence at an outer radius implies
  absolute Cauchy convergence, and hence Cauchy convergence, at every
  nonnegative inner radius below it; a strict-radius corollary weakens `<` to
  `≤` only at the boundary of this theorem.
- Applied radius restriction to the formal-derivative majorant.  Both the
  evaluated formal derivative and the two-variable divided-difference factor
  are now uniformly Cauchy on the inner closed radius when the derivative
  majorant is known to converge at the outer radius.
- Added closed-radius derivative theorems with weak and strict inner-radius
  hypotheses.  In comparison:
  - the original boundary theorem assumes derivative-majorant convergence at
    exactly the conclusion radius;
  - the new theorem assumes convergence at a possibly larger radius plus
    nonnegativity and radius inclusion, and concludes differentiation only on
    the inner closed radius.
- Kept uniform convergence of the original series as a separate premise.
  Convergence of its formal derivative cannot recover the constant term, so
  folding this premise into the derivative-majorant hypothesis would be
  mathematically incorrect.

#### Performance note

- The first derivative wrapper repeated the complete derived uniform witness
  in its dependent result type and did not finish inside one minute.  The
  check was stopped, the witness was factored into a named opaque producer,
  and the unchanged theorem then checked completely in about two seconds.

Validation on 2026-07-31:

- all 114 Agda modules inside `Cubical/HITs/CauchyRealsP/` and the root
  umbrella returned exit code 0 from direct `agda-codex` checks after the
  strict-radius changes;
- the four modified generic premetric modules and the three legacy
  compatibility umbrellas also returned exit code 0;
- all 122 final checks completed in 232 seconds, with no holes, unsolved
  metas, unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-07-31 — rational interpretation of geometric tails and common domains

- Added a uniform natural-power derivative function and theorem, combining
  the previously separate zero and successor cases.  This gives downstream
  constructions a derivative for `xⁿ` without a case split on `n`.
- Reinterpreted every finite-polynomial-prefix/geometric-tail power series as
  the rational function

  `(P(x)(1-r·x) + c·xˡᵉⁿᵍᵗʰ P) / (1-r·x)`.

  Its domain is the canonical inherited subspace where `1-r·x` is apart
  from zero.  The numerator, denominator, quotient, and conventional quotient
  derivative are all checked through the existing derivative algebra.
- Constructed a point in that natural domain from a rational contraction
  bound on `r·x`, using positivity of `1-r·x`, and proved that the canonical
  power-series value equals the rational function at that point.
- Added generic maps between natural denominator domains.  Any pointwise
  implication between denominator-apartness predicates gives a
  coordinate-preserving non-expanding map; pointwise denominator equality
  supplies forward and reverse transports with a checked roundtrip law.
- Applied equality transport to the factored two-pole denominator.  Swapping
  the two poles gives a non-expanding domain map, and swapping twice is the
  identity.
- Added the intersection of two natural denominator domains as a common
  premetric source.  Its non-expanding projections pull each rational
  function and its quotient derivative back to one coordinate space.
- Proved derivative closure for sums and products of two rational functions
  on that common domain.  Numerators and denominators may be unrelated; only
  their ordinary derivative theorems and the two local apartness witnesses
  are required.

#### Proof-engineering decisions

- The rational-series bridge reuses the quotient rule after finite algebra;
  it does not compare the quotient derivative with a separately elaborated
  analytic power-series derivative witness.
- The first two-pole involution proof tried to reuse the generic roundtrip
  theorem directly.  The forward `mulComm` path and the separately generated
  reverse `mulComm` path are propositionally, but not definitionally, equal.
  Replacing that proof-term comparison by `Σ≡Prop` states the relevant
  fact—the coordinate is unchanged and domain evidence is a proposition—and
  restores a normal check.
- Common-domain projections and all new closure modules check at the normal
  roughly two-second scale; no solver or hidden choice of denominator sign is
  used.

Validation on 2026-07-31:

- the natural-power, denominator-domain, two-pole example, geometric-tail
  rational bridge, common-domain operations, rational-function umbrella, and
  analysis umbrella returned exit code 0 from direct `agda-codex` checks
  after their local edits;
- all 116 modules below `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` umbrella returned exit code 0;
- the four modified generic premetric modules and the three legacy
  compatibility umbrellas also returned exit code 0;
- all 124 final checks completed in 230 seconds, with no holes, unsolved
  metas, unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-08-01 — rational composition, denominator normalization, and ambient interior derivatives

- Added the natural domain for composing two rational functions.  It is a
  nested inherited subspace: a point first carries apartness of the inner
  denominator, then apartness of the outer denominator evaluated at the
  resulting inner quotient.
- Constructed the coordinate projection, inner-domain projection, and map to
  the outer natural domain.  The inner quotient derivative supplies its
  continuity, and the chain rule through an arbitrary intermediate
  premetric space proves the conventional derivative of the composite.
- Added a double-reciprocal consumer.  Signed inverse apartness constructs
  every nested-domain point from a shifted-reciprocal-domain point; the
  composite has a checked derivative and its value simplifies exactly back
  to the shifted denominator.
- Added the product of two denominators and its derivative, together with a
  coordinate-preserving non-expanding map from the common two-denominator
  domain to the product-denominator natural domain.
- Added combined numerators for sums and products.  Both single-quotient
  normal forms have conventional quotient derivatives on the common domain,
  and explicit inverse-product/ring calculations prove that their values are
  exactly the direct sum and product of the original quotients.
- Generalised strict-interior recovery from a closed-radius derivative.  A
  relative function and derivative now need only agree with a supplied
  ambient real function on the closed radius; no ambient derivative function
  is required.
- Specialised that extension theorem to uniformly summed power series.  The
  direct divided-difference hypotheses, an outer-radius derivative-majorant
  theorem, and its strict outer-radius wrapper now all yield ordinary
  derivatives of an ambient extension at strict inner points.
- Exported composition and combined-denominator calculus through the
  rational-function umbrella, and the interior power-series consumers through
  the power-series umbrella.

#### Proof-engineering and scope decisions

- The first composition-domain version left numerator and outer-denominator
  parameters implicit in nested projections.  Agda reached a checked source
  but retained twenty non-interaction metas and sixty-five blocked
  constraints, most displayed as expanded real-completion arithmetic.
  Making those parameters explicit removed every meta and restored a normal
  check.  The mathematical interface is unchanged; only elaboration is made
  deterministic.
- Combined-denominator normalization is proved pointwise on the common
  domain.  Both the direct and normalized derivative functions are checked,
  but they are not declared equal merely because the values agree: uniqueness
  of derivatives along an arbitrary coordinate can fail when the coordinate
  is locally constant or its domain is too sparse.
- No equivalence between the common domain and the product-denominator domain
  is claimed.  Only the forward map follows from the currently available
  constructive apartness laws.
- The power-series theorem keeps its ambient extension explicit.  Extending
  a derivative value is unnecessary, while silently extending a function
  beyond its proven convergence radius would be mathematically incorrect.

Validation on 2026-08-01:

- the new composition, combined-denominator, and power-series interior
  modules, their concrete example, the generic interior theorem, and both
  affected umbrellas returned exit code 0 from direct `agda-codex` checks;
- all 119 modules below `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` umbrella returned exit code 0;
- the four modified generic premetric modules and the three legacy
  compatibility umbrellas also returned exit code 0;
- all 127 final checks completed in 228 seconds, with no holes, unsolved
  metas, unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-08-01 — generic neighbourhoods, intervals, extension, and pasting

- Added `Relation.Premetric.OpenPredicate`.  Its predicate universe is
  independent of the carrier universe, and it proves proposition-valuedness,
  openness of the full and empty predicates, finite intersection, continuous
  preimage, and openness of every premetric ball.
- Added real lower/upper open half-lines and open/closed intervals as ordinary
  predicates and inherited premetric subspaces.  Positive-gap witnesses are
  halved to show that strict half-lines, and hence open intervals, are open.
- Generalised the symmetric clamp to `clampInterval a b`.  It is
  non-expanding, fixes every point of `[a,b]`, and is idempotent when `a ≤ b`.
  The analytic interval module packages it as a retraction from the real line
  onto the closed interval, with non-expanding, uniformly continuous, and
  continuous inclusions.
- Added canonical extension from a nonempty closed interval by precomposition
  with the clamp retraction.  The extension agrees on the interval and
  preserves non-expansion, uniform continuity, and continuity into an
  arbitrary target premetric space.
- Added a reusable derivative theorem for open subspaces and its stronger
  form where an open neighbourhood is merely contained in a possibly closed
  derivative domain.  Closed-interval derivatives now yield ordinary
  derivatives at strict interior points, either for a supplied ambient
  extension or for the canonical clamp extension.
- Ported the algebraic min/max pasting construction and its exact left/right
  restrictions.  This establishes the proof-relevant order-domain interface
  needed before continuous pasting is layered on top.
- Exported the stable interval, derivative, and pasting modules through the
  analysis facade; exported open predicates through the generic premetric
  facade.

#### Proof-engineering and scope decisions

- `Predicate` was made universe-polymorphic independently of its carrier.
  Reusing `ℙ A` alone would unnecessarily force predicate truth values into
  the carrier universe and made preimages between differently sized carriers
  ill-typed.
- Open balls use roundedness first, then half of the remaining rational-radius
  gap.  This derives the neighbourhood entirely from `IsPremetric`; no real
  order or completion property leaks into the generic module.
- The first pasting proof checked semantically but retained six metas and
  eight blocked constraints.  They came from an unconstrained reflexivity
  proof under binary subtraction, whose endpoints expanded through real
  negation.  Naming the exact endpoint in `refl` removed all metas and kept
  the normal two-second direct check.  Explicit dependent function types
  remain in the statement to keep later elaboration deterministic.
- A full topology record, arbitrary unions, connectedness, and endpoint
  theorems were deliberately not bundled into this milestone.  The extracted
  neighbourhood layer is sufficient for its current consumers and leaves the
  eventual topology representation reversible.

Validation on 2026-08-01:

- all 126 Agda modules below `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` facade returned exit code 0 from direct
  `agda-codex` checks;
- the generic premetric facade, the new open-predicate module, the four
  previously modified generic premetric modules, and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and `CauchyReals.Sequence`
  facades also returned exit code 0;
- all 136 checks completed in 252 seconds, with no holes, unsolved metas,
  unsolved constraints, warnings, failures, or elaboration stalls.

### 2026-08-01 — retract completeness, radius geometry, and continuous pasting

- Added preservation of rationally indexed Cauchy approximations by
  non-expanding maps and the generic theorem that a non-expanding retract of
  a complete premetric space is complete.  Successful limits are constructed
  in the ambient space and retracted; no real order is present in this proof.
- Added closed half-line subspaces and their max/min retractions from the real
  line.  Both half-lines are complete, as is every nonempty closed interval
  via its general lattice clamp retraction.
- Added one-sided interval clamps between half-lines and closed intervals,
  plus the lower-open half-line and left-open/right-closed interval domains
  needed by strict-endpoint constructions.
- Moved closed absolute-radius predicates and inherited premetric spaces from
  `Series.PowerSeries.Uniform` to `Analysis.Metric.Radius`.  The strict radius
  is the preimage of an open half-line under non-expanding absolute value, so
  its openness follows from the generic continuous-preimage theorem.
- Proved the general equivalence between an absolute-value bound and the two
  symmetric interval bounds.  A symmetric interval clamp is consequently a
  non-expanding retraction onto every nonnegative closed absolute radius, and
  those radius spaces are complete.
- Reimplemented closed-radius interior derivative recovery entirely through
  the open-neighbourhood theorem.  This deletes the bespoke absolute-value
  triangle/gap calculation while keeping both existing theorem statements
  and their power-series consumers unchanged.
- Added continuous pasting at a point from continuous maps on the two closed
  half-lines.  Addition, subtraction of the common endpoint, and the min/max
  retractions provide the continuous map; the algebraic pasting theorem gives
  exact agreement on each side.
- Ported both legacy one-sided consumers in stronger quantitative form:
  `pasteAboveClosedC` pastes a closed interval to a closed right half-line,
  and `pasteAboveC` pastes a left-open/right-closed interval to that
  half-line on a strict lower domain.  Each result is packaged as a
  continuous map and has checked left/right restriction laws.

#### Revised decisions and proof engineering

- The recorded plan originally proposed proving interval completeness from
  closedness of order under limits.  The retraction argument is shorter,
  strictly more general, and automatically covers half-lines and absolute
  radii, so it supersedes that real-specific route.  Closedness-under-limits
  remains useful for predicates that do not admit explicit retractions.
- Strict-lower pasting cannot be reduced to closed-lower pasting without
  manufacturing a value at the excluded endpoint.  Making `(b,junction]` an
  explicit premetric subspace lets min and max supply the two continuous
  pieces directly on `(b,∞)` and preserves the correct domain boundary.
- The dual strict lattice lemma `minStrictLower` belongs with real
  locatedness, not in pasting.  It is now reusable anywhere two strict lower
  bounds must be combined through minimum.
- Absolute-radius geometry no longer enters power-series dependencies by
  definition.  `PowerSeries.Uniform` publicly imports the metric module for
  compatibility, while new metric and derivative code can depend on the
  radius domain without importing series theory.

Validation on 2026-08-01:

- all 131 Agda modules below `Cubical/HITs/CauchyRealsP/` and the root
  `Cubical.HITs.CauchyRealsP` facade returned exit code 0 from individual
  direct `agda-codex` checks;
- the six affected generic premetric modules/facades and the legacy
  `CauchyReals.Foundation`, `CauchyReals.Algebra`, and
  `CauchyReals.Sequence` facades also returned exit code 0;
- all 141 direct checks completed in 282 seconds, with no holes, unsolved
  metas, unsolved constraints, warnings, failures, or elaboration stalls.

### Next concrete goals

1. Survey the legacy connectedness, intermediate-value, extremum, and
   mean-value modules against the new interval and pasting foundations.
   Record the smallest constructive connectedness or interval-splitting
   theorem that unlocks an actual downstream calculus result.
2. Develop total boundedness for nonempty closed intervals independently of
   completeness.  Only after both ingredients and the intended topology
   interface are checked should a compactness theorem be packaged.
3. Use continuous pasting in a concrete interval-calculus consumer before
   generalising it to arbitrary finite covers or a topology-level pasting
   record.
4. Add unions and relative openness to the generic neighbourhood layer only
   when the connectedness proof fixes the required representation and
   universe behaviour.
5. Add a local-coordinate-richness hypothesis only if a concrete consumer
   needs uniqueness of derivative functions on a restricted domain; do not
   strengthen the general along-coordinate predicate.
6. Revisit polynomial-rational normal forms, the apartness-field package,
   and the first transcendental function according to the requirements of
   the selected interval-calculus consumer.

## Open design questions

1. Should coherent elimination from truncated local bounds be factored into a
   general library theorem after the multiplication and reciprocal use cases
   reveal the right interface?
2. When is an explicit equivalence between old `CauchyReals.ℝ` and
   `CauchyRealsP.ℝ` worth its dependency and compile-time cost?
3. Which old analysis modules should be ported, and which should instead be
   replaced by general theorems about complete premetric spaces?
4. How much compatibility re-exporting is useful before it starts obscuring
   the new architecture?
5. Should the apartness-field abstraction live in `Cubical.Algebra`, or first
   remain local until another constructive instance demonstrates that its
   interface is genuinely reusable?

## Validation policy

Every changed Agda module is checked directly with `agda-codex`.  At milestone
boundaries, every module in `CauchyRealsP` is checked directly, followed by
representative unaffected modules from `CauchyReals` and
`Relation.Premetric`.  Occasional cold-cache checks will be used separately
when dependency or performance behaviour needs validation.  Compile-time
regressions and any intentionally deferred holes are recorded here rather than
silently accepted.

Documentation updates are part of each milestone: completed items, changed
decisions, failed approaches worth remembering, and the next concrete goals
must remain visible in this file.
