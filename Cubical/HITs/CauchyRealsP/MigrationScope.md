# Scope and character of the `CauchyRealsP` migration

This document describes what the parallel `CauchyRealsP` development has
actually migrated, which parts follow the mathematical content of the legacy
`CauchyReals` development, and which parts are inherently implemented in a
different way because the new reals are a direct instance of the generic
premetric completion.

The short conclusion is:

> `CauchyRealsP` is a migration of mathematical scope, not a copy of the old
> module hierarchy or public API.  Its foundation is genuinely shared with
> arbitrary premetric completions.  Algebra and analysis are then rebuilt over
> that foundation, retaining useful theorem statements and proof ideas from
> the old development while replacing real-specific completion machinery by
> generic quantitative constructions.

As of 2026-08-01, the new directory contains 131 checked Agda modules.  It has
no imports from `Cubical.HITs.CauchyReals`; the old development remains an
independent reference and source of mathematical guidance.

## Scope reached so far

### Foundation

The migrated foundation includes:

- the rational premetric space, using absolute rational difference;
- the real numbers as the completion of that space;
- rational inclusion and Cauchy-limit constructors;
- real closeness, reflexivity, symmetry, triangle, roundedness, and
  separatedness;
- sethood of the reals and injectivity of rational inclusion;
- completeness and rational approximation/density;
- quantitative extension and uniqueness into complete premetric spaces;
- non-expanding, Lipschitz, and continuous density/extensionality principles.

This is a complete foundational replacement for the custom real-specific HIT
layer needed by the currently migrated mathematics.

### Algebra and order

The migrated algebraic scope includes:

- addition, negation, subtraction, and the additive commutative group;
- minimum, maximum, non-strict order, strict order, and locatedness;
- compatibility of both orders with rational inclusion and additive
  operations;
- absolute value, triangle estimates, symmetric and general interval clamps,
  and the bridge between order bounds and premetric closeness;
- rational density, rational and natural bounds, Archimedean results, and
  apartness;
- bounded multiplication, total multiplication, and all commutative-ring
  laws;
- preservation of nonnegativity and positivity by multiplication;
- a constructive ordered-commutative-ring package;
- bounded positive reciprocal, positive reciprocal, signed inversion on
  inputs apart from zero, division, cancellation, and order laws for
  reciprocals and quotients;
- natural powers and their elementary order and absolute-value properties;
- increasing-degree coefficient lists with Horner evaluation, continuity,
  majorants, and bounded Lipschitz estimates.

The remaining algebraic packaging gap is an appropriate constructive
apartness-field interface.  The library's existing `Field` record asks for an
inverse from mere inequality with zero, which is stronger than the apartness
witness used here.

### Sequences, series, and elementary analytic infrastructure

The migrated analysis currently includes:

- Cauchy sequences and limits, with constructive completeness of real
  sequences;
- preservation of limits and Cauchy status by quantitative and continuous
  maps;
- eventual equality, sequence shifts, paired limits, products of limits, and
  order closedness under limits;
- finite sums and algebraic laws for partial sums;
- real series, summability, explicit Cauchy moduli, absolute convergence,
  comparison, finite modification, and selected rational bounds;
- geometric series, including rational contraction estimates and the
  reciprocal sum formula, scaling, shifts, and exact finite-prefix plus
  geometric-tail decompositions;
- finite convolution, Cauchy products, Mertens-type estimates, and absolute
  product closure;
- power series with bounded, eventually bounded, or arbitrary summable
  nonnegative coefficient majorants;
- convolution products of power series;
- iterated geometric convolution coefficients, simplex and binomial formulas,
  reciprocal powers, and polynomial coefficient bounds;
- uniform Cauchy series on arbitrary parameter types and continuity of their
  values over a premetric parameter space;
- uniform convergence and continuous evaluation of power series on closed
  absolute-value radii;
- termwise differentiation on an inner closed radius from convergence of the
  formal-derivative majorant at a possibly larger radius;
- zero-padded finite power series and exact agreement with Horner polynomial
  evaluation;
- eventually geometric coefficient sequences, including an explicit finite
  polynomial prefix followed by a geometric tail and its closed power-series
  value on the natural contraction domain `|r·x| < 1` (represented by a
  selected rational contraction bound);
- a rational-function interpretation of those polynomial/geometric values on
  the natural nonvanishing domain of `1-r·x`, together with its checked
  quotient derivative;
- ordinary derivatives at strict interior points when a uniformly summed
  closed-radius power series agrees with a supplied ambient function,
  including derivative-majorant convergence at a larger radius.

This layer is not just a minimal reproduction of an old sequence facade.  It
is a new quantitative series framework designed to support later
transcendental and complex analysis without selecting convergence data from
mere propositional existence.

### Metric neighbourhoods and intervals

The first migrated topology-facing layer now includes:

- a generic universe-polymorphic notion of an open predicate on any
  premetric space;
- full and empty open predicates, finite intersections, continuous preimages,
  and open premetric balls;
- strict and closed real half-lines and open intervals, with explicit
  positive-gap neighbourhood proofs;
- open, closed, and left-open/right-closed interval inherited premetric
  subspaces, including the unit interval;
- non-expanding, uniformly continuous, and continuous closed-interval
  inclusions;
- a non-expanding clamp retraction from `ℝ` onto every nonempty closed
  interval;
- non-expanding max/min retractions onto closed half-lines and one-sided
  clamps between half-lines and closed intervals;
- completeness of closed half-lines, nonempty closed intervals, and
  nonnegative closed absolute-radius domains;
- canonical global extension of interval maps by clamping, preserving
  non-expansion, uniform continuity, and continuity;
- closed and strict absolute-radius domains as metric objects, with openness
  of the strict radius obtained by continuous preimage under absolute value;
- algebraic and continuous pasting across a junction, with exact agreement on
  both sides, plus closed-lower and strict-lower one-sided continuous
  consumers.

This is intentionally a neighbourhood and interval foundation, not yet a
complete topology or compactness development.  In particular, arbitrary
unions, connectedness, total boundedness, compactness, and the corresponding
intermediate/extremum principles remain separate next steps.

### Differentiation

The migrated calculus currently includes:

- a division-free first-order remainder definition of a derivative;
- derivatives along a real-valued coordinate on an arbitrary premetric
  parameter space;
- ordinary real-function and pointwise specialisations;
- a continuous divided-difference criterion;
- a local linear estimate and continuity of every differentiable real
  function, generalised to derivatives along continuous real coordinates;
- derivatives of constants, the identity, natural powers, and finite Horner
  polynomials;
- closure under addition, negation, subtraction, rational scaling, real
  scaling with an explicit rational bound, and products;
- a chain rule over arbitrary premetric sources with continuous real
  coordinates, including finite Horner polynomial composition;
- uniqueness of ordinary derivative values and derivative functions,
  proposition-valuedness of derivative structures, and uniqueness of the
  structural Horner derivative;
- formal coefficient differentiation of power series;
- exact agreement between the formal derivative of a zero-padded finite
  coefficient list, its finite Horner derivative, and the corresponding
  uniformly summed power series;
- uniform divided-difference series and analytic termwise differentiation on
  a closed radius;
- the explicit derivative of every iterated-geometric reciprocal-power
  family;
- recovery of an ordinary pointwise derivative from relative differentiation
  on a closed radius at a strict interior point;
- differentiation of reciprocal on each fixed positive-rational-lower-bound
  subspace, and on the positive, negative, and signed-apartness real
  subspaces;
- a chain rule through arbitrary intermediate premetric spaces carrying a
  real coordinate;
- quotients by arbitrary differentiated denominators equipped pointwise with
  constructive apartness from zero;
- polynomial rational functions, uniqueness of their canonical derivatives,
  and the premise-free example `x ↦ x / (1 + x²)`;
- inherited natural nonvanishing domains for denominators with roots,
  restriction of ordinary derivatives to those domains, and the conventional
  quotient-rule derivative `(f'g - fg') / g²`;
- shifted reciprocal and two-pole rational-function examples with explicit
  constructors from root-apartness witnesses;
- non-expanding maps between natural domains induced by apartness
  implications or exact denominator identities, including symmetry of the
  two-pole factorization;
- common nonvanishing domains for pairs of rational functions and derivative
  closure under addition and multiplication on those domains;
- nested natural domains and a chain-rule derivative for composition of
  rational functions, validated by a double-reciprocal simplification;
- single product-denominator normal forms for common-domain sums and products,
  with checked quotient derivatives and exact agreement of their values;
- recovery of an ordinary derivative from a relative closed-radius derivative
  whenever the relative function agrees with a genuine ambient extension;
- recovery of an ordinary derivative from a derivative on any subspace that
  contains an open neighbourhood of the point;
- closed-interval interior differentiation, including a canonical ambient
  function obtained from the clamp extension;
- closed-absolute-radius interior differentiation as an instance of the same
  open-neighbourhood theorem rather than a separate boundary-distance proof.

Mean-value results, integration, and algebra for maps between several
rational-function domains remain future work.  Arbitrary along-coordinate
derivatives are intentionally not claimed unique: a coordinate may be
locally constant.

## What has essentially been copied

“Copied” here means that the legacy formalisation determined the mathematical
content to retain.  It does not generally mean textual copying or reuse of old
implementation dependencies.

### Mathematical specification

The following core choices intentionally preserve the meaning of the old
reals:

- rationals embed densely into the real completion;
- every appropriate rationally indexed Cauchy approximation has a limit;
- two reals equal when they are close at every positive rational radius;
- rational arithmetic computes as the corresponding real arithmetic;
- the reals form a constructive ordered commutative ring;
- strict order and apartness contain positive quantitative separation data;
- inversion is available from apartness rather than from mere negated
  equality;
- limits, series, derivatives, and later transcendental functions are stated
  constructively, with explicit moduli where computation needs them.

### Theorem targets and proof ideas

Large families of results were retained because downstream mathematics needs
them: additive and multiplicative laws, rational preservation/reflection,
Archimedean bounds, absolute-value estimates, reciprocal cancellation,
sequence completeness, geometric sums, and first-order derivative error
bounds.

Many rational calculations also follow the same underlying ideas as the old
proofs.  Examples include showing that rational addition and lattice
operations are non-expanding, clamping multiplication or reciprocal to a
bounded region, and using a positive rational separation to represent strict
order.

The old development was particularly useful as a catalogue of which lemmas
are necessary for substantial real and complex mathematics.  That catalogue
continues to guide priorities even when the new proof has a completely
different dependency structure.

### Familiar mathematical boundary

The names `ℝ`, `rat`, `lim`, real arithmetic notation, absolute value, order,
and conventional sequence and series language are retained where they keep
formulas readable.  This is a mathematical familiarity layer, not a promise
that old identifiers or module imports will continue to work unchanged.

## What is inherently different

The central architectural differences are summarised below.

| Subject | Legacy `CauchyReals` | Migrated `CauchyRealsP` |
| --- | --- | --- |
| Carrier and closeness | A real-specific higher inductive type and its closeness relation are declared together in `Foundation.Base`. | `ℝ` is exactly `Completion ℚPremetricSpace`; its constructors and closeness relation come from `Relation.Premetric.Completion`. |
| Elimination | Custom records such as `Elimℝ`, `Elimℝ-Prop`, and binary variants are maintained specifically for reals. | Generic completion eliminators are specialised to the rational premetric space and re-exported at the boundary. |
| Closeness theory | Reflexivity, symmetry, sethood, triangle, roundedness, completeness, and related results are proved inside the real development. | These are generic completion theorems; the real module mostly gives specialised names. |
| Universal property | The old primary statement factors maps from Cauchy presentations into arbitrary sets. | The primary interface extends non-expanding or Lipschitz maps into complete premetric spaces and proves quantitative uniqueness. |
| Basic lifted operations | A real-specific `NonExpanding`/`NonExpanding₂` and expression-lifting infrastructure recursively handles real constructors. | Rational maps are lifted with `liftNonExpanding`, `liftLipschitzWith`, or `liftLipschitzBinaryWith` from the generic completion library. |
| Algebraic laws | Many laws use real-specific eliminators and computation rules for rational/limit cases. | Laws are normally proved from rational computation by generic quantitative density or continuous extensionality. |
| Multiplication | Total multiplication is assembled through a substantial real-specific hierarchy of expanding bounded regions and intersection/gluing machinery. | Rational multiplication is symmetrically clamped to a chosen bound, lifted as a globally Lipschitz binary map, proved exactly compatible as bounds grow, and glued using merely existing Archimedean bounds. |
| Reciprocal | The old development builds a restricted Lipschitz inverse and extends it through its local-domain infrastructure. | A rational lower-clamped reciprocal is lifted generically; exact compatibility between lower bounds then defines positive and signed reciprocal. |
| Non-strict order | Defined through a lifted maximum in both developments. | The maximum itself is now a generic binary completion lift, and most laws are transported by density rather than real-HIT recursion. |
| Strict order | A truncated rational sandwich witnesses separation between two reals. | A truncated positive rational gap witnesses `x + δ ≤ y`; this makes translation and additive reasoning structural. |
| Sequence language | Real-specific sequence and continuity modules carry much of the infrastructure. | Generic `PremetricTheory` definitions are reused; only real completeness and real-algebra consequences remain local. |
| Derivative domains | Functions are presented over powerset predicates, with separate local and uniform derivative predicates. | A derivative is relative to any premetric source and any real coordinate map; closed-radius and denominator-nonvanishing subspaces are ordinary instances, and an open neighbourhood contained in such a domain is enough to recover an ambient derivative. |
| Topology and intervals | Real-specific open predicates, interval predicates, and pasting constructions are intertwined with the legacy real metric and continuity layers. | Open predicates, balls, intersections, and continuous preimages are generic premetric constructions.  Real order supplies interval predicates; a lattice clamp gives the closed-interval retraction and canonical extension. |
| Power-series derivative | The legacy calculus is oriented around interval predicates and later specialised function developments. | Uniform convergence of a continuous divided-difference series proves termwise differentiation directly, without division at a zero increment. |
| Finite polynomials | Polynomial use is distributed through later developments. | Increasing-degree lists have a dedicated Horner evaluator, Horner divided difference, formal derivative, and exact finite-power-series interpretation. |
| Reciprocal calculus | Restricted-domain inverse rules are developed through the legacy local-domain infrastructure. | A fixed positive-bound theorem is glued first over positive reals, transported through negation over negative reals, and then glued by the local sign of an apart real.  Arbitrary denominators use either a globally apart map or their canonical inherited nonvanishing subspace; quotient derivatives are exposed in conventional `(f'g-fg')/g²` form. |
| Rational-domain calculus | Partial rational expressions are distributed through predicate-oriented local-domain machinery. | Natural denominator subspaces support coordinate-preserving transports, intersections for binary operations, nested domains for composition, and a forward map to product-denominator normal forms.  Domain evidence remains explicit and proposition-valued rather than being hidden in a totalized partial-map structure. |

## How the generic completion changes the proof strategy

The new foundational path is:

```text
rationals with |p - q| < ε
              │
              ▼
       ℚPremetricSpace
              │
              ▼
  Completion ℚPremetricSpace
              │
              ▼
              ℝ
```

The generic completion already owns the difficult recursion and coherence
associated with Cauchy limits.  A real operation therefore starts, whenever
possible, as a quantitative rational map:

```text
rational operation + Lipschitz estimate
              │
              ▼
     generic completion lift
              │
              ▼
 real operation + continuity estimate
              │
              ▼
 laws from rational density/extensionality
```

This applies directly to addition, negation, maximum, absolute value, bounded
multiplication, and bounded reciprocal.  It avoids duplicating a recursion
principle for every operation and makes the quantitative estimate part of the
construction rather than a later theorem.

Multiplication and reciprocal cannot be lifted globally from their unbounded
rational operations: they have no global fixed Lipschitz constant.  The new
implementation therefore separates two issues:

1. construct a globally Lipschitz clamped operation at each explicit bound;
2. prove exact agreement whenever two bounds both contain the arguments;
3. eliminate the merely existing local bound into the set of reals.

This bounded-lift-and-glue pattern is the main new real-specific construction.
It is built on the generic completion rather than being part of the completion
itself.

## General results extracted from the migration

When a proof did not depend on rational or real arithmetic, it was placed in
`Cubical.Relation.Premetric` rather than copied into `CauchyRealsP`.  The
current migration has added or exercised generic results for:

- reflecting closeness between included base points back to the base
  premetric;
- preservation of Cauchy sequences by non-expanding, uniformly continuous,
  and fixed-Lipschitz maps;
- eventual equality of sequences and preservation of Cauchy status and
  limits;
- shifts of Cauchy and convergent sequences;
- reflection of convergence from a finitely shifted sequence back to the
  original sequence;
- Cauchy and limit pairing in product premetric spaces;
- continuous pairing and projections used by multivariable real operations;
- open predicates, finite intersections, continuous preimages, and open
  balls on arbitrary premetric spaces;
- preservation of rationally indexed Cauchy approximations by non-expanding
  maps;
- completeness of every non-expanding retract of a complete premetric space.

These results now apply to every suitable premetric space.  Their presence is
one of the main benefits of performing a genuine migration rather than
creating a second self-contained real implementation.

## Scope not yet migrated

The legacy tree is substantially larger: it currently contains 307 Agda
modules, while `CauchyRealsP` contains 131.  The raw counts are not a direct
measure of mathematical coverage because the new foundation replaces many
real-specific modules with shared generic code, and the new series layer is
organised differently.  Nevertheless, several major areas are clearly still
absent:

- a full topology, connectedness, finite-cover pasting, and the richer
  endpoint-extension machinery beyond canonical clamp extension;
- integration and the fundamental theorem of calculus;
- mean-value results, richer local-domain equivalences, and the more advanced
  interval calculus;
- square roots, nth roots, exponential, logarithm, trigonometric functions,
  inverse trigonometric functions, and real exponentiation;
- circle and angle theory;
- complex numbers, complex completeness, complex series and calculus,
  exponential and trigonometric functions, polar form, and roots of unity;
- an explicit equivalence or compatibility layer between the old and new
  real types.

These omissions are deliberate staging, not claims that the corresponding
legacy results are obsolete.  The current work establishes a compact
foundation, ordered-ring and inverse theory, and enough quantitative series
and derivative machinery for those later subjects to be rebuilt without
reintroducing real-specific completion infrastructure.

## Practical interpretation

The migration should currently be viewed as follows:

- the foundational replacement is mature for the present consumers;
- the ordered-ring, apartness, inverse, sequence, and series layers form a
  substantial checked vertical slice;
- the power-series development is already more systematic and general in its
  use of explicit majorants and uniform convergence;
- differentiation has a reusable new foundation but not yet the breadth of
  the legacy calculus;
- metric neighbourhoods, closed-domain completeness, closed-interval
  extension, and one-junction continuous pasting are checked, while
  total boundedness, connectedness, compact-interval theory, and mean-value
  arguments remain future work;
- transcendental, geometric, and complex developments are still future
  migration milestones.

Detailed chronological decisions, failed approaches, checking performance,
and next implementation goals remain in `MigrationPlan.md`.  This document is
instead the stable conceptual account of what is being preserved and what is
being redesigned.
