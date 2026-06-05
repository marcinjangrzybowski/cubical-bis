# CommRingSolver Architecture

This folder implements reflection-based tactics for commutative rings and
ordered commutative rings. The public surface is intended to be the macros; the
other modules are implementation details used to parse goals, build reflected
syntax, normalize expressions, and turn successful normalization into Agda
proofs.

## Main Modules

`AlgebraExpression.agda`

Defines the reflected expression language used by the solver. A goal term is
translated into this expression syntax before normalization.

`Config.agda`

Defines `CommRingSolverConfig`. A configuration specifies the scalar ring, the
target commutative algebra, the scalar homomorphism, optional scalar decision
procedures, cancellation data, reflection matching, and a guard deciding which
unmatched Agda terms may become polynomial variables.

`Polynomial/Core.agda`

Defines the polynomial representation, monomial and polynomial evaluation,
polynomial multiplication, coefficient cleanup, common-denominator support, and
the bridge from Horner forms to polynomials.

`Solver/Core.agda`

Contains the non-reflection equality solver in module `SansReflection`. It maps
reflected ring expressions to normalized Horner forms, proves that normalization
preserves evaluation, compares normalized forms, and exposes proof-producing
functions used by the macros.

`Reflection.agda`

Contains the equality macros. It reads the Agda goal, reflects the left and
right sides into solver expressions, builds the call to `SansReflection`, and
unifies the current goal hole with the proof term returned by the solver.

`OrderedConfig.agda`

Extends `CommRingSolverConfig` with order relations, order decision procedures,
preservation/reflection of scalar order, optional inverse data, zero matching,
and an inequality matcher.

`OrderedSolver/Core.agda`

Contains the non-reflection ordered solver in module `SansReflectionOrdered`. It
propagates sign information through reflected expressions and polynomials, uses
context assumptions where available, and proves goals of the form `x < y` or
`x <= y` by reducing them to sign information about `y - x`.

`OrderedReflection.agda`

Contains the ordered macros. It recognizes inequality goals, reflects the goal
and explicit assumptions, collects usable inequalities from the context, builds
the ordered solver call, and unifies the goal with the returned proof.

`Specialised/*.agda`

Builds concrete configurations and matchers for common scalar domains such as
fast integers, rationals, and reals.

## Equality Solver Pipeline

The equality solver proves goals in a commutative ring or commutative algebra.
The high-level pipeline is:

1. The macro inspects the goal type and extracts the two endpoints of an
   equality path.
2. Reflection translates both endpoints from Agda syntax into `RExpr n`, where
   `n` is the number of reflected variables.
3. Each expression is normalized to an `IteratedHornerForms n` value.
4. The solver proves that evaluating the normal form is equal to evaluating the
   original expression.
5. The normal forms are compared. When scalar equality is decidable, coefficient
   equalities can be discharged by computation.
6. The solver composes the normalization proofs and the normal-form equality
   proof into a proof of the original goal.
7. The macro unifies the current hole with that proof term.

The key invariant is that normalization is not trusted as an external
procedure. The Agda code proves a soundness theorem for the normalization
function, so the final proof is an ordinary Agda term.

## Reflection And Variables

Reflection is controlled by a `RingReflectionMatcher`.

The matcher recognizes ring operations, scalar literals, and domain-specific
syntax. When a term is not recognized as a ring operation or scalar, the
`polyVarGuard` decides whether it may be treated as a polynomial variable. If
allowed, the term is inserted into the variable list and represented by a
variable expression. If not, it is treated as a constant expression.

This split lets the same solver core work with different syntactic frontends:
generic commutative rings, fast integers, rationals, and lifted real syntax all
provide their own matching layer while reusing the same normalization and proof
machinery.

## Normal Forms

The equality solver uses Horner forms as its primary normal form. Horner forms
give a canonical, variable-ordered representation that is convenient for
normalization and comparison.

The polynomial layer is used when a more explicit polynomial representation is
needed. It supports:

1. evaluating polynomial terms and polynomials;
2. multiplying monomials and polynomial terms;
3. factoring out monomials;
4. normalizing coefficients;
5. common-denominator operations;
6. translating normalized Horner forms to polynomials.

This is used by advanced operations such as `normalize!`, `solveFor!`,
`eliminate!`, and the ordered solver.

## Equality Macros

The main equality macros are defined in `Reflection.agda`:

`solve!`

Proves a ring equality by reflecting both sides and comparing their normal
forms.

`normalize!`

Replaces a ring expression by its computed normal form, together with a proof
that the normal form evaluates to the original expression.

`solveFor!`

Uses an existing equality to isolate a selected variable when the solver can
recognize an isolated power of that variable.

`eliminate!`

Uses two equalities to eliminate a selected variable and produce a derived
equality.

## Ordered Solver Pipeline

The ordered solver proves inequalities by reducing them to sign information.
For a goal `lhs <= rhs` or `lhs < rhs`, it works with the difference
`rhs - lhs`.

The high-level pipeline is:

1. The macro recognizes the goal as a strict or non-strict inequality.
2. The two sides are reflected into ring expressions.
3. Explicit assumptions and usable inequalities from the context are reflected.
4. The solver rewrites the goal to a statement about `0 <= rhs - lhs` or
   `0 < rhs - lhs`.
5. The difference is normalized and converted to a polynomial.
6. Sign information is propagated through variables, monomials, polynomial
   terms, sums, products, and powers.
7. If assumptions can eliminate variables, they are folded into the problem
   before the final sign check.
8. The resulting sign proof is transported back to the original inequality.

The ordered core tracks sign facts with `IneqInfo`:

`noInfo`

No usable sign information is known.

`isPositive`

The value is strictly positive.

`isNonNeg`

The value is non-negative.

`isNonZero`

The value is known to be non-zero, but its sign may not be known.

`isZero`

The value is zero.

The solver combines these facts through ring operations. For example, the square
of any value is non-negative, the product of two positive values is positive,
and adding a positive value to a non-negative value is positive.

## Ordered Macros

The generic ordered macros are defined inside `OrderedReflection.agda` and then
specialized for concrete ordered rings:

`<≤!`

Proves the current inequality without explicit assumptions.

`<≤![ assumptions ]`

Proves the current inequality using explicitly supplied assumptions.

`prev-<≤!`

Shows the reflected problem instead of solving it. This is mainly useful while
debugging the reflection layer.

The exported concrete names use the domain suffixes from the specialization
modules, for example `<≤ℚ!`, `<≤ℚ![_]`, `<≤ℤ!`, and `<≤ℤ![_]`.

## Failure Modes

The solver can fail for several structural reasons:

1. reflection cannot recognize the goal shape;
2. a required scalar equality is not decidable in the current configuration;
3. a term is rejected by `polyVarGuard`;
4. an ordered goal is too strong for the available sign information;
5. no assumption can eliminate a variable needed by the ordered solver;
6. a `solveFor!` or `eliminate!` request does not have the isolated-power shape
   expected by the implementation.

When this happens, the macros report the reflected variables, the reflected
goal, or a `FailReason` where possible.

## Design Summary

The solver is split into two layers.

The non-reflection layer is ordinary Agda code. It defines syntax, evaluation,
normalization, polynomial operations, sign inference, and soundness proofs.

The reflection layer is thin but domain-specific. It translates Agda terms into
the internal syntax, calls the non-reflection solver, and asks Agda to unify the
resulting proof with the user goal.

This separation is what makes the core reusable across generic rings,
rationals, integers, ordered rings, and reals: only the configuration and
reflection matcher need to change.
