# Uniformly continuous path groupoid

Import `Cubical.HITs.CauchyReals.Analysis.PathGroupoid` and open
`FundamentalGroupoid X`, where `X : PremetricSpace ℓ ℓ'`.
This includes complete premetric spaces; the construction actually needs
no completeness assumption and no algebraic structure on `X`.

The objects of `pathGroupoid` are exactly `fst X`. Its arrows `PathClass x y`
are uniformly continuous real interval paths from `x` to `y`, modulo
endpoint-fixed homotopy. `pathGroupoid-invertible` proves that every arrow
is an isomorphism, with `inverseClass` as its inverse.

## Paths and homotopies

- `Interval` is the closed Cauchy-real interval `[0,1]` with its subspace
  premetric; `𝕀` is its carrier and `𝟘`, `𝟙` its endpoints.
- `UCPath x y` contains a map `UC[ Interval , X ]` and its endpoint equations.
  `at p t` evaluates it.
- `PathHomotopy p q` contains a jointly uniformly continuous map
  `Interval × Interval → X`, whose first coordinate is homotopy time.
  The path endpoints stay fixed throughout the homotopy.
- `Homotopic p q` is the propositional truncation of `PathHomotopy p q`.
- `class≡≃homotopic p q` proves that equality of their quotient classes is
  equivalent to `Homotopic p q`.

Uniform continuity uses the repository's `UC` notion: the existence of a
modulus is propositionally truncated. The construction does not choose
moduli globally.

## Concatenation by overlapping constant intervals

`concatPath p q` traverses `p` on `[0,1/3]`, waits at their common endpoint
on `[1/3,2/3]`, and traverses `q` on `[2/3,1]`. Its two formulas are

```
p (clip (3 t))       on t < 2/3
q (clip (3 t - 2))   on 1/3 < t
```

They agree throughout the open overlap. `Stitching.agda` uses
`Stiching.hLev2` from `Analysis.Sequence.Base` to paste them and proves
uniform continuity, also for families with an extra premetric parameter.
The strict overlapping cover avoids deciding the order of arbitrary reals.
`concat-waiting` proves the value on the whole closed waiting interval.

## Laws

`concat-unit-left`, `concat-unit-right`, `concat-inverse-left`,
`concat-inverse-right`, and `concat-assoc` are explicit endpoint-fixed
uniform homotopies. `concat-homotopy` and `reverse-homotopy` show that the
operations respect homotopy; `homotopy-trans` pastes homotopies in time.

The law proofs interpolate real clocks in `[0,1]`, never points of `X`.
For associativity, the traversal `p * (q * r)` is subdivided at `1/2` and
`5/6`, inside its waiting intervals. Its three restrictions are
reparametrizations of `p`, `q`, and `r`. Both parenthesizations then factor
through this one traversal, and their clocks can be interpolated.

The set quotient turns these homotopies into the category laws.
Identities are constant paths and inverses reverse real time.

`Loops X x` exports `Loop`, `LoopClass`, and `loopGroup`, the automorphism
group at `x`. For the circle at `injCircle 0`,
`Cubical.HITs.CauchyReals.Circle.FundamentalGroup` proves this group is
isomorphic to the earlier circle-map homotopy group, preserving winding.

## Files and checking

`Base` defines paths and homotopies; `Real` and `Interval` provide the
parameter maps; `Stitching` and `Pasting` implement the construction;
`Composition`, `Factorization`, `Subdivision`, and `Associativity` prove
the operations and laws; `Quotient` packages the groupoid.
`Extensionality` provides a separate rational-density equality principle.

Run:

```sh
agda-codex Cubical/HITs/CauchyReals/Analysis/PathGroupoid.agda
```

The modules use the project's `--safe --cubical` configuration, with no
postulates, holes, choice axioms, or weakened compiler options.
