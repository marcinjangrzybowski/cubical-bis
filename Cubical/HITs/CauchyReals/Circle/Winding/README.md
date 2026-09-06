# Constructive winding numbers

Import `Cubical.HITs.CauchyReals.Circle.Winding`.

The main functions return integers:

```agda
windingNumber : UC[ CirclePremetricSpace , CirclePremetricSpace ] → ℤ
distCircleWinding : UC[ distCirclePremetricSpace , distCirclePremetricSpace ] → ℤ
```

`Circle` is the set quotient ℝ/ℤ. Its premetric is pulled back from the
Cartesian unit circle through `Circle≃distCircle`. Angles are measured in
turns, and the parametrization is `t ↦ (cos (2πt), sin (2πt))`.

`windingNumber-spec` and `distCircleWinding-spec` characterize the answer
as the sum of short angular increments on a sufficiently fine dyadic
subdivision of one traversal of the domain circle. `turns-unique` proves
that all admissible subdivision depths give exactly the same real sum.

The construction uses the open half-circle chart underlying
`PointedUnwind`. Each short increment lies strictly between −1/4 and 1/4.
For three pairwise close points, the difference between a direct
increment and the sum of two increments is an integer of absolute value
less than one, hence zero. This proves subdivision independence. For a
loop, effectiveness of the quotient supplies the integer represented by
the sum.

The library's `UC` type contains a propositionally truncated modulus.
The proof eliminates this truncation only into the proposition consisting
of an integer together with its winding specification. It does not select
a modulus or use a choice principle. All modules retain the library's
`--safe` options; no axioms, excluded middle, or decision procedure for
real order are added.

`windingLoop-lift` and `windingNumber-lift` identify the winding number with
the endpoint displacement of any supplied uniformly continuous real
lift. `Examples.agda` proves that the identity has winding number one and
every constant map has winding number zero.

The [uniform homotopy development](../Homotopy/README.md) additionally
proves homotopy invariance and additivity, constructs the group of
homotopy classes under pointwise circle addition, and proves that winding
is an abelian group isomorphism to ℤ. Its finite lifting and descent
construction proves that every zero-winding map is uniformly
null-homotopic. Thus two uniformly continuous circle maps are uniformly
homotopic exactly when their winding numbers agree.

Check with:

```sh
agda-codex Cubical/HITs/CauchyReals/Circle/Winding.agda
agda-codex Cubical/HITs/CauchyReals/Circle/Winding/Examples.agda
```
