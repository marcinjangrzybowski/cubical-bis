# Uniform homotopy classes of circle maps

Import `Cubical.HITs.CauchyReals.Circle.Homotopy`.

Winding number gives a constructive **abelian group isomorphism** between
uniform homotopy classes of uniformly continuous circle maps and the
integers:

```agda
circleHomotopy≅ℤ : AbGroupIso CircleHomotopyAbGroup IntegerAbGroup
ℤ≅circleHomotopy : AbGroupIso IntegerAbGroup CircleHomotopyAbGroup
circleHomotopy≃ℤ : CircleHomotopyClasses ≃ ℤ
circleHomotopyAbGroupEquiv :
  AbGroupEquiv CircleHomotopyAbGroup IntegerAbGroup
```

These are unconditional theorems in `Equivalence.agda`. The forward map
is `classWinding`; the inverse is `integerClass`, which sends an integer
to the class of the corresponding pointwise power of the identity map.
Both inverse equations are proved by `winding-integerClass` and
`integerClass-winding`.

For individual maps, the classification and its normal form are:

```agda
winding-classifies : (f g : CircleMap) →
  Homotopic f g ≃ (windingNumber f ≡ windingNumber g)

winding-normal-form : (f : CircleMap) →
  Homotopic f (integerMap (windingNumber f))
```

## Maps, homotopies, and group operation

`CircleMap` is `UC[ CirclePremetricSpace , CirclePremetricSpace ]`.
A `UniformHomotopy f g` consists of a jointly uniformly continuous map

```text
H : ℝ × Circle → Circle
H(0, x) = f(x),   H(1, x) = g(x).
```

The real parameter matters: `Circle` is the set quotient ℝ/ℤ, so paths in
Agda's interval alone do not express the intended topological homotopies.
Using all of ℝ allows constant extension outside [0,1] by clamping.
This development uses uniform homotopies; it does not prove a comparison
with arbitrary merely continuous homotopies.

`Homotopic f g` is the propositional truncation of `UniformHomotopy f g`.
It is proved to be an equivalence relation. `CircleHomotopyClasses` is the
set quotient by this relation, defined independently of winding.
`class-effective` proves that equality of classes implies existence of
a uniform homotopy.

The operation is **pointwise circle addition**, or multiplication when
the circle is written as complex numbers of modulus one. Its neutral
element is the constant map at `injCircle 0`, and inverse is pointwise
circle inversion. This yields `CircleHomotopyAbGroup`. Composition of
circle maps is a different operation and is not the group operation here.

## Why winding is a complete invariant

`windingNumber-homotopy` proves invariance under uniform homotopies.
`windingNumber-add` proves additivity, giving `classWindingHom`.
Integer powers supply a section `integerClassHom`.

The analytic step is `nullWindingIsNull` in `NullHomotopy.agda`:

```agda
nullWindingIsNull :
  (f : CircleMap) → windingNumber f ≡ 0 → Homotopic f zeroCircleMap
```

Its construction proceeds through the following modules:

1. `LocalLift` gives a uniformly continuous inverse-angle chart near any
   circle point, with a covering equation and an angle bound of 1/4.
2. `IntervalLift` glues normalized lifts on adjacent intervals.
   `RealPaths` supplies clamped paths and extensionality from rational
   points, so gluing does not require deciding real order.
3. `FiniteLift` uses a finite dyadic subdivision supplied by uniform
   continuity. The endpoint of the resulting bounded real lift equals
   the sum defining winding. Winding zero therefore closes the lift.
4. `ClosedLift` extends the closed lift across the ends of [0,1], with
   a bound and the one-period identities needed on an overlapping chart.
5. `Overlap` descends through representatives in (0,3/2).
   `DomainAngle` provides a uniformly continuous small angular
   displacement between nearby circle points. `Descent` uses it to
   prove uniform continuity of the descended real function, including
   across the seam of the circle.
6. `NullHomotopy` writes the original map as a constant plus the
   exponential of this bounded real function. The contraction
   `lifted-null`, together with `constant-null`, gives the null-homotopy.

`Classification` contains the algebraic criterion
`classificationFromNullWinding`. Applying it to the constructed
`nullWindingIsNull` proves the full isomorphism in `Equivalence`.
The abstract criterion and the alternative sufficient condition
`classificationFromLogLift` remain available separately.

## Other contraction results

- `liftedHomotopy` and `lifted-null` contract maps with a supplied bounded,
  uniformly continuous real logarithm. The formula uses
  `injCircle (clamp 0 1 t · g x)`; joint uniform continuity is proved.
- `constant-null` contracts every constant circle map by quotient
  induction into a proposition.
- `strip-null` contracts maps whose image lies in the strip
  `x > 0, |y| ≤ 1/2` of the Cartesian unit circle.
- `close-homotopic` proves that two maps uniformly close within
  `circleAddModulus ([ 1 / 2 ]₊)` are uniformly homotopic.

## Constructive discipline and verification

Continuity moduli, interval lifts, and existence of homotopies are
propositionally truncated. Truncations are eliminated into propositions,
or into the already proved unique winding data. Local representatives
are used only under truncation; no simultaneous choice of representatives
or moduli is made. Rational order and locatedness suffice for the finite
subdivision and overlap arguments.

No excluded middle, real-order decision procedure, axiom of choice,
postulate, unsafe pragma, or weakened library option is added.

Check the complete development with:

```sh
agda-codex Cubical/HITs/CauchyReals/Circle/Homotopy.agda
```

The complete import checks with exit code 0, with no holes, unsolved
metas, or unsolved constraints.

## Comparison with based interval loops

`Cubical.HITs.CauchyReals.Circle.FundamentalGroup` proves
`circleLoop≅circleHomotopy`, a group isomorphism from the based loop group
of `injCircle 0` in the uniform path groupoid to this earlier group.
It preserves winding number and identifies the integer generators.
See [the comparison construction](../FundamentalGroup/README.md).
