# Winding over the sequential reals

Import `Cubical.Analysis.Circle`. The carrier is the set quotient of the
native `Cubical.Analysis.Real.Base.ℝ` by integer translations. It is an
abelian group with a separated premetric measured in turns; the projection
`cover : ℝ → Circle` is non-expanding.

The winding API follows `Cubical.HITs.CauchyReals.Circle.Winding.Loop`:

```agda
windingLoop : (f : UC[ ℝPremetricSpace , CirclePremetricSpace ]) →
  fst f (rat 0) ≡ fst f (rat 1) → ℤ

windingNumber : UC[ CirclePremetricSpace , CirclePremetricSpace ] → ℤ
```

`HasWinding` specifies the answer by the sum of short real increments on a
fine dyadic subdivision of `[0,1]`. `windingLoop-spec` establishes that
specification, `hasWinding-unique` proves uniqueness, and
`windingLoop-subdivision` identifies every admissible subdivision with the
same integer. `windingLoop-cong` gives extensionality and independence from
continuity and endpoint-equality witnesses.

`windingLoop-lift` identifies the result with the endpoint displacement of
any supplied uniformly continuous real lift, stated through its translation
law. `lift-step` obtains that law from a lift relative to a fixed base point.
The circle-map variants are `windingNumber-spec`, `windingNumber-lift`, and
`windingNumber-cong`.

`Winding.Examples` proves that one traversal and the identity circle map have
winding one, constant circle maps have winding zero, and the loop
`t ↦ cover ([ k / 1 ] ⋆ t)` has winding `k` for every integer, including
negative integers.

## Why this differs from the reference implementation

The reference obtains short angles from trigonometric charts of the Cartesian
unit circle and pulls its metric back to the quotient. Analysis instead
defines closeness by the mere existence of a small real displacement:

```text
p ≈ᶜ[ ε ] q  iff  ∥ Σ t, (t ∼[ ε ] 0ℝ) × (p +ᶜ cover t = q) ∥
```

Integer separation proves that a displacement smaller than a quarter turn
is unique. Truncation can therefore be eliminated into the full short-
displacement specification. Three such increments have total bound less
than one turn, proving exact local angle addition and hence subdivision
independence. Quotient effectiveness makes a closed-loop sum an integer.
The final integer-plus-specification pair is again a proposition, so the
construction can eliminate the truncated continuity modulus. It chooses no
global representatives or sequence of approximation witnesses.

This route uses only the native additive group and premetric, plus rational
dyadic arithmetic. It neither imports the HIT Cauchy reals nor assumes an
equivalence between the real implementations. No postulates, extra choice
hypotheses, real-order decisions, or new solver calls are used.

The quotient circle is **not yet identified with the Cartesian unit circle**
over Analysis. Native π and its trigonometric characterization are now
constructed in `Real/Series/PowerSeries/Trigonometric/Pi/Value.agda`; the
restricted inverses are constructed in `Pi/InverseValue.agda`. The
Cartesian-circle bridge remains separate work. Homotopy classification and
the fundamental-group isomorphism from the larger reference development are
also not asserted here.

## Checks

Verified on 2026-10-08: all twelve new Agda modules, the updated `Real`
facade, `Everything`, and `Cubical.Analysis` passed `agda-codex` with exit
code 0 and no holes, unsolved metas, constraints, or warnings. The three
large aggregate checks used `+RTS -c -RTS`, retaining the memory guard.
The source/import audit found no added postulates, choice assumptions,
unsafe options, or imports of another real-number implementation.

```sh
agda-codex Cubical/Analysis/Circle/Winding/Loop.agda
agda-codex Cubical/Analysis/Circle/Winding/Examples.agda
agda-codex Cubical/Analysis/Everything.agda
agda-codex Cubical/Analysis.agda
```
