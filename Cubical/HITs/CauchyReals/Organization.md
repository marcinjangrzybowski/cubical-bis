# Cauchy-real module organization

The public API is organized around layered facades. Root-level Agda modules
are import entry points; mathematical implementations live in subject folders
below them.

## Choosing an import

Use the narrowest facade that covers the intended client code. The broad
facades are cumulative:

```text
Foundation
  └─ Algebra
       └─ Analysis
            └─ Calculus
                 └─ Transcendental
                      └─ Geometry
```

For example, a client can import `Cubical.HITs.CauchyReals.Analysis` without
having to know where continuity, sequences, or metric spaces are implemented.
The focused root facades provide smaller entry points:

- `Approximation`, `Metric`, `Lipschitz`, `Sequence`, and `Pasting`;
- `Derivative` and `Integration`;
- `NthRoot`, `Trigonometry`, and `Exponentiation`;
- `ArcSin` and `Circle`.

Exponentiation also has focused subfacades: `Exponentiation.Base`,
`Exponentiation.Approximation`, `Exponentiation.Series`,
`Exponentiation.RealPower`, `Exponentiation.Logarithm`,
`Exponentiation.Normalized.Exponential`, and `Exponentiation.ExpLog`.

The focused `Metric` facade exports the canonical `Relation.Premetric`-based
real, interval, product, compatibility, and mapping modules. The former
real-valued `MetricSpace`/`UContMap` compatibility hierarchy has been retired.
Generic clients can import `Cubical.Relation.Premetric` for structures and
mappings, and
`Cubical.Relation.Premetric.Instances` for structural constructors such as
subspaces, products, function spaces, and Archimedean-ring premetrics.

## Implementation tree

The main implementation areas are:

```text
CauchyReals/
├─ Foundation/
│  └─ Order/
├─ Algebra/
│  ├─ Expression/
│  ├─ Order/
│  └─ Power/
├─ Analysis/
│  ├─ Continuity/Uniform/
│  ├─ Lipschitz/Inverse/
│  ├─ Metric/Compatibility/
│  ├─ Order/
│  ├─ Pasting/
│  └─ Sequence/
├─ Calculus/
│  ├─ Derivative/
│  └─ Integration/Partition/
├─ Approximation/
├─ Transcendental/Roots/
├─ Trigonometry/
├─ Exponentiation/
│  ├─ Approximation/
│  ├─ RationalPower/
│  ├─ Logarithm/Sequence/
│  ├─ RealPower/
│  ├─ Normalized/Exponential/
│  ├─ ExpLog/
│  └─ Series/
├─ ArcSin/
└─ Circle/
```

This separates general real analysis from specialized transcendental
constructions. In particular, roots and trigonometry no longer appear as
unrelated files beside the foundational real-number implementation, and the
exponentiation sequence, normalization, and real-power layers have distinct
namespaces.

## Dependency rules

Implementation modules import concrete leaves, such as
`Analysis.Continuity.Base`, `Calculus.Integration.Properties`, or
`Exponentiation.Logarithm.Sequence.Limit`. They do not import a facade that
re-exports the module being implemented. This keeps the dependency graph
acyclic and keeps unrelated public declarations out of proof contexts.

Shared declarations belong at their lowest natural layer. For example,
natural-power algebra lives in `Algebra.Power`, while derivative rules for
powers live in `Calculus.Derivative.Power`.

`Base`, `Infrastructure`, `Construction`, and `Definition` denote successive
implementation layers. Names such as `Properties`, `Laws`, `Order`, `Bounds`,
and `Derivative` describe dependent results. Catchall names such as `More` are
not used.

The cumulative facades may hide implementation-only aliases when otherwise
independent leaves use the same local name. A facade should curate that
boundary; leaf modules should not be distorted merely to make a broad import
possible.

## Compatibility

The repository is updated to use the new paths directly. Removed flat,
misspelled, or catchall modules such as `Aproximations`, `IntegrationMore`, and
`ExponentiationMore` are intentionally not retained as compatibility shims.
