# Construction-independent completion properties

This directory separates the data shared by completion constructions from
the map class whose universal property is being studied.

## Presentation and uniqueness

`Base` defines `CompletionPresentation`.  A presentation of a completion of
a premetric space `M` consists of:

1. a completed premetric space `C`;
2. an injection `ι : M → C`;
3. preservation and reflection of approximation along `ι`;
4. quantitative density of `ι`.

`Extensionality` derives the consequences that need only density and
separation.  In particular, continuous maps `C → N`, and hence
nonexpanding maps, are equal if they agree after `ι`.  No chosen limits or
extension operator are involved in these proofs.

The root `Completion.UniversalProperty` module is a facade exposing
`Extensionality`, `NonExpanding`, and `CompletionCentered` for one
presentation and target.

## Ordinary nonexpanding universal property

`NonExpanding` defines

```agda
HasNonExpandingUniversalProperty
```

to mean that each nonexpanding `M → N` has a nonexpanding extension
`C → N` along `ι`.  Density supplies uniqueness, so
`WithUniversalProperty` proves the precise mapping-space statement

```agda
NE[ M , N ] ≃ NE[ C , N ]
```

where the forward map is extension and the inverse is restriction along
`ι`.  It also proves the two inverse laws separately.  Both the extension
fiber and `HasNonExpandingUniversalProperty` are propositions.

For the Cauchy-sequence construction, the required target structure is the
recent radiuswise interface

```agda
HasCauchySequenceLimits =
  ∀ x → (∀ ε → ∥ CauchyTail x ε ∥₁) → limitSeq x
```

`Instances.CauchySequence.NonExpanding` initializes the generic property for
every target with this structure.  The direct theorem is also available as
`CauchySequence.Extension.UniversalProperty.nonExpandingExtensionEquiv`.

## Completion-centered continuity

`CompletionCentered` studies a larger, qualitative map class.  It defines a
condition on a base function `M → N` by testing its values around arbitrary
centers of `C`, without mentioning constructors or chosen representations of
limits.  Its universal property says that exactly these base maps admit a
continuous extension.

Given

```agda
universal : HasCompletionCenteredUniversalProperty
```

`WithUniversalProperty` supplies both the fiberwise equivalence

```agda
IsCompletionCenteredContinuous f ≃ ContinuousExtension f
```

and the global equivalence between completion-centered restrictions and
continuous maps out of `C`.

This is intentionally separate from the ordinary nonexpanding universal
property.  A nonexpanding extension theorem does not by itself construct
extensions for all completion-centered base maps.

For `CauchySequence`, `Instances.CauchySequence` exposes this part through
`CompletionCenteredProperty`, `ConcreteCompletionCentered`, and
`CompletionCenteredMappingSpace`.
