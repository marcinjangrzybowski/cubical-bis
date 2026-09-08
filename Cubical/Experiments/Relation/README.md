# Typed relations and aggregation

[Base.agda](Base.agda) supplies schemas with distinct field names, typed rows,
list-valued relations, field operations, Cartesian products, and `mapᵣ`.

[Operations.agda](Operations.agda) adds named field access (`get "clientId"`),
canonical finite tabulation, one-row projection, Boolean selection, finite-key
membership masks (`keyMask`), and their composition laws. A field getter's
result type is selected from the schema; its implicit membership argument
requires that the field exists. Membership masks have append, projection,
replay, and reordering laws.
The forward application operator `|>` displays stages in data-flow order.
`deriveᵣ "value" compute` adds a computed column while retaining the input
fields; the schema requires that the new name is fresh. For example:

```agda
sourceRows
  |> deriveᵣ "value" compute
  |> selectᵣ eligible
  |> Totals.groupSum (get "clientId") (get "value")
```

This is ordinary composition of typed operations, with no additional query
interpreter. `sum-derive` and `sum-insert` expose the aggregation semantics of
derived and constant columns for downstream proofs.
[Aggregation.agda](Aggregation.agda) adds `Sum A zeroA _+A_`: weighted folds,
finite sums, grouping by a `Fin n` key, and dense key/total output rows. Empty
groups contribute `zeroA`. Selection and concatenation laws take the needed
identity and associativity proofs explicitly. Neither module imports financial
theory or fixes the accumulator to rationals or reals.

Relations retain list order and multiplicity. These operators do not silently
deduplicate data or quotient by permutation. In particular, `concatᵣ` is a
Cartesian product: an enrichment that must produce exactly one row per input
can use `projectᵣ` with a total keyed lookup. `sum-project`, `sum-select`,
`sum-tabulate`, and `group-tabulate` relate these computations to their folds.

The [Broker2 pipeline](../../HITs/CauchyReals/Example/Financial/Broker2/Pipeline/README.md)
uses rational sums to implement valuation and receipt accounting, then proves
agreement with a Cauchy-real margin model. The correctness boundary assumes
complete finite source catalogs with valid business identities; it does not
establish the semantics of an external SQL database or ingestion service.

```sh
agda-codex Cubical/Experiments/Relation/Operations.agda
agda-codex Cubical/Experiments/Relation/Aggregation.agda
```
