# A standalone relational margin calculation

Start with `calculate` in
[Implementation/Calculation.agda](Implementation/Calculation.agda). It reads
keyed trade and collateral catalogs, selects recorded receipt cash, computes the
exact scenario requirement for each client, applies the minimum-transfer policy,
and returns a typed margin-call table. Its body shows these calculations as
`|>` chains. No margin-engine state machine or proof argument is needed to read
or run this calculation.

Inside `MarginCalculation sources`, the entry point is:

```agda
calculate : Valuation → Receipts.Ledger → (ClientId → ℚ) → ⟦ MarginCalls ⟧
```

The inputs are a supplied rational valuation, the ledger of already recorded
receipt IDs, and client MTAs. The operation is read-only: its result is the call
table. It does not mark new receipts as received. All catalog sizes are arbitrary
and finite; the scenario family is nonempty. There are no concrete portfolios,
stress calibrations, or external service connections here.

The separate [Properties/Calculation.agda](Properties/Calculation.agda) connects
the actual returned table to an indexed financial specification. Its contract
has two parts: the rows contain the specified amounts and identifiers, and
nonnegative actual payments meeting their requested amounts give a risk bound
for the resulting reference book. Calculating a call does not establish that it
has been paid.

## Read the calculation from top to bottom

The four local quantities in `calculate` are `claims`, `collateral`, `paid`, and
`required`. Each has a direct business meaning:

| Stage | Visible relation operations | Result |
| --- | --- | --- |
| Trade valuation | Source rows → `deriveᵣ` replacement claim → `groupSum` by client | Signed net claim for each scenario/client. |
| Collateral valuation | Source rows → `deriveᵣ` eligible value → `groupSum` by client | Eligible collateral for each scenario/client. |
| Recorded cash | Canonical receipt rows → `selectᵣ` seen IDs → `groupSum` by client | Cash already received and recorded. |
| Scenario requirement | Finite scenario rows → `deriveᵣ` positive shortfall → maximum fold | Exact additional requirement for each client. |
| Output | Client rows → derive requirement → derive request → `projectᵣ` | One `MarginCalls` row per client. |

For example, this is the trade branch directly from `calculate`:

```agda
Trades.tradeRows
|> deriveᵣ "replacementClaim" (λ row →
     get "notional" row ℚ.· unitClaim valuation (get "instrumentId" row) scenario)
|> Sum.groupSum (get "clientId") (get "replacementClaim")
```

`deriveᵣ` adds a named field to each row. `get` reads that field directly, and
`groupSum` aggregates only rows matching the client key. The calculation nets
signed trade values within each client before taking a positive shortfall.
Other client keys never contribute to that client's exposure.

For a client `j`, let `X(s,j)` be its summed trade claim in scenario `s`,
`C(s,j)` its summed eligible collateral, and `P(j)` its recorded receipt cash.
The scenario fold computes

```text
u(j) = max over supplied scenarios s of max(X(s,j) − C(s,j) − P(j), 0).
```

The code calls the maximum fold `Maximum.sumBy`: `Maximum` instantiates the
generic fold with rational `max` and initial value zero. Each scenario gap is
already nonnegative. The amount `u(j)` is incremental: collateral and existing
cash have each been deducted once.

The final relation chain, also directly from the implementation, is:

```agda
tabulateᵣ {schema = Fields.fields ClientKeys} (λ client → client ,, [])
|> deriveᵣ "incrementalUpper" (λ row → required (get "clientId" row))
|> deriveᵣ "requestedCash" (λ row →
     Policy.transferAmount (get "incrementalUpper" row) (mta (get "clientId" row)))
|> projectᵣ {target = Fields.fields MarginCalls} (λ row →
     get "clientId" row ,, clientReference sources (get "clientId" row) ,, snapshotId valuation ,,
     get "incrementalUpper" row ,, mta (get "clientId" row) ,, get "requestedCash" row ,, [])
```

For nonnegative MTA `m(j)`, `requestedCash` is zero when `u(j) ≤ m(j)` and is the
whole `u(j)` otherwise. Equality is in the zero-request branch. Despite the
column name `incrementalUpper`, the standalone calculation computes the exact
requirement for these supplied data. It does not add the broader engine's
conservative revaluation reserve.

The output retains internal client key, external client reference, snapshot
label, incremental requirement, MTA, and requested cash. It includes every
client key, including clients with no contributing source rows.

## What the separate proofs establish

In `Calculation sources`, `calculate-refines-model` identifies the complete
`Code.calculate valuation seen mta` relation with `modelRows`: all six columns,
row order, and multiplicity agree. `modelRows` uses the exact initial report
and current V06 quote on the decoded relational state. The theorem concerns
the actual calculation result.

`EveryRow` is a conjunction over the actual relation list.
`calculate-certified` supplies `EveryRow (RowCertified valuation seen mta)` for
the returned rows: the specified client/reference/snapshot fields, exact
incremental requirement, nonnegative amounts, and request policy. Its
`upper-exact` field relates the returned amount to the independent
`referenceBook`; `request-exact` identifies the current V06 quote. Metadata
equality means the supplied labels are retained; it does not establish their
external authenticity or freshness.

`fulfilling-calculation` assumes nonnegative MTAs and **additional** actual
payments beyond the cash already represented by `seen`. Its `MeetsRequests`
premise is

```text
EveryRow (λ row → get "requestedCash" row ≤ paid (get "clientId" row))
         (Code.calculate valuation seen mta).
```

It yields `Tolerance.Guarantee` for the independent reference book after those
payments. In every supplied scenario, each client's positive unsecured amount
is at most its MTA, and both aggregate exposure and every severity-weighted
closeout loss are at most the sum of MTAs. Severity entries lie in `[0,1]`.
At zero MTA these nonnegative residuals vanish. No default-probability model is
required or inferred.

This is a conditional payment theorem. The standalone function emits requests;
payment provenance and availability remain inputs. The payment vector is not
deduplicated by this theorem. Delivery-based callers can use `deltaBalances`
and its accounting proofs to obtain new cash amounts; the closing balance or
old seen receipts must not be credited again. The lower accounting proofs
in [Properties/Valuation.agda](Properties/Valuation.agda) and
[Properties/Receipts.agda](Properties/Receipts.agda) establish that relation
grouping and receipt selection equal direct sums over source keys.

## Implementation and properties are separate

```text
Pipeline/
  Implementation.agda             qualified runtime umbrella
  Implementation/
    Sources.agda                  catalogs, valuation interface, schemas
    Valuation.agda                trade/collateral relation chains
    Receipts.agda                 receipt selection and grouping
    Margin.agda                   optional quote/receipt processing engine
    Calculation.agda              standalone calculate entry point
  Properties.agda                 qualified proof umbrella
  Properties/
    FiniteRisk.agda                finite numeric fold bounds
    Valuation.agda                 indexed accounting and market paths
    Receipts.agda                  journal accounting and replay proofs
    Correctness.agda               engine status and amount certificates
    Refinement.agda                complete engine output refinement
    Stability.agda                 engine replay and unchanged-market laws
    Calculation.agda              actual returned-table certification
```

[Implementation.agda](Implementation.agda) exposes runtime modules;
[Properties.agda](Properties.agda) exposes their proofs. Runtime relation
expressions use `get`, `deriveᵣ`, `selectᵣ`, `groupSum`, and `|>` directly.
Receipt delivery processing additionally uses `keyMask`. There are no field
accessor wrappers to trace before understanding these expressions.

The generic [Operations](../../../../../../Experiments/Relation/Operations.agda)
and [Aggregation](../../../../../../Experiments/Relation/Aggregation.agda)
operate on lists, preserving order and multiplicity. Canonical tabulation visits
each internal key once; deriving fields and projecting rows preserve row count.
Total functional valuation lookup introduces no join multiplication. This is a
specified relation program, not a SQL optimizer or database transaction engine.

## Source assumptions

The financial interpretation depends on these supplied conditions:

- **Complete, distinct records:** keys enumerate the selected live trades,
  available custody lots, and actual receipts without duplicating physical
  items under different keys. Canonical tabulation alone does not validate
  ingestion or trade lifecycle selection.
- **Authorized netting:** a `ClientId` represents one permissible netting set,
  or a client whose selected trades all belong to one such set. There is no
  additional agreement key separating a counterparty's legal netting sets.
- **Sufficient pricing keys:** `InstrumentId` determines all terms needed by the
  supplied per-notional value. Product and settlement-date fields are metadata.
  Signed notional scaling must match the source valuation convention.
- **Available collateral:** lot units are nonnegative, distinct lots denote
  disjoint available allocations, and eligible unit values include conversion,
  haircut, and eligibility in one common currency. These values are shared by
  asset across clients; client-specific eligibility needs a suitable input
  scheme. Receipt cash is excluded from the lot catalog.
- **Recorded cash at par:** seen receipt keys identify actual, available,
  eligible cash at par in the common account currency across scenarios. Each
  immutable key fixes owner and amount. External strings do not authenticate
  receipts or define replay identity.
- **Stable identifiers and snapshots:** external references and snapshot labels
  are metadata, without uniqueness, freshness, or chronology checks. Internal
  IDs are `Fin n` aliases, so equal cardinalities can make different namespaces
  the same Agda type. Correct mappings are an adapter responsibility.
- **Valid valuation inputs:** rational prices are embedded exactly as supplied
  into Cauchy reals. Pricing accuracy, rounding bounds, scenario adequacy, and
  provenance are external. The catalogs remain fixed within this calculation.

No regulatory compliance, enforceability, physical inventory-capacity proof,
settlement-principal protection, currency-specific funding, or production
throughput follows. The [references](../REFERENCES.md#relational-pipeline)
explain the literature motivations and their limits.

## Optional: the broader processing engine

[Implementation/Margin.agda](Implementation/Margin.agda) retains `process` for
revaluation, actual receipt deliveries, updated amounts, and a status tag. Its
`Output.calls` is the assessed pre-receipt quote; `next-amounts` is the remaining
bound afterward. Unlike the standalone exact calculation, a maintained report
plus a computed revaluation reserve can be conservative. An unmet quote then
does not prove economic undercollateralization.

[Correctness](Properties/Correctness.agda) separately certifies raw amount
vectors and the actual returned status under valid-bound and nonnegative-MTA
premises. [Refinement](Properties/Refinement.agda)'s `pipeline-correct` bundles
state/computed-report paths, remaining-vector and call-row equality, status
certification, and a conditional reference guarantee. These paths identify the
specified computations, not arbitrary conservative reports.

[Stability](Properties/Stability.agda) proves receipt replay and two-batch
commutation at a fixed target valuation, including paths of state and risk
guarantee. It does not commute different market updates. This engine remains
available without being a prerequisite for reading `calculate`.

## Checking

From the repository root:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Broker2/Pipeline/Implementation/Calculation.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Broker2/Pipeline/Properties/Calculation.agda
```

The separate umbrellas check the complete runtime or proof collection when
needed. [PROGRESS.md](PROGRESS.md) records compiler results and source hashes.
These commands are not a performance benchmark or source-ingestion test. The
[five-minute presentation extension](../PRESENTATION.md#pipeline-extension)
starts with the calculation and then reads its certificate.
