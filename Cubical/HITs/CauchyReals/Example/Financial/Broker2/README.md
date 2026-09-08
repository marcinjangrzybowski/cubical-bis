# One broker margin engine, evolved seven times

`Broker2` is a presentation development for quantitative developers: start with
one account, add business requirements, and keep proving what the same engine
does. The recurring interface is **`quoteCall`, `receive`, `receive-correct`**.
Every successor imports the preceding version and states its compatibility
contract explicitly.

Read the modules in order. Use [PRESENTATION.md](PRESENTATION.md) for a 28-minute
speaker guide, [REFERENCES.md](REFERENCES.md) for the financial and systems
motivation, and [PROGRESS.md](PROGRESS.md) for reviews and validation. The
[entry point](../Broker2.agda) checks all seven versions together.

## The evolution

| Version | Change to the engine | Result proved | Relationship to the preceding version |
| --- | --- | --- | --- |
| [V01 Account](V01Account.agda) | A signed claim, available cash, and an additional cash call. | A sufficient receipt covers the claim; the quote is the least such nonnegative receipt. | Baseline. Two successive receipts equal one combined receipt. |
| [V02 Clients](V02Clients.agda) | Lift the same state and operations to separate client netting sets. | Every client is covered; aggregate residual and all modeled severity-weighted losses are zero. | Projecting a client commutes with both operations: `quote-refines-V01`, `receive-refines-V01`. |
| [V03 Stress](V03Stress.agda) | A market profile and common received cash; one call must work across all supplied stresses. | The least nonnegative uniform call covers every client in every supplied scenario. | Receipt and scenario projection commute. A singleton market recovers V02's quote: `receive-refines-V02`, `singleton-quote-refines-V02`. |
| [V04 Rational](V04Rational.agda) | A rational report on the real quote, a decidable receipt gate, and an updated report after payment. | Passing the quoted plan proves coverage. Exact reports make the decision complete for coverage. Rational inputs compute exact initial reports. | Rational receipts embed into the V03 transition: `receive-refines-V03`. Reports bound the V03 quote; equality is an additional proved property. |
| [V05 Tolerance](V05Tolerance.agda) | Suppress calls at or below each client's minimum transfer amount. | Sufficient actual receipts leave residual at most MTA per client; aggregate residual and every severity-weighted loss are at most total MTA. | Receipt behavior is inherited; zero MTA gives exactly V04's quote: `zero-mta-refines-V04`. |
| [V06 Receipts](V06Receipts.agda) | Replace amount-only receipt input with a market and identified-event ledger. Return the next state, certified report, and assessment. | The same loss bounds hold using newly credited cash; replay and order preserve the resulting state. | `receive-refines-V05` identifies the projected transition with V05 receiving precisely the new cash. |
| [V07 Revaluation](V07Revaluation.agda) | Preserve the receipt ledger, change the market, refresh the report with a certified reserve, and run the same engine. | The final receipt operation bounds all client residuals and aggregate losses under the new market; zero MTA gives full coverage and zero modeled loss. | An unchanged market and zero reserve recover V06: `quote-refines-V06`, `receive-refines-V06`. |

This is a sequence of engine versions. Earlier states and operations remain
visible through projections or specializations. The table does not claim that
every version has the same state type, that every later quote equals an earlier
one, or that finite-catalog cash represents every arbitrary real balance.
The named theorems give the precise relationship in each case.

## The contract grows with the program

V01 starts with the familiar formula

```text
quoteCall(b) = max(claim(b) − cash(b), 0)
```

and a theorem whose conclusion mentions the actual state transition:

```agda
receive-correct : ∀ b paid paid₊ →
  quoteCall b ≤ᵣ paid → Safe (receive b paid paid₊)
```

`paid₊` proves that the received amount is nonnegative. This is a proof for every
input of the specified type, rather than a claim about selected evaluated cases.
A call calculation does not record a receipt.

V02 adds a client quantifier. V03 adds a scenario quantifier. V04 connects the
real specification to a rational executable gate. V05 changes the postcondition
from zero residual to an explicit tolerance. V06 changes the representation of
receipts and proves a commuting state transition. V07 changes the market inputs
and proves that a refreshed report suffices. The program and its contract evolve
together.

In the final version, let:

- `X₁(s,i)` be the new signed claim for scenario `s` and netting set `i`;
- `C₁(s,i)` be its eligible collateral, excluding separately recorded cash;
- `p′(i)` be cash derived from the updated receipt ledger;
- `t(i) ≥ 0` be that netting set's MTA;
- `θ(i)` be any supplied severity between zero and one.

If the newly credited receipts meet every computed request, `receive-correct`
constructs a `Guarantee` of

```text
max(X₁(s,i) − (C₁(s,i) + p′(i)), 0) ≤ t(i)                for every s, i
Σᵢ max(X₁(s,i) − (C₁(s,i) + p′(i)), 0) ≤ Σᵢ t(i)          for every s
Σᵢ θ(i) max(X₁(s,i) − (C₁(s,i) + p′(i)), 0) ≤ Σᵢ t(i)     for every s, θ
```

`zero-mta-safe` and `zero-mta-loss-zero` specialize this to full coverage and
zero modeled loss. Client identity is retained before taking positive parts;
a different client's surplus cannot discharge an unsecured claim.

The client count, scenario count, real market values, receipt catalog size,
and batch length are parameters. There is at least one supplied scenario;
clients or events may be empty. These are mathematical quantifiers, not a
production throughput benchmark. The theorem covers the supplied finite stress
family; it does not assert that future markets stay inside it.

## A complete report and receipt cycle

The report convention is deliberately stable throughout V04–V07:

```text
Report b bounds the current INCREMENTAL requirement at state b.
Existing cash is already accounted for inside b.
```

For arbitrary Cauchy-real inputs, a caller supplies a nonnegative rational upper
bound with its proof. For rational claim/collateral profiles and existing cash,
`V04Rational.RationalInputs` computes `initialState`, `initialAmounts`, and
`initialReport`; `initialReport-exact` proves those computed calls equal the
real specification. No sample market or assumed optimizer is needed.

After receiving new cash `d`, `advanceReport` calculates

```text
next upper = max(current upper − d, 0)
```

and proves that it bounds the new state's requirement. V04 also proves exactness
is preserved when the old report was exact. Partial payments produce valid next
reports; no new analysis certificate is needed for that receipt update.

V06 derives `d` from `newlyPaid(oldLedger, batch)`. IDs already credited and
repetitions within the batch contribute no additional cash. Its `process`
returns a `Processed` record with:

| Field | Meaning |
| --- | --- |
| `next-state` | The actual computed market-and-ledger state after ingesting the batch. |
| `state-correct` | A path identifying that returned state with `receive s batch`. |
| `next-report` | A report indexed by the returned state, ready for the next call. |
| `assessment` | Either evidence that the new receipts fulfilled the quote and produced the risk guarantee, or a client whose quote remains unmet. |

A failed assessment does not roll back an actual receipt and does not assert
that the account is unsafe: a conservative report can overstate the true
requirement. This differs from V04's complete economic decision when exactness
is supplied.

For revaluation, `Update s` contains a new market and uniform nonnegative bounds
on claim rises and effective-collateral falls. The ledger is unchanged during
`revalue`. `refreshReport` adds a certified rational upper reserve to the current
incremental report. It does not subtract already recorded cash again. V07 then
uses V06's same receipt operation and returns its `Processed` result. The next
report can feed another update, so the interface supports repeated cycles.

## The proof-assistant story for the talk

The progression demonstrates several distinct uses of proofs in software:

1. **Contracts tied to results.** `Safe (receive b paid paid₊)` describes the
   particular computed state, rather than a detached arithmetic fact.
2. **Quantified regressions.** A client projection, singleton stress family,
   zero MTA, and unchanged market each give a checked compatibility statement.
3. **Refinement at the numeric boundary.** Rational execution is connected to
   real valuation by an explicit bound or equality. Finite stress enumeration
   alone does not give a decision procedure for arbitrary real order.
4. **Refinement at the event boundary.** The identified-event state projects to
   the same economic state as crediting only newly received amounts.
5. **Dependent state changes.** V06 transports financial evidence along that
   state equality. Its replay theorem identifies the engine state together
   with its safety certificate, even if the proof is reconstructed differently.

V01 and V04 also exhibit univalence paths between equivalent policy propositions.
Cauchy reals are supplied by the existing higher-inductive construction; finite
lattice folds avoid selecting a maximizing index. Each module uses
`--safe --cubical`. The development adds no postulate or missing analysis axiom.
The public operational computation from V04 onward compares rationals; it does
not verify IEEE floating-point arithmetic or external pricing implementations.

## Scope of this presentation model

Claims may come from swap portfolios or another instrument model. The engine
consumes their valuation profiles, keeping instrument pricing outside this
progression. Eligible collateral is a nonnegative supplied profile; the earlier
[Broker collateral allocation theory](../Broker/Stage04Collateral.agda) can
justify such values from inventory, prices, and haircuts.

The catalog denotes distinct actual receipts with fixed owners and amounts.
Its cash remains available at par and is separate from eligible collateral.
The ledger proof does not authenticate a bank receipt, detect one physical
payment assigned two different IDs, or provide durable storage. V06's state
projection represents catalog-derived rational cash balances, not every V05
real cash state. There are no withdrawals, reversals, collateral returns, or
dynamic catalog extension in this version sequence.

The revaluation bounds and stress family are model inputs. The loss is positive
unsecured replacement exposure weighted by supplied default/recovery severity.
Settlement principal, native-currency funding, liquidation execution, legal
rights and empirical calibration require separate specifications. MTA is an
explicit tolerated residual, with the whole gap requested only when it exceeds
MTA; it is not a calibrated initial-margin or regulatory implementation.

`certified-state-replay` concerns receipt replay at a fixed valuation and pairs
state with `Guarantee`. It does not assert that all conservative `Report` values
are equal, or that an arbitrary revaluation workflow can be repeated unchanged.

## Imports and checking

```agda
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V07Revaluation as Broker
```

The [Broker2.agda](../Broker2.agda) umbrella exposes qualified version namespaces;
[Theory.agda](../Theory.agda) exposes them through `Broker2`. Earlier financial
examples and the first broker progression remain available independently.

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Broker2.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Theory.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

See [PROGRESS.md](PROGRESS.md) for the final checked source and review record.
