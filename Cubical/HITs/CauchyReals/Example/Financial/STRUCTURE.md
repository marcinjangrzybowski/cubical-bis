# Structure, shared interfaces, and imports

The canonical implementation is organized by mathematical responsibility.
Worked examples live under `Examples/`; their illustrative data is not part
of the reusable theory. Existing flat imports remain forwarding modules.

## Entry points and dependency direction

- [Theory.agda](Theory.agda) publicly exports reusable financial theory.
- [Broker2.agda](Broker2.agda) exports successive versions of [one margin engine](Broker2/README.md), with a [speaker guide](Broker2/PRESENTATION.md).
- [Broker.agda](Broker.agda) exports the eight generic [broker stages](Broker/README.md) with qualified names.
- [Examples.agda](Examples.agda) imports all worked applications with qualified names.
- [../Financial.agda](../Financial.agda) preserves the original public API and
  qualified examples, and checks both new entry points.

For focused use, import the canonical module directly:

```agda
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base
import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerMargin as Broker
```

`Core/` provides common finite arithmetic, probability, bounds and economic
identity. `Risk/`, `Portfolio/`, `Dynamic/`, `Instruments/`, `Margin/`, and
`Settlement/` build the reusable financial statements. `Broker/` composes them
in a separate, increasingly rich progression of generic margin controllers. These implementations
import canonical theory paths; none imports `Examples` or a legacy forwarding
module. Examples may compose related examples. General-purpose example inputs
belong in [CommonScenarioData](Examples/CommonScenarioData.agda), so an FX
application does not acquire a dependency on a particular asset portfolio
merely to use a uniform probability distribution.

The flagship composed statements are
[BrokerGuarantees](Examples/FX/BrokerGuarantees.agda) and
[TradingGuarantees](Examples/Portfolio/TradingGuarantees.agda), with motivation
and theorem-level contracts in [SYSTEM_GUARANTEES.md](SYSTEM_GUARANTEES.md).
The theory entry point exposes the new reusable controls as public qualified
namespaces `MarginWorkflow`, `PaymentHistory`, and `Broker`, keeping their status and
receipt names separate from the existing scalar controller and settlement API.

## One engine evolved for a presentation

[Broker2/](Broker2/README.md) contains seven successive engine versions, each
importing its predecessor. The recurring operations are `quoteCall`, `receive`,
and `receive-correct`. Relationships are proved by client/scenario projection,
singleton specialization, rational receipt embedding, zero-MTA equality,
identified-receipt accounting, and unchanged-market regression.

The version sequence contains complete engine workflows, including a generic
rational factory for exact initial reports, incremental report updates after
partial receipts, and a final `process` result carrying the next state, report,
and assessment. It reuses the existing finite-margin, receipt-journal and drift
lemmas. The earlier broker progression remains independent. `Theory.Broker2`
exports qualified version namespaces; no concrete example is imported.

## Generic broker progression

[Broker/README.md](Broker/README.md) gives the stage-by-stage contracts and
[Broker/REFERENCES.md](Broker/REFERENCES.md) maps them to primary literature.
Stages add cash, arbitrary scenario coverage, client netting, inventory and
haircuts, identified receipts, revaluation, minimum transfers, and the final
controller. They reuse `Core`, `Risk` and `Margin` without importing worked
examples or changing the earlier broker application.

The progression distinguishes exact minimum certificates from sufficient upper
reports, a call from a receipt, a minimum-transfer tolerance from full coverage,
and proof of an unfulfilled plan from proof of economic deficiency. The journal
uses immutable IDs and contributes only newly credited cash. The final controller
proves loss bounds for the actual updated ledger, plus equality of the complete
ledger/certificate state after replay. It contains no numerical scenarios.

## Shared expressions and reusable statements

| Interface | Role and current consumers |
| --- | --- |
| [Core/Vectors](Core/Vectors.agda): `two`, `three`, `four` | Constructors for `Fin n → A`, polymorphic in `A : Type ℓ`; shared by numeric profiles and scenario examples. |
| [Core/Finite](Core/Finite.agda): `sum-negate` | Negation commutes with a finite real sum; settlement uses it to compare net and gross outgoing payments. |
| [Core/Bounds](Core/Bounds.agda): `Bound`, `InInterval`, product bounds | Closed intervals with nonnegative lower endpoints. FX valuation uses these arithmetic bounds; the definitions contain no FX-specific data. |
| [Risk/Shortfall](Risk/Shortfall.agda): `stopLoss-upper`, `stopLoss-evaluate`, `stopLoss-at-zero` | Common coverage and exact-evaluation rules used by margin, client exposure, portfolio and FX examples. |
| [Risk/FiniteShortfall](Risk/FiniteShortfall.agda): `positivePart-sum-bound`, `stopLoss-sum-bound` | Positive-part and shortfall bounds for arbitrary finite sums; used by client netting and settlement. |
| [Risk/WorstCase](Risk/WorstCase.agda): `worstCase-exact-at` | An upper bound and a supplied attaining index certify an exact finite maximum. |
| [Margin/Scenario](Margin/Scenario.agda): `Coverage`, `MarginCertificate`, `BindingScenario` | Coverage and minimal cash over an arbitrary admissible scenario domain; instantiated by finite margin and joint FX bounds. |
| [Margin/Workflow](Margin/Workflow.agda): `CertifiedClients` | Any finite client count and admissible scenario domain: complete rational coverage checks, zero-loss guarantees, and minimal further requests. |
| [Margin/PaymentHistory](Margin/PaymentHistory.agda): `creditHistory`, `processHistory` | Arbitrary receipt sequences, scenario-polymorphic collateral updates, exact outstanding calls and transported report equality under batching. |
| [Margin/Base](Margin/Base.agda): `margin-postCash` | For every nonnegative real payment, the remaining margin equals the positive part of the original margin less that payment. The rational payment controller specializes it. |
| [Portfolio/TransactionCosts](Portfolio/TransactionCosts.agda): `TailCosts.objective-cash-at` | Cash translation at an arbitrary threshold; the rebalancing example delegates its net objective identity to this shared law. |

The shared example data includes `half`, `quarter`, the fair two-state and
uniform four-state distributions, `halfTail`, and three admissible dual
measures. The names `stress02`, `stress12`, and `stress01` identify their
nonzero coordinates. Their admissibility depends on the base distribution
and tail multiplier; tightness for a particular portfolio is proved by its
example. The original `Diversification.dualA`, `dualB`, and `dualBalanced`
names remain public aliases.

## Scenario certificates and constructive boundaries

For arbitrary states `S` and a supplied admissibility predicate `A`:

```text
Coverage A X C b = every admissible state s satisfies X(s) ≤ C(s) + b
```

`MarginCertificate A X C m` contains nonnegativity of `m`, coverage at `m`,
and leastness among nonnegative budgets. It proves
`m ≤ b ≃ Coverage A X C b` when `0 ≤ b`.

A `BindingScenario A X C m` supplies an admissible state with the **raw**
difference `X(s) - C(s) = m`. Together with coverage at `m`, this proves the
equivalence for **all real budgets**, preserving the stronger existing joint
FX results. Merely knowing `stopLoss(X(s), C(s)) = 0` would not suffice:
a negative raw difference can leave surplus collateral. The record and
equivalence interfaces are universe polymorphic; their univalence paths
currently specialize to small state and admissibility types.

Finite maxima are constructive lattice folds. Neither `worstCase-exact-at`
nor `margin-exact-at` selects a maximizing index for arbitrary Cauchy reals;
each consumes explicit evidence. The general finite margin certificate does
not require such an index. `IsCVaR` still requires supplied attainment and a
global bound; this refactor does not assume general optimizer existence.

## Financial terminology and units

| Expression | Convention |
| --- | --- |
| Scenario loss `X` | Positive is loss, negative is gain, in a common value unit and horizon. |
| Broker replacement claim | Positive is owed to the broker; negative is owed by it. Client netting labels remain explicit. |
| Signed settlement cashflow | Positive is receipt by the broker, negative is a payment owed, in its native currency and date. |
| `stopLoss x c` | `(x - c)⁺`; a threshold shortfall generally, and residual exposure when `c` is eligible collateral. |
| `requiredMargin` | Least nonnegative uniform domestic cash top-up under the supplied stress policy. It becomes collateral through `postCash`. |
| Broker residual exposure | Sum of separately clamped client-netting-set claims after collateral. Default/recovery severities turn this into modeled closeout loss. |
| Tail multiplier `κ` | Reciprocal of tail probability mass, or `1/(1-confidence)` as an interpretation; the formal input is `κ ≥ 1`. |
| Proportional execution cost | Sum of rate times absolute traded amount across all legs. Conventional one-way turnover may be half that total. |

These distinctions matter when composing portfolio risk, collateral and
settlement models. [REFERENCES.md](REFERENCES.md) gives their methodological
sources and the numerical conventions used in the examples.

## Flat import migration

All paths below are relative to `Financial/`. New source edits belong at the
canonical destination. A legacy module contains only imports and compatibility
aliases, so there is one implementation of each result.

| Original path | Canonical implementation |
| --- | --- |
| [Ambiguity](Ambiguity.agda) | [Risk/Ambiguity](Risk/Ambiguity.agda) |
| [Application](Application.agda) | [Examples/Portfolio/Application](Examples/Portfolio/Application.agda) |
| [BrokerMargin](BrokerMargin.agda) | [Examples/FX/BrokerMargin](Examples/FX/BrokerMargin.agda) |
| [BrokerOperations](BrokerOperations.agda) | [Examples/FX/BrokerOperations](Examples/FX/BrokerOperations.agda) |
| [ClientNetting](ClientNetting.agda) | [Margin/ClientNetting](Margin/ClientNetting.agda) |
| [CounterpartyRisk](CounterpartyRisk.agda) | [Margin/CounterpartyRisk](Margin/CounterpartyRisk.agda) |
| [Diversification](Diversification.agda) | [Examples/Portfolio/Diversification](Examples/Portfolio/Diversification.agda) |
| [DynamicAmbiguity](DynamicAmbiguity.agda) | [Dynamic/Ambiguity](Dynamic/Ambiguity.agda) |
| [DynamicRisk](DynamicRisk.agda) | [Dynamic/Base](Dynamic/Base.agda) |
| [EconomicEquivalence](EconomicEquivalence.agda) | [Core/EconomicEquivalence](Core/EconomicEquivalence.agda) |
| [ExecutionEquivalence](ExecutionEquivalence.agda) | [Portfolio/ExecutionEquivalence](Portfolio/ExecutionEquivalence.agda) |
| [ExpectedShortfall](ExpectedShortfall.agda) | [Risk/ExpectedShortfall](Risk/ExpectedShortfall.agda) |
| [FXBounds](FXBounds.agda) | [Instruments/FXBounds](Instruments/FXBounds.agda) |
| [FXSwap](FXSwap.agda) | [Instruments/FXSwap](Instruments/FXSwap.agda) |
| [Finite](Finite.agda) | [Core/Finite](Core/Finite.agda) |
| [JointFXMargin](JointFXMargin.agda) | [Examples/FX/JointFXMargin](Examples/FX/JointFXMargin.agda) |
| [Margin](Margin.agda) | [Margin/Base](Margin/Base.agda) |
| [MarginControl](MarginControl.agda) | [Margin/MarginControl](Margin/MarginControl.agda) |
| [Policy](Policy.agda) | [Portfolio/Policy](Portfolio/Policy.agda) |
| [Portfolio](Portfolio.agda) | [Portfolio/Base](Portfolio/Base.agda) |
| [Probability](Probability.agda) | [Core/Probability](Core/Probability.agda) |
| [Rebalancing](Rebalancing.agda) | [Examples/Portfolio/Rebalancing](Examples/Portfolio/Rebalancing.agda) |
| [RiskControl](RiskControl.agda) | [Risk/RiskControl](Risk/RiskControl.agda) |
| [RiskLaws](RiskLaws.agda) | [Risk/RiskLaws](Risk/RiskLaws.agda) |
| [RobustAllocation](RobustAllocation.agda) | [Examples/Portfolio/RobustAllocation](Examples/Portfolio/RobustAllocation.agda) |
| [Settlement](Settlement.agda) | [Settlement/Base](Settlement/Base.agda) |
| [Shortfall](Shortfall.agda) | [Risk/Shortfall](Risk/Shortfall.agda) |
| [StressConstrainedTrade](StressConstrainedTrade.agda) | [Examples/Portfolio/StressConstrainedTrade](Examples/Portfolio/StressConstrainedTrade.agda) |
| [TradeDecision](TradeDecision.agda) | [Examples/Portfolio/TradeDecision](Examples/Portfolio/TradeDecision.agda) |
| [TransactionCosts](TransactionCosts.agda) | [Portfolio/TransactionCosts](Portfolio/TransactionCosts.agda) |
| [Variance](Variance.agda) | [Risk/Variance](Risk/Variance.agda) |
| [VarianceExample](VarianceExample.agda) | [Examples/Portfolio/VarianceExample](Examples/Portfolio/VarianceExample.agda) |
| [WorstCase](WorstCase.agda) | [Risk/WorstCase](Risk/WorstCase.agda) |

The following examples formerly nested inside theory modules are now separate:

| Preserved legacy name | Canonical example |
| --- | --- |
| `DynamicRisk.DownstreamControl` | [Examples/Dynamic/DownstreamControl](Examples/Dynamic/DownstreamControl.agda) |
| `DynamicAmbiguity.RectangularGap` | [Examples/Dynamic/RectangularGap](Examples/Dynamic/RectangularGap.agda) |
| `ClientNetting.OppositeClaims` | [Examples/Netting/OppositeClaims](Examples/Netting/OppositeClaims.agda) |
| `Settlement.TwoCurrencyExample` | [Examples/Settlement/TwoCurrencyExample](Examples/Settlement/TwoCurrencyExample.agda) |
| `FXBounds.JointMoveExample` | [Examples/FX/JointMoveExample](Examples/FX/JointMoveExample.agda) |
| Concrete declarations of `ExecutionEquivalence` | [Examples/Portfolio/ExecutionEquivalence](Examples/Portfolio/ExecutionEquivalence.agda) |

`Portfolio/ExecutionEquivalence` contains only the general `ExecutionModel`.
The legacy module also reexports its original concrete example declarations.
Inherited `DynamicAmbiguity.DownstreamControl` and
`CounterpartyRisk.OppositeClaims` names also remain available. The old umbrella
retains its nested example names; the theory-only umbrella omits the
demonstrations. Public nested modules use `open import ... public`, preserving
exported names without copying primitive declarations through module application.

## Checking

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Theory.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

The full umbrella reaches all canonical modules and legacy wrappers, including
the existing executable reduction proofs. [PROGRESS.md](PROGRESS.md) records
the final compiler outcome and dependency/API audit.
