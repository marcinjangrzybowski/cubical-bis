# FX swaps and broker margin

This extension formalizes deliverable FX swaps and a broker managing client
portfolios of those swaps. It distinguishes market valuation, replacement
claims, collateral conversion, realized closeout loss, native-currency
funding, and settlement principal risk. The theory and examples use the
library's Cauchy reals throughout.

The flagship result is [BrokerGuarantees](Examples/FX/BrokerGuarantees.agda),
presented in [SYSTEM_GUARANTEES.md](SYSTEM_GUARANTEES.md). Its executable
`checkBroker` is sound and complete for whole-box client coverage together
with gross native-currency funding. `history-end-to-end` connects arbitrary
actual receipt sequences to coverage of the trade-by-trade swap portfolios,
zero modeled closeout loss under every admissible severity, and the funding
certificate. The worked program proves that the further 10 and 8 are sufficient
and that every real-valued covering further-payment vector costs at least 18.
Equal totals credited to the wrong client or held in the wrong currency are
computationally rejected.

The instrument convention follows the [BIS definition of FX
swaps](https://data.bis.org/help/glossary?item=FX+swaps): a near exchange of
currency principals and a reverse exchange at a later agreed date. This is
not a rolling spot/CFD contract with an overnight charge called a swap.

The [reference guide](REFERENCES.md) gives the BIS cashflow and funding
context, robust-optimization motivation for universal quote bounds, and BCBS
FX settlement guidance. It also distinguishes collateral haircut methodology
from regulatory applicability to physically settled FX swaps. All numerical
quotes, discount bounds, and collateral haircuts here are illustrative inputs.

## Instrument cashflows and valuation

[FXSwap.agda](Instruments/FXSwap.agda) records signed foreign notional, positive near and
far exchange rates, and natural-number dates with a proof that the near date
precedes the far date. Quotes are domestic currency per foreign unit.
Positive cashflow means receipt **by the broker**.

For signed foreign notional `q`, near rate `S₀`, and far rate `K`:

| Date | Broker domestic cashflow | Broker foreign cashflow |
| --- | ---: | ---: |
| Near | `q S₀` | `-q` |
| Far | `-q K` | `q` |

Positive `q` means the client receives foreign currency at the near date and
returns it at the far date. Negative `q` reverses the direction. Reversal,
scaling, return of foreign principal, and the domestic swap-points cashflow
`q(S₀-K)` are proved. Currency and date coordinates remain distinct: summing
cashflows algebraically does not establish payment-netting rights or permit
a future receipt to fund an earlier payment.

After the near leg settles, the modeled broker mark is

```text
V = q (S D_f - K D_d)
```

Here `S` is current spot and `D_d,D_f` are positive effective discount inputs
for the remaining settlement date at the valuation time. Their calculation,
funding/basis convention, calibration, and consistency across maturities are
external model choices. Positivity alone does not prove no arbitrage or an
initial fair price. The theorem `par-far-value` is explicitly conditional on
`S D_f = K D_d`.

Positive `V` is a replacement claim **owed to the broker**, not a broker
market loss. A broker market loss over a move is old mark minus new mark.
The finite-change identity retains the interaction of spot and foreign
funding factors:

```text
ΔV = q (D_f ΔS + S ΔD_f + ΔS ΔD_f - K ΔD_d)
```

Here the undifferenced `S,D_f` are the reference (old-state) values.
There is no differentiation or discarded second-order term. A portfolio
uses the existing finite dot-product aggregation; states can differ across
trades to reflect their different remaining maturities. `Phase` controls
which legs remain outstanding, but it is supplied rather than inferred from
calendar dates. A mark change crossing settlement requires accounting for
the settled cashflow separately.

## The margin policy being proved

For one supplied client netting set, let `Xᵢ` be the signed broker replacement
claim and `Cᵢ` eligible collateral in scenario `i`, in domestic units.
[Margin.agda](Margin/Base.agda) defines

```text
residualᵢ       = max(Xᵢ - Cᵢ, 0)
requiredMargin  = maxᵢ residualᵢ
```

This is the **least nonnegative uniform domestic cash top-up** covering every
modeled scenario. Its defining guarantee is

```text
requiredMargin ≤ b  ⇔  every Xᵢ ≤ Cᵢ + b        (provided b ≥ 0)
```

The implementation proves both directions, an equivalence of the certificate
types, and their path obtained by univalence. It also proves monotonicity in
claims, antitonicity in collateral, within-set netting/convexity bounds, and
transport under a uniform claim error.

The guarantee is conditional on collateral actually being received,
available, and realizable as modeled. `postCash` represents that changed
state. A calculated or issued call does not itself change collateral.
`paid-required-margin-zero` proves zero residual call after sufficient cash
is posted. The general real-payment law `margin-postCash` identifies the
remaining requirement as `stopLoss(requiredMargin, paid)` for any nonnegative
real payment; the rational controller specializes this theorem. This is a specified stress-margin policy, not a claim about a
particular jurisdiction's mandatory initial/variation-margin methodology.

Foreign collateral is valued in each scenario:

```text
eligible collateral = domestic cash + retention × spot × foreign units
```

`retention` is the fraction remaining after a haircut. Valid input conditions
include `0 ≤ retention ≤ 1` and nonnegative collateral amounts. The general
spot-monotonicity theorem holds with claims fixed; FX swap claims that also
move with spot must be revalued jointly, as in the example.

The arbitrary-scenario layer [Margin/Scenario.agda](Margin/Scenario.agda)
expresses coverage for any supplied admissible state predicate. Its least
nonnegative cash certificate covers both finite scenario lists and continuous
uncertainty sets. An explicit binding state gives the stronger leastness
statement for every real budget. The joint FX box example supplies those
states instead of assuming a procedure that selects a maximizing real quote.

## Two clients with matched FX swap portfolios

[BrokerMargin.agda](Examples/FX/BrokerMargin.agda) supplies two swap notionals, 60 and 40.
Both have near/far rates 1 and dates 0/30. Client A holds one of each; client B
holds their reversals. The example uses zero swap points to keep the
arithmetic visible. The generic instrument permits different positive near
and far rates. All amounts and shocks are illustrative model inputs.

The near leg has settled, and reference spot and both discount factors are
1, so initial marks are zero. Four valuation scenarios give:

| Scenario | Spot | Domestic factor | Foreign factor | Broker claim on A | Broker claim on B |
| --- | ---: | ---: | ---: | ---: | ---: |
| Foreign appreciation | 6/5 | 1 | 1 | 20 | -20 |
| Foreign depreciation | 4/5 | 1 | 1 | -20 | 20 |
| Domestic factor falls | 1 | 9/10 | 1 | 10 | -10 |
| Foreign factor falls | 1 | 1 | 9/10 | -10 | 10 |

The signed market marks sum to zero in every scenario. A and B are separate
client netting sets, so the broker retains their separate positive claims.
Client A has 5 domestic cash collateral. Client B has 10 foreign units with
retention `4/5`.

| Scenario | A collateral | B eligible collateral | A residual | B residual | Broker total residual |
| --- | ---: | ---: | ---: | ---: | ---: |
| Foreign appreciation | 5 | 48/5 | 15 | 0 | 15 |
| Foreign depreciation | 5 | 32/5 | 0 | 68/5 | 68/5 |
| Domestic factor falls | 5 | 8 | 5 | 0 | 5 |
| Foreign factor falls | 5 | 8 | 0 | 2 | 2 |

The exact cash calls are **15 for A and 68/5 (13.6) for B**. Each is minimal
for its own client and the four specified scenarios. After those amounts are
received in domestic cash, their residual margin is zero.
The separate calls total `143/5` (28.6), as proved by `total-client-calls`.
Their binding scenarios differ. The broker's aggregate exposure maximum 15
and exposure CVaR 14.3 are different diagnostics and do not replace separately
received collateral for each client under this margin policy.

If B's foreign collateral is frozen at its reference eligible value 8, the
model asks for only 12. In the depreciation scenario, the claim has risen to
20 while eligible collateral has fallen to `32/5`. Paying 12 then leaves
`8/5` (1.6) uncovered. These values and the insufficiency proof are checked.
This is adverse co-movement of claim and collateral values; no statistical
default-correlation model is inferred from it.

For an additional distributional diagnostic, the four scenarios are assigned
equal weights. Broker residual exposure has mean `89/10`, maximum 15, and
CVaR `143/10` at 50% confidence. An explicit threshold 5 and dual distribution
`(1/2,1/2,0,0)` certify the CVaR value. These probabilities are illustrative
market-scenario weights, not estimated probabilities of client default.

## Joint market moves and an entire real uncertainty box

Single-factor tests do not by themselves bound simultaneous changes.
[FXBounds.agda](Instruments/FXBounds.agda) proves interval bounds for every Cauchy-real
state satisfying supplied box-membership evidence. For nonnegative notional:

```text
q(S_low D_f_low - K D_d_high) ≤ V ≤ q(S_high D_f_high - K D_d_low)
```

Reversed swaps inherit the negated bounds. There is no case split on real
order, grid search, or assumption that a general maximum exists.

[JointFXMargin.agda](Examples/FX/JointFXMargin.agda) applies this theory to the same client
portfolios with spot in `[4/5,6/5]` and both discount factors in `[9/10,1]`.
Every original scenario is in this box, but the box also admits joint moves.

| Attaining joint state | Spot | Domestic factor | Foreign factor | Relevant claim | Eligible collateral | Required cash |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| A's maximum | 6/5 | 9/10 | 1 | 30 | 5 | 25 |
| B's maximum | 4/5 | 1 | 9/10 | 28 | 32/5 | 108/5 |

The code proves both universal sufficiency and minimality:

```text
25 ≤ cash_A       ⇔ A is covered at every real quote in the box
108/5 ≤ cash_B    ⇔ B is covered at every real quote in the box
```

B's claim maximum and collateral minimum occur at the same explicit state,
so the combined bound is sharp. The reported requirements cover an entire
real-valued uncertainty family, not only the two displayed witnesses.
Box membership is an assumption on permitted valuation inputs, not a claim
that the box contains every possible market state or imposes curve consistency.

| Client | Cash for four single-factor scenarios | Cash for all quotes in the box | Further cash after the old payment |
| --- | ---: | ---: | ---: |
| A | 15 | 25 | 10 |
| B | 68/5 | 108/5 | 8 |

The old payments are proved insufficient under the enlarged model. Exact
rational reports on the two attaining states drive executable payment checks;
their coverage of the whole box follows from the separate universal
equivalence theorems. A generic `ExactMargin` report alone certifies only
its specified finite scenario vectors.

## Executable calls and received payments

[MarginControl.agda](Margin/MarginControl.agda) uses an `ExactMargin` record containing
a rational amount and proof that it equals the real scenario requirement.
It does not assume every real requirement is rational. Given received
nonnegative domestic cash, the further request is

```text
outstanding = max(exact amount - cash already received, 0)
```

The request is proved minimal. It equals the residual margin recomputed
after the actual payment. `recordPayment` returns a report for that changed
collateral state; paying the further request clears the residual.
`checkPayment` compares rationals and returns either coverage evidence or
a proof that more cash is due.

[BrokerOperations.agda](Examples/FX/BrokerOperations.agda) checks these reductions for the
four-scenario reports:

| Operation | Checked result |
| --- | --- |
| A pays 14 | More due |
| A pays 15 | Covered |
| B pays 12 | More due; exact further request 8/5 |
| B then pays 8/5 against its updated report | Covered |
| B pays 68/5 at once | Covered |

After both clients pay the required cash, the broker residual and every
admissible realized-closeout-loss severity are zero **for these scenarios**.
The joint-box reports similarly reject the earlier payments 15 and `68/5`.
Changing the risk model requires a new certificate; a prior payment verdict
does not automatically cover a larger uncertainty set.

## Client identity, netting, and realized losses

[ClientNetting.agda](Margin/ClientNetting.agda) proves

```text
max(Σ claims - Σ collateral, 0)
  ≤ Σ_clients max(claim_client - collateral_client, 0)
```

The left side is a pooled comparison quantity. It is not the separate-client
exposure policy. The simple claims `(10,-10)` have total mark zero and positive
exposure 10. In the broker example, pooling would incorrectly report zero
residual despite the nonzero values above.

The HIT economic quotient therefore retains **client and scenario labels**.
For fixed collateral, exposure descends through equality of all those claim
profiles. A checked impossibility theorem shows that no separate-exposure
function on aggregate-mark classes can preserve its value on every original
position. If collateral also varies between positions, it must be included
in the equivalence criterion. The supplied netting-set tags do not establish
legal enforceability or prevent physical collateral from being double-counted
by an external bookkeeping system.

[CounterpartyRisk.agda](Margin/CounterpartyRisk.agda) distinguishes exposure from
realized closeout loss. An input severity `θⱼ ∈ [0,1]` represents occurrence of
default combined with the unrecovered fraction for client `j`:

```text
realized closeout loss = Σⱼ θⱼ max(claimⱼ - collateralⱼ, 0)
```

The loss is nonnegative and bounded by broker residual exposure. The latter
is the exact bound over every permitted severity, since all-one severity
attains it. Severities may depend on both client and market scenario; no
independence assumption is made. Worst-case, expectation, and CVaR acceptance
certificates transfer from exposure to every such realized-loss profile.
With every client claim covered, all these modeled closeout losses vanish.
This does not remove a separate settlement-principal or liquidity obligation.

## Funding and settlement remain separate controls

[Settlement.agda](Settlement/Base.agda) keeps signed native-currency cashflows by
trade and date. Outgoing principal is the positive part of the negative
cashflow. It proves that algebraically netted outgoing amounts do not exceed
gross outgoing amounts, but the inequality does not authorize payment
netting. Funding certificates compare balances with outgoing amounts in
**each currency and at each date**.

A single cashflow `(-100 domestic, +100 foreign)` has mark zero at spot 1,
yet requires 100 domestic units. Holding only foreign currency does not
satisfy that domestic funding certificate. A trade and its reversal have
zero aggregate cashflow but gross outgoing payments of 100 in each currency.
The generic converted principal-at-risk bounds retain these obligations.

The broker operations example constructs the actual four far-leg instructions
from the 60/40 swaps and their reversals. It proves that every far date is 30,
net cashflow is zero in both currencies, and gross outgoing amounts are
`(100 domestic,100 foreign)`. Those native-currency buffers satisfy its
gross-funding certificate. At conversion factors `(1,1)`, the gross amounts
are worth 200 domestic units. Zero funding is proved insufficient even after
the separate closeout margin calls have been paid; client collateral is not
declared reusable for settlement funding.

A small delivery-state model distinguishes unreleased payments from
irrevocably released principal, and pending/final/failed receipts. Under its
explicit zero-recovery failure assumption, paid-away principal can be lost.
An ideal atomic exchange condition proves this principal exposure and loss
zero; it does not prove away replacement-cost, funding, or operational risk.
The distinction between replacement costs, principal risk, and per-currency
liquidity is motivated by the [BIS FX settlement
guidance](https://www.bis.org/publ/bcbs241.pdf). The formalization is a finite
mathematical model, not an implementation or compliance assessment of an
actual settlement system.

Each certificate applies to its specified stage and obligation. Combining
closeout exposure, settlement principal, and liquidity into one capital
number would require additional joint accounting.

## Scope of the certificates

The proofs use constructive real order and lattice operations, cubical
function extensionality, proposition-valued evidence, univalence, and HIT
set quotients. No real-order decision procedure, missing-analysis postulate,
or choice of a quotient representative is assumed.

Inputs still need a defensible valuation model, market shocks, collateral
eligibility and realization assumptions, client grouping, and funding
resources. The code does not estimate default probabilities, compute CVA,
infer a legal netting right, perform a liquidation, or submit a margin call
to a client. Calendar processing, minimum transfer amounts, rounding, settlement
calendars, credit limits, custody and cash ledgers, and market-data integration
are further application work.

## Entry points and validation

| Module | Role |
| --- | --- |
| [FXSwap](Instruments/FXSwap.agda) | Two-leg contracts, dated currency cashflows, lifecycle marks, exact factor changes |
| [FXBounds](Instruments/FXBounds.agda) | Universal mark bounds for real spot/discount boxes |
| [Margin](Margin/Base.agda) | Least cash top-up, coverage equivalences, stressed collateral |
| [MarginControl](Margin/MarginControl.agda) | Exact rational requests, partial payments, certified decisions |
| [ClientNetting](Margin/ClientNetting.agda) | Per-netting-set residuals and labelled economic quotients |
| [CounterpartyRisk](Margin/CounterpartyRisk.agda) | Default/recovery severities and risk-budget transfer |
| [Settlement](Settlement/Base.agda) | Currency/date liquidity, gross principal, conditional atomic settlement |
| [BrokerMargin](Examples/FX/BrokerMargin.agda) | Client portfolios, four scenarios, collateral FX shortfall, exposure CVaR |
| [BrokerOperations](Examples/FX/BrokerOperations.agda) | Executable payment workflow and actual gross settlement instructions |
| [JointFXMargin](Examples/FX/JointFXMargin.agda) | Sharp whole-box calls and rejection of single-factor capital |

The umbrella includes all modules. Check it from the repository root:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

The final validation record and proof-discipline checks are in
[PROGRESS.md](PROGRESS.md).
