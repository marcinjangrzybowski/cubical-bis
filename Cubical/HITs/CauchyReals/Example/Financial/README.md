# Constructive portfolio risk over Cauchy reals

This development implements a finite-scenario portfolio risk system in safe
Cubical Agda. Its inputs may be arbitrary higher-inductive Cauchy reals, not
just embedded rational numbers. The application supplies exact rational data
and proves a portfolio optimum, executes a certified budget check, and carries
policy evidence through rebalancing and economic netting. Extensions add
transaction costs, executable optimal trade selection, probability ambiguity,
and sequential capital control.
The instrument extension adds deliverable FX swaps and broker margin,
including foreign collateral, client netting sets, default/recovery
severities, and currency-specific settlement funding.

For a presentation to quantitative developers, start with
[Broker2: one engine, seven versions](Broker2/README.md). Each version evolves
`quoteCall`, `receive`, and its correctness contract, with a proved connection
to the preceding version. The [28-minute speaker guide](Broker2/PRESENTATION.md)
follows the program from one cash account to replay-safe receipt processing and
certified revaluation, without introducing concrete market scenarios.

For the generic broker machinery, start with the new
[Broker correctness progression](Broker/README.md): eight stages from a single
cash account through scenario reports, separate netting sets, inventory-backed
collateral, identified receipts, revaluation and minimum transfers to a composed
controller. Its final theorem bounds every client and aggregate modeled loss
after actual receipts, with zero loss at zero transfer tolerance. The progression
contains no concrete scenarios; [its references](Broker/REFERENCES.md) explain
the literature basis and [its progress log](Broker/PROGRESS.md) records checks.

Start with [System correctness: motivating examples](SYSTEM_GUARANTEES.md).
The flagship [broker guarantee](Examples/FX/BrokerGuarantees.agda) proves that
an executable payment/funding check succeeds exactly when every client is
covered at every real quote in the specified box and the actual settlement
book has enough native-currency funding. Success yields zero modeled closeout
loss for every admissible default/recovery realization. The same statement
holds for arbitrary finite histories of actual client receipts.

The [trading guarantee](Examples/Portfolio/TradingGuarantees.agda) turns the
fee-aware optimizer into a complete feasibility solver: success returns a
certified allocation, while failure proves that **no** signed real fully
invested competitor meets the stated tail budget in this market.

[FX_BROKER.md](FX_BROKER.md) and [EXTENSIONS.md](EXTENSIONS.md) explain the
component models. [Application.agda](Examples/Portfolio/Application.agda) and
[Diversification.agda](Examples/Portfolio/Diversification.agda) provide the
original portfolio workflow and optimizer. [PROGRESS.md](PROGRESS.md) records
implementation milestones, independent reviews, and validation.

## Organization and references

[Theory.agda](Theory.agda) is the reusable entry point and imports no worked
examples. [Examples.agda](Examples.agda) collects the applications under
qualified names. The original `Financial.agda` umbrella and flat module paths
remain compatibility imports. New implementations and imports use this layout:

| Folder | Responsibility |
| --- | --- |
| `Core/` | Finite real arithmetic, polymorphic vector constructors, nonnegative interval bounds, probability, economic equivalence |
| `Risk/` | Scalar and finite shortfall, worst-case loss, CVaR, variance, ambiguity, certified risk checks |
| `Portfolio/` | Holdings, transaction costs, policies, execution equivalence |
| `Instruments/` | Deliverable FX swaps and valuation bounds |
| `Broker2/` | Seven evolving versions of one margin engine, with compatibility proofs and a presentation guide |
| `Broker/` | Eight-stage generic margin machinery and system correctness proofs |
| `Margin/` | Scenario coverage, cash requirements, payment control, client exposure and counterparty loss |
| `Dynamic/` | Two-stage risk and rectangular ambiguity |
| `Settlement/` | Currency/date cashflows, liquidity and principal exposure |
| `Examples/` | Shared illustrative data and portfolio, FX, dynamic, netting and settlement applications |

[STRUCTURE.md](STRUCTURE.md) explains shared interfaces, terminology,
dependencies, and migration from every old import path.
[REFERENCES.md](REFERENCES.md) connects the examples to primary sources and
states which aspects they support. Each example also names its methodological
references in source comments. The numerical scenarios and parameters are
synthetic; the references motivate the methods rather than calibrate the data.

## FX instruments and broker margin

The [FX broker guide](FX_BROKER.md) develops two-leg deliverable FX swaps,
exact spot/discount-factor valuation changes, and the least domestic cash
top-up covering a client's stressed replacement claims. Currency collateral
is revalued with the claims; a calculated call becomes protective collateral
only after it is paid and available as modeled.

Two clients hold opposite portfolios of swaps with notionals 60 and 40.
Their market marks cancel, but client identity and principal obligations
remain relevant:

| Control | Checked result |
| --- | --- |
| Four single-factor scenarios | Client cash calls 15 and `68/5`; frozen foreign collateral leaves a proved `8/5` shortfall. |
| All real quotes in a joint spot/discount box | Sharp cash calls 25 and `108/5`; earlier payments require a further 10 and 8. |
| Received payments | Arbitrary receipt histories preserve exact outstanding calls and whole-box coverage; equal per-client totals preserve the combined broker decision. |
| Counterparty loss | Exposure bounds every supplied default/recovery severity; paid sufficient collateral eliminates modeled residual closeout loss. |
| Settlement funding | Actual far legs net to zero but require gross native-currency payments of 100 domestic and 100 foreign; the combined checker rejects 200 domestic and zero foreign. |
| End-to-end broker policy | Pass iff all-client whole-box coverage and gross funding hold; staged receipts yield a certificate for the actual swap book. |

Client-labelled HIT quotients preserve exposure; an aggregate-mark quotient
is proved to lose information needed for that calculation. The box results
cover an infinite family of Cauchy-real states using constructive bounds
and explicit attaining witnesses. The guide distinguishes these mathematical
guarantees from valuation calibration, legal enforceability, and operational
receipt of collateral.

## Model and conventions

A loss vector is `Fin n → ℝ`. Positive values are losses; negative values are
gains. A distribution contains nonnegative real scenario weights and a proof
that their finite sum is one. Zero-probability scenarios are permitted.

A market maps each asset to a scenario-loss vector. Portfolio losses are the
finite dot product of holdings and unit asset losses. General holdings can be
negative; the `Allocation` subtype restricts them to nonnegative weights with
total capital one. Amounts in the diversification example are abstract loss
units over a single horizon, not prices or percentages inferred from market data.

The model separates three controls:

| Control | Meaning |
| --- | --- |
| Expected loss | Probability-weighted mean loss |
| Worst-case stress loss | Maximum over a **nonempty** scenario set, including zero-probability stress scenarios |
| Expected shortfall / CVaR | Attained minimum of the threshold objective described below |

Variance and covariance provide additional dispersion diagnostics; variance
is distinct from a loss-based capital requirement. The extensions also study
the worst expected loss across a finite family of probability models and its
entire convex hull, and compose risk rules on a two-stage scenario tree.

## Further theory and applications

The [extension guide](EXTENSIONS.md) gives definitions, proof ideas, precise
input assumptions, and the following checked results:

| Question | Result |
| --- | --- |
| When should a concentrated portfolio trade, including proportional fees? | For fee parameter `0 ≤ s ≤ 4`, weights `(3/4,1/4)` attain CVaR `2+s/4`; for `s ≥ 4`, no trade attains the minimum 3. Rational inputs give executable certified trade and budget decisions. |
| What if the trade must also obey a scenario stress cap? | For `2 ≤ c ≤ 4`, A weight `(c+2)/8` minimizes CVaR including any nonnegative proportional fee subject to raw stress at most `c`. Fee 1 and cap 3 give CVaR `19/8`; budget `9/4` is impossible for every feasible portfolio. |
| What if scenario probabilities are uncertain? | A different allocation `(9/20,11/20)` uniquely minimizes worst expected loss across two models and all their mixtures, with capital `7/5`. Its scenario stress loss increases from 2 to `12/5`. |
| Can managers check capital locally at intermediate branches? | Two-stage coherent risk composes with proved time consistency, node-budget propagation, and a finite expectation tower formula. |
| Does independently changing models at each branch matter? | Coupled uncertainty has capital 2 in a checked example; independent branch uncertainty gives nested capital 4. |
| Can equal raw portfolios still have different execution risk? | A direct basket and a wrapped basket have identical raw losses but fees 1 and 3, producing CVaR 3 and 5. Quotient descent is characterized by fee invariance. |

The trading and ambiguity examples optimize different criteria. The
stress-constrained trade explicitly couples a raw scenario limit with CVaR
including fees; the other optima do not assert automatic compliance with
the original combined policy limits.

## Worked diversification and optimization

Each scenario has probability `1/4`.

| Scenario | Asset A | Asset B | Equal-weight portfolio |
| --- | ---: | ---: | ---: |
| A stress | 6 | -2 | 2 |
| B stress | -2 | 6 | 2 |
| Neutral 1 | 0 | 0 | 0 |
| Neutral 2 | 0 | 0 | 0 |

The tail multiplier is `κ = 2`, corresponding to the worst 50% of probability
mass. This small confidence level makes every step of the example visible.

| Quantity | Asset A | Asset B | Equal-weight portfolio |
| --- | ---: | ---: | ---: |
| Expected loss | 1 | 1 | 1 |
| Worst-case stress loss | 6 | 6 | 2 |
| CVaR at 50% confidence | 3 | 3 | 2 |
| Variance | 9 | 9 | 1 |

For every **real** weight `w`, including shorted allocations, let
`L(w) = w A + (1-w) B`. The distribution `(1/2, 1/2, 0, 0)` is an admissible
dual witness with expected loss exactly 2 for every `w`. Weak duality proves
`2 ≤ F(L(w), t)` for **every real threshold** `t`. The equal-weight allocation
attains 2 at threshold 0, so it is a global optimizer over both variables.
This result does not depend on a grid search or an unproved optimizer.

CVaR minimizers need not be unique. Worst-case stress risk provides a stronger
selection criterion in this example: the two stress losses are `8w-2` and
`6-8w`, and requiring both to be at most 2 forces `w = 1/2`.
The quarter allocation is a checked second CVaR optimizer: it has losses
`(0,4,0,0)`, CVaR 2, stress loss 4, and variance 3.

[VarianceExample.agda](Examples/Portfolio/VarianceExample.agda) proves covariance `-7` between
the assets and the identity

```text
variance(L(w)) = 1 + 32 (w - 1/2)²
```

for every real weight. Nonnegativity of real squares proves global variance
minimization at equal weights without assuming independent asset returns.

## Expected-shortfall certificates

For a distribution `P` and a real multiplier `κ ≥ 1`, define

```text
positivePart(x) = max(x, 0)
stopLoss(x, t)  = positivePart(x - t)
F(L, t)        = t + κ E_P[stopLoss(L, t)]
```

The usual confidence parameter is related by `κ = 1/(1-confidence)`. The
formal input is `κ` and its lower-bound proof, avoiding a partial inverse.
This threshold formulation follows Rockafellar and Uryasev's treatment of
general loss distributions, including atoms. It does not identify CVaR with
naive conditioning on a strict exceedance of a quantile; that would mishandle
discrete mass at a threshold. See their
[2002 paper](https://sites.math.washington.edu/~rtr/papers/rtr187-CVaR2.pdf).

An admissible dual distribution `Q` satisfies `Q_i ≤ κ P_i` for every scenario.
The implementation proves

```text
E_Q[L] ≤ F(L, t)
```

directly, for every threshold. A concrete `OptimalityCertificate` supplies a
threshold, an admissible dual distribution, and equality of these two bounds.
The resulting value is a global minimum and independent of the certificate.
The nominal distribution is itself proved admissible, so the dual family is
inhabited and every threshold objective is bounded below by the mean loss.
A pointwise scenario bound supplies an upper certificate.

`IsCVaR L r` expresses the global minimum value and propositionally truncated
attainment. There is at most one such real value. General existence of an
optimizer for every real-valued finite dataset is **not** asserted here; the
worked examples construct their optimizers in full. No missing analysis
result is postulated or silently used.

[RiskLaws.agda](Risk/RiskLaws.agda) proves monotonicity, cash translation,
subadditivity, weighted convex bounds, and uniform perturbation bounds for
values supplied with `IsCVaR` evidence. It also proves that acceptance is
equivalent to `r ≤ budget`, and gives the corresponding univalence path.

## Executable budget control

`RiskControl.Report` contains a trial threshold, an admissible dual measure,
and verified rational bounds enclosing their objective values. `check` uses
decidable rational comparisons:

- If the upper bound is within the budget, return acceptance with a proof.
- If the budget is strictly below the lower bound, return rejection with a
  proof that no threshold can certify the budget.
- Otherwise return `inconclusive`.

Inconclusiveness can reflect coarse numerical bounds or a gap between the
chosen primal and dual witnesses. It is not an assertion that the portfolio
violates its budget. The four reduction checks in `Application.agda` establish:

| Input | Budget | Result |
| --- | ---: | --- |
| Equal-weight portfolio, exact report `[2,2]` | 2 | pass |
| Equal-weight portfolio, exact report `[2,2]` | 1 | fail |
| Concentrated asset A, exact report `[3,3]` | 2 | fail |
| Equal-weight portfolio, coarse report `[1,3]` | 2 | unknown |

These labels carry logical evidence via `check-sound`. The checker never
branches on equality, sign, or order of arbitrary Cauchy reals.

## Rebalancing, reserves, and economic identity

`Policy` combines a mean-loss limit, a stress limit, and a tail-risk limit.
It proves that a convex blend of two compliant portfolios satisfies the same
limits. `rebalance-certified` returns both the new fully invested allocation
and its policy evidence for every real weight in `[0,1]`.

For nonnegative holdings, asset-specific one-sided model error bounds combine
into the dot product of holdings and errors. Adding that reserve transports a
tail certificate to the actual model. Moving the threshold with a uniform
loss error gives coefficient **one** on the reserve, rather than `κ`.

The application adds a third instrument which wraps the equal-weight basket.
The allocations `(1/2,1/2,0)` and `(0,0,1)` have different holdings but identical
losses. Their proof-bearing policy records become equal in the economic
quotient. This netting result concerns scenario losses; operational details
such as transaction fees must be included in those losses to be covered.

## HoTT and Cubical Agda content

- The real numbers are the library's higher-inductive Cauchy reals. Constructive
  lattice maxima and stop losses work without decidable real order.
- Positive parts and fixed-threshold stop losses preserve the native Cauchy
  closeness relation through the existing HIT lifting of maximum.
- Cubical function extensionality turns pointwise loss equality into paths.
- A HIT **set quotient** identifies economically equivalent positions. Its
  equality is proved equivalent to pointwise loss equality, and its loss map
  is an embedding.
- The quotient is equivalent to the **image with propositionally truncated
  fibers** of the loss map. No representative selection or choice axiom is
  needed. Univalence gives a path between the two type presentations, with
  risk-preservation theorems for the equivalence.
- Order proofs and policy evidence are propositions. Two proofs do not create
  two different certified economic positions.
- Truncation hides threshold witnesses in acceptance and attainment while
  retaining all proposition-valued consequences.

The real rebalancing segment is not a cubical equality path between unequal
real numbers. Cauchy reals and the relevant portfolio types are sets; the
quotient and proof-transport techniques provide the pertinent HoTT structure.

## Scope and extension points

This is a checked finite mathematical system, with executable example checks.
It does not include market-data ingestion, floating-point numerical solvers,
a general CVaR minimizer, continuous-time trading, or probability calibration.
The supplied probabilities and error certificates are model inputs; proofs
establish consequences of those inputs, not their empirical accuracy.

Useful extensions are a verified numerical routine that produces `Report`
bounds, certificates generated by a rational linear-programming solver,
an explicit funding account, and scenario-label invariance. Any optimizer
used externally can remain outside the trust boundary: Agda can check its
threshold and dual witness with the existing certificate interface.

Transaction costs are now formalized as additional losses with prescribed
target holdings. Self-financing execution and probability calibration remain
outside the model. The dynamic layer is a finite two-stage evaluation and
certificate system, without a general dynamic trading optimizer.

The entire development stays under this example directory and its umbrella
module. It uses the project's `--safe --cubical` settings, with no new
postulates, unsafe pragmas, holes, or changes to foundational APIs.

## Validation

From the repository root, check reusable theory or the complete compatibility
umbrella, which also imports every canonical example:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Theory.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

The current validation record, including compiler status and scope of the
refactor, is in [PROGRESS.md](PROGRESS.md). All foundational results come from
the existing library; no additional analysis assumptions were introduced.
