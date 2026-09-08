# Constructive portfolio risk: progress

Latest completed work: [fifth-phase system correctness](#fifth-phase-completion-system-correctness-as-motivating-examples).
Start with [SYSTEM_GUARANTEES.md](SYSTEM_GUARANTEES.md) for the flagship broker
and trading statements. The canonical layout is in [STRUCTURE.md](STRUCTURE.md);
methodological sources are collected in [REFERENCES.md](REFERENCES.md).

## Objective and scope

Develop a checked finite-scenario financial mathematics example over the
library's higher-inductive Cauchy reals. Positive numbers represent losses;
negative numbers represent gains. All probabilities, holdings, and losses may
be arbitrary Cauchy reals, subject to explicit hypotheses.

The intended application combines portfolio aggregation, probability-weighted
expectation, worst-case stress risk, and expected-shortfall certificates. A
worked portfolio will demonstrate diversification and a certified risk budget.
Economic equivalence will use a cubical set quotient, so duplicate financial
representations have the same risk and acceptance properties.

## Foundation discipline

- Work stays in `Cubical/HITs/CauchyReals/Example/Financial` and its entry module.
- The project enables `--safe --cubical`; no new axioms, postulates, holes, or
  weakened options are planned. Missing analysis would be an explicit theorem
  parameter, never a hidden assumption.
- Finite maxima use constructive lattice operations, not decidable real order.
- A real line segment is not a cubical equality path between distinct reals.
- Existing untracked RealHomotopy and Spheres work is outside this task.

## Work log

### FX instruments and broker margin: design

The third phase responds to the request for client FX swap portfolios and
broker margin management. The working product assumption is a deliverable
near/far FX swap, with both currency principals and ordered dates retained.
An optional clarification about deliverable swaps versus rolling FX/CFDs was
asked while generic collateral and netting theory proceeded independently.

The design separates signed market marks, positive replacement claims,
scenario-dependent collateral value, client netting sets, and currency/date
funding obligations. Planned checked examples include matched market marks
with positive separate-client exposure; foreign collateral losing value in
the adverse exposure scenario; minimal cash margin calls; and zero aggregate
mark with nonzero settlement principal requirements. This is a specified
mathematical margin policy, not an assertion of regulatory compliance.

Instrument cashflows and exact spot/discount-factor changes are being built
locally. Parallel modules address minimal collateral top-ups, client-labelled
netting quotients, and currency-specific funding/settlement certificates.
Reference definitions are checked against BIS material; all proofs remain
constructive, safe, and confined to this example.

### FX broker: first checked milestones

`FXSwap`, `Margin`, `ClientNetting`, `Settlement`, `CounterpartyRisk`,
`MarginControl`, and `BrokerMargin` have passed individual checks with
exit 0 and no holes/metas/constraints/warnings. The instrument supports
ordered near/far dates and exact spot/discount-factor change attribution.
Margin is characterized as the least nonnegative cash top-up; an exact
rational report supports partial payments and minimal further requests.

The broker has two swaps (notionals 60 and 40) per client, held in opposite
directions. Its market marks cancel, but its four-scenario collateral-adjusted
exposure is `(15,68/5,5,2)`. Client cash calls are 15 and `68/5`; freezing
foreign collateral understates the second call by `8/5`. Mean exposure
`89/10`, worst exposure 15, and CVaR `143/10` have explicit proofs.

Source review verified broker signs, cashflow timing conventions, and exact
factor attribution. A comment was corrected to distinguish valuation-time
inputs for a settlement date from valuation at maturity. Documentation keeps
phase selection, curve calibration, collateral availability, and legal
netting as explicit scope boundaries. Local type inference in the broker
vector proof was resolved by specifying its finite-vector type.

The operational example is being connected to actual per-trade settlement
flows and executable payment checks. A further analytic extension will bound
every real quote in a joint spot/discount-factor box, since separate one-factor
stress tests need not cover their simultaneous adverse combinations.

### Further development: transaction costs, ambiguity, and sequential control

The next phase extends the checked foundation in three directions. Finite
probability mixtures and their extreme-model risk bounds will represent
uncertainty about probabilities. A coherent risk interface and two-stage
composition will express sequential risk control. Proportional transaction
costs will be included in losses rather than ignored by economic netting.

The practical targets are a robust allocation selected by an ambiguity set
and a rebalancing example in which fees change the optimizer, including a
proved no-trade regime at sufficiently high fees. New work continues to use
safe Cauchy reals without missing-analysis postulates. Earlier results and
their validation record below describe the completed first phase.

### Further development: checked milestones

Eight new modules have passed individual checks with exit 0:
`TransactionCosts`, `Rebalancing`, `TradeDecision`, `Ambiguity`,
`RobustAllocation`, `DynamicRisk`, `DynamicAmbiguity`, and
`ExecutionEquivalence`. Their first umbrella integration checked completely;
a selective module-export warning was then corrected using Agda's explicit
`module` import syntax.

The fee optimizer is proved over all real weights and thresholds. It chooses
three quarters in A when `0 ≤ s ≤ 4`, and no trade when `s ≥ 4`. Rational
inputs give a certified executable selector and complete exact budget
decisions. The ambiguity example has the unique global optimum `w=9/20`
with worst expected loss `7/5`; the strict tradeoff with stress loss `12/5`
is also checked. A naming collision in its final uniqueness proof was fixed
locally before its successful check.

The dynamic layer constructs coherent two-stage risk, time consistency,
node-budget certificates, and the finite expectation tower formula. Independent
conditional mixtures have a sound root-capital bound. A separate example
computes coupled risk 2 and rectangular risk 4. The execution quotient has
a necessary and sufficient fee-invariance condition for representative-
preserving descent from raw economic classes, and a checked counterexample
with net CVaR 3 versus 5.

Read-only cross-reviews found no mathematical errors. They clarified that
CVaR-only trades do not automatically satisfy stress controls; fees require
an external reserve or a future funding model; total-loss classes do not
retain all future trading state; and the general dynamic ambiguity result
is soundness, not an exact supremum representation. These boundaries are
recorded in `EXTENSIONS.md`. A further stress-constrained trading example
is being implemented to connect two of the portfolio controls directly.

### 2026-09-07: initial design

Inspected the foundational real, ordered ring, and lattice APIs. They suffice
for the initial finite model without new analysis assumptions. Parallel work
has started on positive parts/stop loss, nonempty finite worst-case risk, and
economic set quotients. Main work is finite sums, probability, portfolios, and
integration into the worked example. Validation uses `agda-codex` exclusively.

### Checked finite risk foundation

`Finite`, `Probability`, `Shortfall`, `WorstCase` (initial core),
`EconomicEquivalence`, `ExpectedShortfall`, and `Portfolio` have each passed
`agda-codex` with exit code 0 and no holes, metas, constraints, or warnings.
The finite layer includes finite Fubini, allowing expected portfolio losses
to be computed from asset means. Allocation blending preserves nonnegativity
and total capital. Asset-specific model errors produce an explicit reserve.

The expected-shortfall layer proves weak duality directly: if a probability
vector Q satisfies Q_i ≤ κ P_i, then E_Q[L] ≤ t + κ E_P[(L-t)⁺] for every t.
A matching primal/dual certificate proves a global minimum. `IsCVaR` records
the global lower bound and propositionally truncated attainment; its value
is unique. No general optimization or quantile existence theorem is assumed.

Cubical results include effective economic quotient paths, an equivalence
with the image of the loss map using truncated fibers, univalence between these two
presentations, and proof-independent risk certificates. Positive parts and
stop losses preserve the native Cauchy-real closeness relation.

### Validation environment

The sandbox initially prevented the wrapper from measuring system memory.
It returned 75 before starting Agda, with no RAM or peak-RSS measurement.
The user enabled full access, after which root checks worked with the memory
guard intact. Child agents retained the old sandbox, so checks are centralized
through the root agent. This was an environment refusal, not proof memory
exhaustion.

### Checked application and risk laws

`RiskControl`, `Policy`, and `Application` passed with exit 0. The checker
reduces to pass for the balanced portfolio at budget 2, fail at budget 1,
fail for concentrated asset A at budget 2, and unknown for a coarse `[1,3]`
report at budget 2. `check-sound` attaches mathematical evidence to the labels.

The policy combines expected loss ≤ 1, stress loss ≤ 2, and tail risk ≤ 2 in
the example. General convex rebalancing preserves all three limits. The
application constructs direct and wrapped-basket allocations and proves their
certified economic classes equal. A model-error reserve transports acceptance
with coefficient one on uniform loss errors.

`Diversification` passed with exact means 1, CVaRs 3/3/2, and worst losses
6/6/2 for A/B/balanced. The dual measure `(1/2,1/2,0,0)` proves a global
lower bound 2 for every real allocation weight and threshold. The stress
budget uniquely forces equal weights. A distinct quarter allocation also
has optimal CVaR 2 but worst loss 4, demonstrating why the stress control adds
information and why optimizer uniqueness should not be assumed.

The extended `WorstCase` and `RiskLaws` passed with exit 0. Worst-case risk
has nonnegative real homogeneity and weighted bounds. CVaR values, whenever
supplied with `IsCVaR` evidence, satisfy monotonicity, cash translation,
subadditivity, weighted convex bounds, and perturbation estimates. Acceptance
is equivalent to the CVaR value being within budget; univalence also exposes
this as a path between policy types. These proofs eliminate truncated
attainment only into propositions.

### Completed dispersion comparison and review

`Variance` and `VarianceExample` passed with exit 0. General results include
centered mean zero, nonnegative variance, cash invariance, square scaling,
covariance symmetry, and the two-asset variance formula. The example gives
variance 9 for both assets, covariance -7, balanced variance 1, and quarter
variance 3. The identity `Var(L(w)) = 1 + 32 (w - 1/2)²` proves a global
variance optimum for every real weight, including short positions.

A separate read-only review of `Application`, `Policy`, `RiskControl`, and
the README found no mathematical defects. It caught an overstatement in an
application comment: a model error certificate gives an upper capital
allowance, not necessarily an exact change in the minimum risk. The comment
was corrected and `Application` rechecked successfully.

The README explains the finite model, the discrete-tail convention, all
example values, the executable checker, HoTT techniques, and limitations.
The conceptual reference is Rockafellar and Uryasev, *Conditional Value-at-Risk
for General Loss Distributions* (2002), available from the author's
[University of Washington page](https://sites.math.washington.edu/~rtr/papers/rtr187-CVaR2.pdf).
All local theorems are proved in Agda; literature is explanatory background.

## First-phase validation

First-phase final command, run after that phase's last Agda edit:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

Result: **exit 0**, checked completely with **0 holes, 0 unsolved metas,
0 constraints, and 0 warnings**. The umbrella imports all 14 component
modules, including the three worked application/example modules. There are
15 Agda modules and 2,077 source lines including comments and the umbrella.
An explicit source scan found no postulates, holes, unsafe termination
pragmas, or weakened checking options.

## First-phase limitations and extension points

- No general optimizer/quantile existence theorem for every arbitrary real
  finite dataset is claimed. Every optimizer used in the examples has an
  explicit checked certificate.
- Numerical `Report` bounds are supplied with proofs; producing them from
  general Cauchy approximations remains an extension point.
- No general linear-program solver, floating-point extraction, market-data
  connection, transaction-cost calibration, or continuous-time model is
  included.
- Economic identity means equality of the modelled loss profiles. Extra
  operational costs belong in the model before this quotient is applied.
- Native constructive reals, finite computations, truncations, and existing
  continuity lemmas sufficed. **No missing analysis assumptions were needed.**

All new work is confined to the requested `Example/Financial` directory and
`Example/Financial.agda`. Existing RealHomotopy and Spheres work was preserved.

## Second-phase completion and validation

The follow-up request is implemented with **nine additional Agda modules**.
The final addition, `StressConstrainedTrade`, couples fee-aware CVaR
optimization to a raw scenario stress cap. For every `s ≥ 0` and
`2 ≤ c ≤ 4`, its fully invested long-only allocation has A weight `(c+2)/8`,
raw stress `c`, net stress `c+s(6-c)/8`, and globally minimal net CVaR
`2+s(6-c)/8` among all feasible real weights. At fee 1 and cap 3, it gives
weight `5/8`, CVaR `19/8`, and net stress `27/8`. Every feasible competitor
is proved to fail tail budget `9/4`. The no-trade position is infeasible
for all the stated caps.

The final source review found no mathematical defects. One comment was
made precise at zero fees: net stress includes the fee and can equal raw
stress. Documentation review clarified rational budget inputs and the
economic image's propositionally truncated fibers. The extension guide
records formulas, API entry points, exact examples, references, and scope.

After the last Agda edit, both the affected `StressConstrainedTrade.agda`
and the complete umbrella were checked with `agda-codex`. Final umbrella
command:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

**2026-09-07 20:27:05 UTC: exit 0**, status `checked`, with **0 holes,
0 unsolved metas, 0 constraints, and 0 warnings**. Umbrella source SHA-256:
`cb87d32bd7faaebc464fb165d9c70d61986ac071a1975089ac2727aad50bd25c`.

The umbrella imports every component: **24 Agda modules and 3,999 source
lines**, including comments and the umbrella. A source scan found no
postulates, explicit holes, unsafe termination/positivity/universe pragmas,
or weakened checking flags. Local documentation links resolve, and no Agda
source has trailing whitespace. Executable examples check by reduction
inside the source modules, including fee selection and rational budget
acceptance/rejection. No floating-point test substitutes for those proofs.

### Current limits and useful next steps

- Funding feasibility remains outside the fee model. Costs are additional
  same-horizon losses; they do not reduce target holdings.
- The executable optimizer specializes to the supplied two-asset market.
  General certified rational linear programming and automatically produced
  approximation reports remain useful future work.
- Probability ambiguity and fees are both developed, but there is no joint
  optimizer combining model ambiguity, transaction fees, and every policy
  constraint. The stress-constrained example combines fees and two controls.
- Sequential risk uses fixed finite two-stage trees. General rectangular
  mixture results are upper bounds, not a full dual representation theorem;
  no generic multistage trading optimizer is claimed.
- Execution classes describe current total loss. They need not retain the
  holdings information required to calculate later transaction costs.
- No general arbitrary-real CVaR existence theorem is assumed, and no new
  analysis hypotheses were needed for any completed proof.

All changes remain in the requested example directory and its umbrella.

## Third-phase completion: FX swaps and broker margin

The FX instrument and broker-margin request is implemented in **ten new
Agda modules**: `FXSwap`, `FXBounds`, `Margin`, `MarginControl`,
`ClientNetting`, `CounterpartyRisk`, `Settlement`, `BrokerMargin`,
`BrokerOperations`, and `JointFXMargin`. The product assumption is a
deliverable near/far FX swap. The guide is [FX_BROKER.md](FX_BROKER.md).

The four-scenario broker workflow now includes exact rational call reports,
decidable payment statuses, updated reports after partial receipt, and
minimal further cash requests. Client B paying 12 leaves `8/5`; receiving
that further amount clears its modeled residual. After both clients pay,
separate-client residual exposure and every admissible default/recovery
severity loss are zero for those scenarios. Total segregated client calls
are `143/5`; the aggregate broker exposure maximum 15 and exposure CVaR
`143/10` are separate diagnostics.

The actual four far-leg payment instructions come from the 60/40 swaps and
their reversals. Their far dates are proved to be 30. Net cashflows vanish,
but gross funding requires 100 domestic and 100 foreign units, with base
value 200 at conversion factors `(1,1)`. Zero gross funding is impossible.
Margin collateral is not implicitly reassigned to these payment obligations.

The analytic extension bounds **every Cauchy-real quote** with spot in
`[4/5,6/5]` and both effective discount factors in `[9/10,1]`. The same
portfolios then require sharp cash top-ups 25 and `108/5`. Explicit joint
states attain both requirements. In particular, B's worst claim and lowest
collateral value occur together, making its bound exact. Coverage for the
whole box is equivalent to meeting those capital bounds, with a univalence
path for policy transport. The old payments 15 and `68/5` are rejected by
the new reports and require another 10 and 8. Original scenario membership
and portfolio/valuation links are proved explicitly.

Read-only reviews found no mathematical or numerical defects. Clarifications
recorded in the guide include reference-state factors in the exact change
formula, the difference between separate margin calls and broker capital
statistics, and the scope of finite reports versus whole-box certificates.
One local binder was renamed because it collided with the payment-status
constructor `covered`. All affected sources were rechecked successfully.

### Final third-phase validation

After the last Agda edit, the affected broker module and the full umbrella
were checked with the required wrapper. Final command:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

**2026-09-07 21:00:10 UTC: exit 0**, status `checked`, with **0 holes,
0 unsolved metas, 0 constraints, and 0 warnings**. Umbrella SHA-256:
`74fae6f6a8b2a260f65a3bec081cdb9635dae29c79e08321201a9077b90bd44e`.

The complete development now has **34 Agda modules and 6,000 source lines**,
including comments and the umbrella. Every component is imported by the
umbrella. A source scan found no postulates, explicit holes, unsafe
termination/positivity/universe pragmas, or weakened checking flags. Local
Markdown links resolve; Agda sources have no trailing whitespace. Payment
decisions compute by rational comparison and carry their checked real-valued
coverage or insufficiency evidence.

No missing analysis results or additional foundational assumptions were
needed. The valuation model, quote bounds, collateral eligibility and
availability, client netting sets, severity inputs, settlement states, and
funding balances remain explicit financial model inputs. No market-data
calibration, legal enforceability assessment, actual cash collection,
regulatory margin compliance, or generic arbitrary-real pricing/optimization
algorithm is claimed. Native currency funding and settlement-principal risk
remain distinct from closeout-margin certificates.

All work remains under the requested example directory and its umbrella;
existing RealHomotopy and Spheres work is preserved.


## Fourth-phase completion: organization, shared theory, and references

The request to organize the Financial folder is implemented. The existing
33 flat implementation modules moved into `Core`, `Risk`, `Portfolio`,
`Dynamic`, `Instruments`, `Margin`, `Settlement`, and topic-specific `Examples`
folders. Their old paths remain thin compatibility modules. Six concrete
blocks formerly mixed into theory are separate example modules. The new
`Theory.agda` entry point exports only reusable theory; `Examples.agda`
provides public qualified application namespaces. The original umbrella
preserves its public names and imports both new entry points.

### Shared definitions and generalizations

- `Core/Vectors` provides universe-polymorphic two-, three-, and four-coordinate
  constructors. `Examples/CommonScenarioData` owns fair/uniform probabilities,
  tail level, and admissible dual weights. Old example names remain aliases.
  Broker modules no longer depend on the diversification example for this data.
- Nonnegative interval membership and product bounds moved from FX-specific
  code to `Core/Bounds`; finite-sum negation moved from settlement to `Core/Finite`.
- `Risk/Shortfall` contains shared upper-bound, exact-evaluation, and
  zero-threshold lemmas. `Risk/FiniteShortfall` supplies the positive-part and
  stop-loss sum inequalities used in both client netting and settlement.
- `worstCase-exact-at` packages upper bounds with an explicitly supplied
  attaining index. The stress-constrained portfolio uses it. No algorithm for
  selecting an argmax of arbitrary Cauchy-real data is asserted.
- `Margin/Scenario` expresses coverage for arbitrary admissible state types.
  `MarginCertificate` records a least nonnegative cash requirement;
  `BindingScenario` supplies a state with the raw difference `X(s)-C(s)=m`.
  The binding witness yields leastness and coverage equivalence for all real
  budgets. Record/equivalence APIs are universe polymorphic; univalence paths
  are provided for small state and admissibility types.
- Finite margin instantiates that interface, while the joint FX example uses
  explicit corner witnesses. Its existing all-real-budget statements retain
  their types and strength. `margin-postCash` generalizes the payment update
  to any nonnegative real payment; the rational controller delegates to it.
- Rebalancing reuses the existing cash-translation theorem for its net CVaR
  objective. Worked numerical outcomes and rational decision reductions remain
  unchanged and check in their new locations.

### References and documentation

`REFERENCES.md` maps nine primary sources to the financial methods: Markowitz;
Rockafellar–Uryasev; Boyd and coauthors; Ben-Tal–Nemirovski; Shapiro;
Epstein–Schneider; BIS on FX swap funding; BCBS on FX settlement; and BCBS–IOSCO
on collateral methodology. All 17 example/data modules contain specific source
notes. The guide documents tail-parameter and turnover conventions and clearly
separates synthetic inputs from methodological justification. It records the
physically settled FX exclusion from the general BCBS–IOSCO margin framework;
that source is not used to claim regulatory validation of the toy cash calls.

`STRUCTURE.md` gives canonical imports, shared interfaces, sign/unit conventions,
and the complete old-to-new module map. README, extension and FX guides now
link to implementations and separate extracted demonstrations.

### Compatibility audit and final validation

An external importing module caught a namespace regression that umbrella
compilation alone did not expose: a bare `import ... as Name` is not a public
replacement for the former nested example module. The wrappers now export
explicit nested modules with public imports. Inherited namespaces forward the
original module, preserving their identity and avoiding ambiguous exports.
The expanded compatibility check verifies all five extracted nested namespaces,
two inherited namespaces, execution APIs, original constructor type expectations,
dual admissibility, the root umbrella's example access, and every new example
namespace. It passes exit 0; this targets refactor-sensitive APIs rather than
claiming exhaustive signature equivalence for every exported declaration.

Final checks after the relevant final source edits:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Theory.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

- **Theory: 2026-09-07 21:18:45 UTC, exit 0**, status `checked`.
  SHA-256: `d53e01405d960767a04b8d44d6e9ae4a072006936db85071718906ddd11de402`.
- **Full umbrella: 2026-09-07 21:22:13 UTC, exit 0**, status `checked`.
  SHA-256: `412afca06dcb966bf9d9e6e12e6c29f187a62a57550c079686594e5532655490`.
- Both report **0 holes, 0 unsolved metas, 0 constraints, and 0 warnings**.
  The expanded external compatibility check also passes at 21:22:13 UTC.

There are now **44 canonical implementation modules, 33 compatibility wrappers,
and 3 entry points**, totaling **80 Agda files and 6,614 source lines**, including
comments. Import-graph inspection confirms that the full umbrella reaches every
module, reusable theory reaches no example or legacy wrapper, and no canonical
implementation imports a flat compatibility path. Local Markdown links and
source-reference anchors resolve. No trailing Agda whitespace, new postulates,
holes, unsafe pragmas, or weakened checking options were introduced.

The refactor stays within the Financial directory and its umbrella. Existing
RealHomotopy and Spheres work remains untouched. General CVaR optimizer
existence, empirical calibration, and operational/legal assumptions retain
exactly the explicitly stated scope in the financial guides.


## Fifth-phase completion: system correctness as motivating examples

The request for large, practically meaningful correctness statements is
implemented in four new modules. Three separate agents developed the generic
client workflow, receipt-history theory, and complete trading solver; the main
agent integrated the broker book, executable funding gate, sequential receipts,
and worked scenarios. Independent cross-reviews checked both financial scope
and constructive proof discipline.

### Flagship broker result

`Examples/FX/BrokerGuarantees.agda` composes the actual 60/40 swap portfolios,
joint real spot/discount box, currency-sensitive client collateral, exact margin
certificates, rational payment decisions, and actual gross far-leg settlement
instructions. `broker-ready≃requirements` identifies program success with
universal client coverage and gross funding in both native currencies.
`broker-end-to-end` constructs a `BookGuarantee` with coverage of trade-by-trade
claims, zero modeled closeout loss for every scenario-dependent admissible
severity, and sufficient gross settlement funding.

`history-end-to-end` transports this whole-book guarantee to collateral produced
by arbitrary per-client receipt folds over the entire FX state domain.
`history-reports-agree` connects iterative `recordPayment` reports to the
universal workflow's outstanding requests. Equal per-client receipt totals
preserve the full combined decision by `history-batching-invariant`.

The worked receipts A:(15,10) and B:(68/5,8), with funding (100,100), compute a
successful result. The old receipts (15,68/5) fail. New requests are exactly
(10,8), and `eighteen-is-least-further-cash` proves that every nonnegative REAL
further-payment vector covering all actual swap claims has total at least 18.
`request-cycle-ready` proves that receipt of computed requests completes the
margin gate for any nonnegative prior client balances, with sufficient funding.

Two deliberate control failures are checked by reduction: the full cash total
233/5 credited entirely to A fails client coverage, and correct client payments
with (200 domestic,0 foreign) funding fail the native-currency requirement.
Separate equal-total/equal-base-value proofs establish why aggregate values
cannot replace these obligations.

`closeout-and-principal-zero` additionally sums modeled closeout and settlement
principal losses across the book. Its zero-loss conclusion requires the separate
`AtomicBook` idealized delivery law. The broker check does not establish that
law or actual settlement completion.

### Reusable scale and trading completeness

`Margin/Workflow.agda` supports any finite client count and an arbitrary small
admissible scenario domain. The checker is sound and complete relative to exact
supplied `MarginCertificate`s; failure identifies a client and refutes its
universal coverage. Success yields zero aggregate residual and zero closeout
loss under every scenario-dependent admissible severity. Computed requests are
sufficient and componentwise/total minimal against arbitrary nonnegative real
further payments. Client collateral remains separate throughout.

`Margin/PaymentHistory.agda` processes arbitrary finite lists of nonnegative
rational receipts. Pure collateral operations are universe-polymorphic in the
scenario domain. Finite exact-report processing maintains the total/outstanding
invariant, and complete reports agree after transport under batching, equal
totals, concatenation and batch swapping. Coverage and zero remaining margin
are each equivalent to a sufficient total. Insufficient actual receipts cannot
produce a covered verdict. Client-family lifts are also proved.

`Examples/Portfolio/TradingGuarantees.agda` gives a complete solver for the
existing proportional-fee CVaR problem. `solver-pass≃feasible` identifies success
with truncated existence of ANY signed real holding vector whose sum is one
and whose actual `TransactionCosts.allInLoss` meets the budget. Success returns
a normalized long-only allocation with actual fee/loss links, an exact rational
optimal CVaR and global lower bounds. Failure rules out every real competitor.
Fee1/budget2 is globally infeasible; fee1/budget9/4 returns (3/4,1/4) with actual
fee1/4. Truncated feasibility can reconstruct the computed canonical trade;
no hidden witness is selected from truncation.

### Framing, reviews and validation

[SYSTEM_GUARANTEES.md](SYSTEM_GUARANTEES.md) is now the main motivating guide,
with the broker theorem first, a component diagram, executable scenarios,
quantifier/scope explanations, and a named theorem map. README, FX and extension
guides lead readers to these statements. The structure/reference guides link
the new modules to reusable theory and financial methodology. `Theory.agda`
exports the new workflow/history APIs in public qualified namespaces;
`Examples.agda` exports both flagship applications.

Independent reviews found no remaining correctness issue. An external temporary
edge-case module also checked zero clients over an inhabited infinite real
scenario domain, zero margin for arbitrary client counts with surplus collateral
and no binding state, and overpayments producing pass with zero requests. Its
final check at **2026-09-07 21:41:13 UTC** returned **exit0 with no holes, metas,
constraints or warnings**. Reviews confirmed that the trading competitor domain
includes shorts and that all truncation eliminations target propositions.

Final relevant source checks:

| Module | Checked at (UTC) | Result |
| --- | --- | --- |
| `Margin/Workflow` | 2026-09-07 21:33:47 | exit0, checked |
| `Examples/Portfolio/TradingGuarantees` | 2026-09-07 21:34:26 | exit0, checked |
| `Margin/PaymentHistory` | Final generalized source checked before broker integration | exit0, checked |
| `Examples/FX/BrokerGuarantees` | 2026-09-07 21:39:43 | exit0, checked |
| `Theory.agda` | 2026-09-07 21:41:29 | exit0, checked |
| `../Financial.agda` | 2026-09-07 21:41:30 | exit0, checked |

All report **0 holes, 0 unsolved metas, 0 constraints, and 0 warnings**.
The last two commands, after the final entry-point edits, were:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Theory.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

Theory SHA-256:
`ddedfc8ebf03d58ae0814d9d41ca6aa59e6c7737fb31632dfddf5c8c2223d21e`.
Full umbrella SHA-256:
`412afca06dcb966bf9d9e6e12e6c29f187a62a57550c079686594e5532655490`.
Broker guarantee source SHA-256:
`8e62c8ac89893b43823bf09e5c7a0d8d33b5defad3f2a16defab137f74bb55f5`.
The umbrella source hash is unchanged because the new modules enter through
its existing `Theory` and `Examples` imports; its dependency closure was rechecked.

The complete development has **84 Agda files and 7,813 source lines**:
48 canonical implementations, 33 compatibility wrappers, and 3 entry points.
Every module is reached from the full umbrella. Theory still imports neither
examples nor compatibility modules. Every concrete example has reference notes;
local Markdown links resolve, and the proof-discipline/whitespace scan is clean.

The general theorems scale in client count, scenario domain, real-valued
competitors and receipt-history length. No production throughput claim is made.
Exact model certificates, receipt provenance, custody/enforceability, available
separate currency balances and the fixed valuation snapshot remain input
conditions. No withdrawal, duplicate-event protection, real settlement protocol,
self-financing trading ledger, or empirical calibration is silently inferred.
No postulates, unsafe flags, new analysis assumptions, or foundational edits were
needed. Existing RealHomotopy and Spheres work remains untouched.

## 8 September 2026 — separate generic broker progression

Added [Broker/](Broker/README.md), an eight-stage development of margin machinery
without concrete scenarios: cash accounts, scenario reports, client netting,
inventory-backed collateral, identified receipts, revaluation, minimum transfers,
and a composed controller. Three agents developed and reviewed independent
components. [The local progress record](Broker/PROGRESS.md) includes the theorem
map, review conclusions, final source hashes, and compiler outcomes.

The final `controller-correct` theorem links a sufficient margin report and
certified revaluation bounds to an executable call plan and actual receipt
journal. New receipts meeting each client's request yield universal per-client
residual bounds and aggregate closeout-loss bounds by transfer tolerances.
Zero tolerance gives full client coverage and zero modeled loss for every
severity. Additional theorems prove modeled resource backing and equality of
the entire ledger/certificate pair after receipt replay.

This adds identified-event duplicate suppression to the earlier anonymous
payment-history theory. IDs and payloads are fixed by the catalog; distinct IDs
must represent distinct actual receipts. The older progress entry's lack of
such protection describes that earlier theory, not the new journal. Additional
journal cash must be separate from base inventory. Conservative call failure
means an unfulfilled plan and does not assert economic deficiency.

[Broker/REFERENCES.md](Broker/REFERENCES.md) grounds the stages in BCBS FX guidance,
BCBS–IOSCO margin concepts, robust optimization, margin/gap-risk literature,
FINOS event identity, and application-level duplicate suppression. The new
[Broker.agda](Broker.agda) entry point is exposed through `Theory.Broker`.

Final checks after the last Agda edits:

| Module | UTC time, 7 September 2026 | Result |
| --- | --- | --- |
| `Broker/Stage08Controller.agda` | 22:11:36 | exit 0 |
| `Broker.agda` | 22:14:03 | exit 0 |
| `Theory.agda` | 22:14:25 | exit 0 |
| `../Financial.agda` | 22:14:52 | exit 0 |

All checked with **0 holes, 0 unsolved metas, 0 constraints and 0 warnings**.
Eight stage modules add 1,482 source lines; the whole development now has
93 Agda files and 9,327 lines. The full umbrella reaches every module. The broker
progression imports neither worked examples nor compatibility shims, and the
theory/example dependency boundary remains intact. No postulates, unsafe options,
new analysis assumptions, or foundational edits were needed.

## 8 September 2026 — Broker2: one engine evolved for presentation

Added [Broker2/](Broker2/README.md), seven successive versions of the same
quote/receive engine, with a [28-minute quant developer speaker guide](Broker2/PRESENTATION.md)
and [source/review record](Broker2/PROGRESS.md). Each successor imports its
predecessor and proves the precise relationship between old and new behavior.
The progression adds client books, stress profiles, rational execution, transfer
tolerances, identified receipts, and certified revaluation. It introduces no
concrete scenarios or calibrated data.

A generic rational input factory computes exact initial reports. Actual receipt
processing updates a certified incremental report, including after partial
payments. The final operation returns the next state, an equality proving that
state is the receipt result, a report for that state, and an assessment. Its
success guarantee covers every supplied stress/client and all modeled
severity-weighted losses; zero transfer tolerance restores full coverage and
zero modeled loss. Receipt replay preserves the state plus its safety proof.

Three agents contributed rational execution, independent review, and the
presentation narrative. Reviews confirmed the incremental-cash convention,
conditional exactness, projection/refinement scope and conservative-failure
semantics. The earlier broker progression and numerical examples remain
independent.

Final `agda-codex` entry-point checks on 8 September 2026 UTC: `Broker2.agda`
06:21:10, `Theory.agda` 06:22:17, and the full `Financial.agda` umbrella 06:22:59.
All returned **exit 0 with zero holes, metas, constraints and warnings**.
The seven new version modules have 857 lines; the whole development now has
101 Agda files and 10,213 lines. All modules are reachable, all new successors
import their predecessor, and Theory imports no worked examples. No postulates,
unsafe options, missing analysis assumptions or foundational edits were added.


## 8 September 2026 — relational refinement of Broker2

[Broker2/Pipeline](Broker2/Pipeline/README.md) implements the final abstract
margin engine with typed trade/client/receipt rows, functional valuation lookup,
selection and grouped sums. Generic `get`, `keyMask`, aggregation and their laws
were added under `Experiments/Relation`; its existing Base was preserved.

The implementation returns ordinary state, remaining amounts, call rows and a
status. Separate proofs certify those actual outputs and refine them to V07,
including the broker-wide bounds over all supplied stresses and severities.
Initial reports and conservative revaluation reserves are computed; partial
receipts preserve valid reports, and replay/order preserve certified states at
a fixed valuation. No concrete numerical scenario or postulate was introduced.

Sixteen final `agda-codex` checks passed with exit 0 and no holes, metas,
constraints or warnings, including Theory and the full financial umbrella.
The full import closure contains 112 Agda sources and 11,375 lines. All are
reachable. See [Pipeline/PROGRESS.md](Broker2/Pipeline/PROGRESS.md) for exact
checks, hashes, independent review and scope, and the updated Broker2
presentation/reference guides for motivation.
