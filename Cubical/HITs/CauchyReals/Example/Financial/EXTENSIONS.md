# Fees, model ambiguity, and sequential capital

The second development phase adds execution costs, optimization under uncertain
probabilities, and two-stage risk evaluation. All values still live in the
library's higher-inductive Cauchy reals. No additional analysis assumptions
were needed. The examples answer different management questions; their risk
criteria and budgets are stated separately below.

The [README](README.md) describes the shared four-scenario market and the
original CVaR, stress, variance, and economic-quotient foundations.

The [reference guide](REFERENCES.md) gives primary sources for proportional
transaction costs, CVaR, robust optimization, and recursive multiple priors.
The [structure guide](STRUCTURE.md) separates their reusable interfaces from
the numerical examples.

The new [TradingGuarantees](Examples/Portfolio/TradingGuarantees.agda) supplies
the large correctness statement for the fee-aware system: its success is
equivalent to existence of an acceptable signed real fully invested portfolio.
Its failure rules out every such competitor, while success returns an allocation
with proved actual proportional fees, accepted all-in loss, and global optimality.
See the [motivating examples](SYSTEM_GUARANTEES.md#trading-complete-feasibility-against-real-portfolios)
for the precise scope and comparison with the separate stress constraint.

## An executable trading rule with fees

[TransactionCosts.agda](Portfolio/TransactionCosts.agda) defines proportional costs by

```text
cost(rates, old, target) = Σᵢ ratesᵢ |targetᵢ - oldᵢ|
allInLossᵢ               = cost + portfolioLossᵢ(target)
```

The generic proofs establish nonnegativity for nonnegative rates, zero cost
for no trade, symmetry, the triangle inequality, monotonicity in rates, and
convexity in target holdings from a fixed starting position. Adding the cost
shifts mean loss, maximum loss, and certified CVaR by exactly that cost.
Threshold/dual certificates and budget acceptance are transported explicitly.
Convex combinations of targets have a proved bound on CVaR budgets including
costs.

In [Rebalancing.agda](Examples/Portfolio/Rebalancing.agda), the manager starts with all capital in
asset A and chooses holdings `(w, 1-w)`. Each asset has rate `s/2`, so charging
both trade legs gives

```text
fee(s,w) = s |1-w|
netLoss  = fee(s,w) + w A + (1-w) B
```

This equality is proved against the generic transaction-cost implementation.
The nonnegative parameter `s` is an abstract fee per traded weight in the
example's loss units, not a quoted percentage or a calibrated market rate.

For every Cauchy-real fee satisfying the indicated inequalities, the following
global optima are proved. Competitors include **every real weight** and every
real trial threshold, including signed holdings outside `[0,1]`.

| Fee regime | Selected A/B weights | Minimum CVaR including fees |
| --- | --- | --- |
| `0 ≤ s ≤ 4` | `3/4, 1/4` | `2 + s/4` |
| `4 ≤ s` | `1, 0` (no trade) | `3` |

The proof combines two admissible dual lower bounds for raw CVaR with a
supporting bound for the absolute-value fee. It does not require a complete
piecewise evaluation of CVaR at every competing weight. At `s=4` both stated
choices attain 3; no uniqueness claim is made, including at `s=0`.

[TradeDecision.agda](Examples/Portfolio/TradeDecision.agda) turns this result into

```agda
chooseTrade : (s : ℚ) → 0 ℚ.≤ s → CertifiedTrade (rat s)
```

The returned record contains a real weight, proof that it is in `[0,1]`, an
attained CVaR value, and a lower-bound proof for every competitor. The
`chosenAllocation` adapter returns the ordinary fully invested `Allocation 2`
used by the earlier portfolio layer. Rational comparison selects the fee
regime; arbitrary real order is never decided.

The exact rational optimum also makes `checkChosenBudget` a complete decision
procedure for rational budgets on this selected portfolio: it returns either
acceptance or a proof of nonacceptance. Its domain requires nonnegative fees.
Checked computational reductions include:

| Fee `s` | Selected A weight | CVaR including fees | Budget | Decision |
| ---: | ---: | ---: | ---: | --- |
| 1 | 3/4 | 9/4 | 2 | fail |
| 1 | 3/4 | 9/4 | 9/4 | pass |
| 5 | 1 | 3 | 3 | pass |
| 4 | 3/4 | 3 | 3 | pass |

For fee 1, fully rebalancing to equal weights would instead have CVaR `5/2`
and fails budget `9/4`. The unconstrained selected trade optimizes CVaR alone:
its raw maximum loss is 4, and its maximum loss including fees is `17/4`.
The original combined policy limits do not automatically hold for this trade.

## Minimize CVaR while enforcing a stress cap

[StressConstrainedTrade.agda](Examples/Portfolio/StressConstrainedTrade.agda) adds an explicit
constraint on the **raw** market loss: `worstCase(L(w)) ≤ c`. For every
real cap `2 ≤ c ≤ 4` and fee `s ≥ 0`, it constructs the optimal allocation

```text
A weight          = (c+2)/8
B weight          = (6-c)/8
raw scenario loss = (c, 4-c, 0, 0)
fee               = s(6-c)/8
minimum net CVaR  = 2 + s(6-c)/8
net stress        = c + s(6-c)/8
```

The raw stress constraint bounds any competitor's A weight by `(c+2)/8`.
This forces a lower bound on its trading fee. Combining that bound with the
universal raw-CVaR lower bound 2 proves the displayed constrained optimum.
`IsConstrainedOptimum` bundles feasibility, an attained CVaR value, and the
comparison against all feasible real weights and all real thresholds.
`capAllocation` supplies the fully invested long-only holdings.

At fee 1 the cap gives a visible capital tradeoff:

| Raw stress cap | Optimal A weight | Fee | Minimum net CVaR | Net stress |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 1/2 | 1/2 | 5/2 | 5/2 |
| 3 | 5/8 | 3/8 | 19/8 | 27/8 |
| 4 | 3/4 | 1/4 | 9/4 | 17/4 |

The middle row has dedicated checked numerical theorems. Budget `19/8` is
accepted, while budget `9/4` is impossible for **every** portfolio meeting
raw stress cap 3. The other rows are substitutions in the proved general
formulas and agree with the earlier balanced and partial-trade values.

The initial all-A position has raw stress 6, so no trade is infeasible for
all these caps. A large fee therefore does not remove the required trade
when the stress cap is mandatory. Net stress is reported separately: it
includes fees and exceeds the raw cap whenever the fee is positive.

## Allocation under uncertain scenario probabilities

[Ambiguity.agda](Risk/Ambiguity.agda) takes a nonempty finite family of real
distributions and defines risk as the maximum of their expected losses.
The expectation of any real convex mixture equals the corresponding mixture
of model expectations. Consequently, bounding all listed models is
**equivalent** to bounding all their mixtures. An additional formulation
covers arbitrary finite selections of the original labels, including
repetitions. Dirac weights prove the converse without selecting a maximizing
real value.

The resulting risk satisfies monotonicity, cash translation, nonnegative
homogeneity, subadditivity, weighted bounds, and uniform error bounds. This
is an ambiguous expected-loss criterion, distinct from CVaR at a specified
confidence level.

[RobustAllocation.agda](Examples/Portfolio/RobustAllocation.agda) keeps the original asset losses
but uses two candidate probability laws:

| Model | A stress | B stress | Neutral 1 | Neutral 2 |
| --- | ---: | ---: | ---: | ---: |
| Up | 1/2 | 1/4 | 1/4 | 0 |
| Down | 1/8 | 1/2 | 3/8 | 0 |

For `L(w) = w A + (1-w) B`, their expectations are

```text
E_Up[L(w)]   = 1/2 + 2w
E_Down[L(w)] = 11/4 - 3w
```

A fixed adversarial mixture with model weights `(3/5,2/5)` has expectation
`7/5` at **every real weight**. It supplies a universal lower bound. At
`w=9/20`, both models attain `7/5`, proving global optimality. The two affine
inequalities also prove uniqueness: any real weight meeting capital `7/5`
equals `9/20`. The selected weight is within the long-only interval.

| Quantity | Equal weights | Robustly selected A weight `9/20` |
| --- | ---: | ---: |
| Worst expected loss across models/mixtures | 3/2 | 7/5 |
| Maximum scenario loss | 2 | 12/5 |
| Mean under the old uniform law | 1 | 1 |

The strict improvement in ambiguous expected loss and the strict deterioration
in stress loss are both proved. Capital `7/5` rejects equal weights under the
ambiguity criterion. This example has no transaction fees; selecting a
portfolio jointly under costs, ambiguity, and all policy limits requires a
further constrained model.

## Two-stage risk and local capital certificates

[DynamicRisk.agda](Dynamic/Base.agda) defines `CoherentRisk` using monotonicity,
cash translation, nonnegative homogeneity, and subadditivity. Normalization
and evaluation of constants follow from those laws. Expectation, worst-case
loss, and finite model ambiguity provide constructed instances.

A `LossTree m n` has a first observed branch and then a terminal leaf. With
an outer risk rule and one inner rule per branch, backward evaluation is

```text
continuationRisk(X)ᵢ = innerᵢ(Xᵢ)
rootRisk(X)         = outer(continuationRisk(X))
```

The composition inherits the risk laws. If every revised continuation risk
is at most its previous value, root risk is at most its previous value.
This is the proved two-stage time-consistency property. It allows changes
which do not improve loss at every terminal leaf.

In the checked [DownstreamControl](Examples/Dynamic/DownstreamControl.agda) example, the outer rule is maximum and
each inner rule is fair expectation:

| Branch | Original leaf losses | Revised leaf losses | Conditional risk before/after |
| --- | --- | --- | --- |
| 0 | `(8,-2)` | `(2,0)` | `3 → 1` |
| 1 | `(0,2)` | `(0,2)` | `1 → 1` |

Root capital falls from 3 to 1 even though the gain `-2` at one leaf becomes
loss 0. This is a comparison of supplied loss trees, not a proof that a
particular trading strategy can implement the revision.

A `NodeBudgetCertificate` records intermediate branch budgets and their
aggregate root bound. It implies root acceptance, and exact continuation
risks construct a certificate from any root bound. Propositional truncation
of such certificates is equivalent to root acceptance. Known branch costs
can be added after evaluating future local risk; nonuniform error reserves
propagate through the outer rule. Nested maxima are characterized by their
leafwise bounds and commute when the two finite indices are exchanged.
For expectation, multiplying initial and conditional probabilities gives
total mass one and a proved finite tower formula, including zero atoms.

## How independent branch uncertainty changes capital

[DynamicAmbiguity.agda](Dynamic/Ambiguity.agda) composes finite ambiguous
expectations. It proves that root capital bounds expected loss under every
outer mixture and every independently chosen family of inner mixtures, with
arbitrary real probability weights on the supplied model lists. Node-budget
certificates have the same soundness guarantee. The generic theorem is an
upper bound; a converse or exact supremum representation for all rectangular
models is not claimed.

The explicit [RectangularGap](Examples/Dynamic/RectangularGap.agda) example has fair initial branches and losses
`(4,0)` at each branch. Two coupled global models select opposite leaves:

| Global model | Selected leaf at branch 0 | Selected leaf at branch 1 | Expected loss |
| --- | ---: | ---: | ---: |
| Model 0 | 0 | 1 | 2 |
| Model 1 | 1 | 0 | 2 |

Every mixture of these coupled models meets budget 2. If conditional model
choices are allowed independently after each branch, both branches may
select leaf 0, and nested risk is exactly 4. The strict gap and the
impossibility of a rectangular budget of 2 are checked. Enlarging the
uncertainty set changes the capital requirement; nesting does not preserve
the original coupled model's risk value.

The mathematical background for nested risk and time consistency includes
Ruszczyński's [Risk-Averse Dynamic Programming for Markov Decision
Processes](https://optimization-online.org/wp-content/uploads/2009/12/2497.pdf).
The distinction between coupled uncertainty and dynamic decomposition is
discussed in Shapiro's [Rectangular sets of probability
measures](https://optimization-online.org/wp-content/uploads/2014/10/4613.pdf).
These are conceptual references. The Agda development proves its finite
statements locally and does not import the papers' analytic or optimization
existence results.

## A precise limit on economic netting

[ExecutionEquivalence.agda](Portfolio/ExecutionEquivalence.agda) applies the existing
HIT economic quotient to total losses including fees. For a fixed market,
rate vector, initial holding, and nonempty scenario set, it proves:

```text
given equal raw loss profiles,
equal execution classes ≃ equal transaction costs
```

Fees can therefore be carried from raw economic classes to execution classes
exactly when they are invariant under raw loss equivalence. Sufficiency uses
the set-quotient recursor; necessity uses quotient effectiveness and
cancellation at one scenario. The relevant equalities and equivalences
ignore alternative proofs of the same financial condition.

The [execution example](Examples/Portfolio/ExecutionEquivalence.agda) shows
that the direct equal-weight holding and the wrapped basket still have the same
raw economic class. Starting at zero, with asset rates `(1,1,3)`, their fees
are respectively 1 and 3. Their CVaRs including fees are 3 and 5: at budget 3,
direct execution passes and basket execution fails. Their execution classes
are unequal, and no map from the raw quotient to the execution quotient can
agree with execution on every representative.

This does not exclude arbitrary functions between the quotient types. Nor
does a total-loss class retain enough state for future rebalancing: actual
holdings may still be needed to calculate later fees.

## Foundation and scope

All probabilities, weights, fees, and risk values in the general statements
are Cauchy reals. Real maxima and absolute values use constructive lattice
operations. Supporting inequalities avoid real-order case splits; the
executable trade and budget decisions compare rationals. Cubical function
extensionality, effective HIT set quotients, propositional truncation, and
univalence connect financial representations and policy evidence. No choice
of a maximizing model or a representative of a quotient is required.

Fees are deterministic additional losses with prescribed target holdings.
Funding feasibility is outside this model: fees are not deducted from the
target notionals, and a cash account is not constructed. Rates remain fixed
for the triangle and convexity theorems. Prices, interest, slippage, liquidity,
fixed ticket charges, and market-data calibration are absent.

The dynamic layer has a fixed finite two-stage tree. It does not construct a
filtration, recover conditional probabilities from a joint law, or solve a
general dynamic trading problem. A generic static CVaR risk function is not
assumed to exist or to be time consistent. Every numerical optimum used here
has an explicit checked proof.
