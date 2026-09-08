# Financial methods and example sources

The new generic margin progression has its own
[Broker references and stage mapping](Broker/REFERENCES.md), including collateral,
revaluation, minimum transfers and identified receipt processing. It introduces
no additional numerical scenarios.

These nine primary sources explain the financial methods used here. The Agda
modules prove their stated claims for supplied finite data and Cauchy-real
parameters; the references are not axioms imported into those proofs. In
particular, the development does not import classical existence theorems for
optimizers, quantiles or infinite-dimensional risk representations.

The [system guarantees](SYSTEM_GUARANTEES.md) compose these methods into
[BrokerGuarantees](Examples/FX/BrokerGuarantees.agda) and
[TradingGuarantees](Examples/Portfolio/TradingGuarantees.agda). Their end-to-end
correctness statements are proved locally from the component definitions and
certificates; the references motivate the financial models used by that code.

<a id="synthetic-parameters"></a>
## Synthetic parameters and conventions

All worked examples use synthetic inputs. Their scenario losses, probabilities,
fee rates, notionals and collateral amounts are chosen to make exact proofs
readable. They are not estimates from market data or recommended trading rules.

| Input | Meaning in the examples |
| --- | --- |
| Four equal scenario probabilities and a 50% tail | An illustrative tail-risk problem, not estimated default probabilities or a regulatory confidence level. |
| Spot 0.8 and 1.2 around a reference of 1 | Synthetic minus/plus 20% currency moves. The joint box also includes all intermediate real spot values. |
| Discount factors between 0.9 and 1 | Supplied valuation factors. A factor of 0.9 is not an assertion of a 10% annual interest rate. |
| 20% collateral haircut | The example retains 80% of the foreign collateral's stressed domestic value. This is not a prescribed regulatory haircut. |
| Fees 1 and 5, or instrument rates (1, 1, 3) | Abstract loss units for exact comparisons. The resulting fee threshold 4 is specific to the constructed portfolio. |

The loss convention makes positive values losses and negative values gains.
The tail objective is `t + κ E[(X - t)⁺]`, where the interpretation is
`κ = 1 / tail mass = 1 / (1 - confidence)`. `TailLevel` records `κ ≥ 1`
directly, avoiding a partial reciprocal operation. Thus `κ = 2` means a 50%
tail. The dual certificate uses a probability vector `q` satisfying
`qᵢ ≤ κ pᵢ`; it does not divide by possibly zero nominal probabilities.
Shapiro's AVaR notation uses a tail-mass parameter, whereas confidence-level
notation uses its complement.

Execution cost is `Σᵢ rateᵢ |targetᵢ - oldᵢ|`, charging each traded leg.
For normalized holdings, conventional one-way turnover is often **half** the
L¹ traded amount. In `Rebalancing`, the two leg rates are `s/2`, giving cost
`s |1 - w|`. Fees enter the loss objective as an additional deterministic loss;
the model does not deduct them from target notionals through a funding account.

<a id="markowitz-1952"></a>
## 1. Markowitz: covariance and diversification

Harry Markowitz (1952), **Portfolio Selection**, *The Journal of Finance*
7(1), 77–91. [Publisher DOI](https://doi.org/10.1111/j.1540-6261.1952.tb01525.x);
[scan of the original article](https://traders.berkeley.edu/papers/Markowitz.pdf).

The mean–variance formulation makes portfolio risk depend on pairwise
covariances as well as individual variances. This motivates
[Risk/Variance.agda](Risk/Variance.agda) and
[VarianceExample](Examples/Portfolio/VarianceExample.agda), which evaluates
the covariance contribution and proves an exact variance minimum. The related
[Diversification](Examples/Portfolio/Diversification.agda) example also uses
tail and worst-scenario risk; those measures are covered by the sources below.
The paper does not supply our loss vectors or imply that variance measures
every relevant form of risk.

<a id="rockafellar-uryasev-2002"></a>
## 2. Rockafellar–Uryasev: CVaR threshold certificates

R. Tyrrell Rockafellar and Stanislav Uryasev (2002), **Conditional Value-at-Risk
for General Loss Distributions**, *Journal of Banking & Finance* 26(7),
1443–1471. [Author PDF](https://sites.math.washington.edu/~rtr/papers/rtr187-CVaR2.pdf).

Theorem 10 gives the threshold minimization characterization for general loss
distributions, including discrete ones; Theorem 14 and the finite scenario
formulation explain its optimization use. These support the objective in
[ExpectedShortfall](Risk/ExpectedShortfall.agda), the certificates used by
[Application](Examples/Portfolio/Application.agda), and the explicit global
bounds in [Diversification](Examples/Portfolio/Diversification.agda).
Our finite weak-duality proof checks a supplied threshold and capped probability
vector; it does not assume an algorithm that sorts arbitrary real losses or
automatically chooses an optimizer. The dual representation has an additional
reference in [Shapiro](#shapiro-2016).

<a id="boyd-2017"></a>
## 3. Boyd and coauthors: trading costs and turnover

Stephen Boyd, Enzo Busseti, Steven Diamond, Ronald N. Kahn, Kwangmoo Koh,
Peter Nystrup and Jan Speth (2017), **Multi-Period Trading via Convex
Optimization**, *Foundations and Trends in Optimization* 3(1), 1–76.
[Author publication page](https://web.stanford.edu/~boyd/papers/cvx_portfolio.html);
[PDF](https://web.stanford.edu/~boyd/papers/pdf/cvx_portfolio.pdf).

Sections 2.3 and 4.5 discuss transaction costs and turnover constraints;
section 4.2 includes covariance-based portfolio risk. The proportional-cost
part motivates [TransactionCosts](Portfolio/TransactionCosts.agda),
[Rebalancing](Examples/Portfolio/Rebalancing.agda),
[TradeDecision](Examples/Portfolio/TradeDecision.agda), and
[StressConstrainedTrade](Examples/Portfolio/StressConstrainedTrade.agda).
[ExecutionEquivalence](Examples/Portfolio/ExecutionEquivalence.agda) combines
that fee model with a separately proved cubical quotient counterexample.
The paper's broader multi-period optimization system is not formalized here;
our exact trading decisions concern the specified finite market. Observe the
[L¹ versus half-L¹ convention](#synthetic-parameters).

<a id="ben-tal-nemirovski-1998"></a>
## 4. Ben-Tal–Nemirovski: robust uncertainty sets

Aharon Ben-Tal and Arkadi Nemirovski (1998), **Robust Convex Optimization**,
*Mathematics of Operations Research* 23(4), 769–805.
[Author PDF](https://www2.isye.gatech.edu/~nemirovs/robmp.pdf);
[publisher DOI](https://pubsonline.informs.org/doi/abs/10.1287/moor.23.4.769).

The robust formulation requires constraints to hold for every parameter in a
specified uncertainty set. This motivates
[RobustAllocation](Examples/Portfolio/RobustAllocation.agda),
[FXBounds](Instruments/FXBounds.agda),
[JointMoveExample](Examples/FX/JointMoveExample.agda), and
[JointFXMargin](Examples/FX/JointFXMargin.agda). The latter uses universal
real-box bounds plus explicit attaining quotes to prove exact margin minima.
The source does not calibrate our uncertainty sets. Checking a few isolated
shocks alone would not prove coverage of their whole joint box.

<a id="shapiro-2016"></a>
## 5. Shapiro: coherent risk and rectangular ambiguity

Alexander Shapiro (2016), **Rectangular Sets of Probability Measures**,
*Operations Research* 64(2), 528–541.
[Author preprint](https://optimization-online.org/wp-content/uploads/2014/10/4613.pdf);
[publication DOI](https://pubsonline.informs.org/doi/abs/10.1287/opre.2015.1466).

Sections 2–3 connect worst expectations, dynamic decomposition and coherent
risk. Equation (3.5) expresses AVaR using normalized, bounded probability
densities, motivating the finite density-cap certificates in
[ExpectedShortfall](Risk/ExpectedShortfall.agda). The ambiguity and nested-risk
methods inform [Risk/Ambiguity](Risk/Ambiguity.agda),
[Dynamic/Ambiguity](Dynamic/Ambiguity.agda),
[DownstreamControl](Examples/Dynamic/DownstreamControl.agda), and
[RectangularGap](Examples/Dynamic/RectangularGap.agda).

The current dynamic development proves the stated two-stage consistency and
rectangular upper-bound results. It does not identify nested risk with static
CVaR or import a general infinite-dimensional representation theorem. The
static mixture equivalences quantify over mixtures of the supplied model
generators, not every possible probability law.

<a id="epstein-schneider-2003"></a>
## 6. Epstein–Schneider: recursive multiple priors

Larry G. Epstein and Martin Schneider (2003), **Recursive Multiple-Priors**,
*Journal of Economic Theory* 113(1), 1–31.
[Author draft, dated 2002](https://people.bu.edu/lepstein/files-research/rectang50.pdf);
[published article](https://www.sciencedirect.com/science/article/pii/S0022053103000978).

Rectangularity relates admissible conditional beliefs to dynamic consistency.
[RectangularGap](Examples/Dynamic/RectangularGap.agda) illustrates how allowing
branch-dependent model selection enlarges a coupled ambiguity set and raises
its exact risk from 2 to 4 in a synthetic tree. This is a concrete finite
illustration, not a formalization of the paper's complete preference axioms.

<a id="bis-fx-2016"></a>
## 7. BIS: FX swap cashflows and cross-currency funding

Claudio Borio, Robert McCauley, Patrick McGuire and Vladyslav Sushko (2016),
**Covered interest parity lost: understanding the cross-currency basis**,
*BIS Quarterly Review*, September, 45–64.
[BIS PDF](https://www.bis.org/publ/qtrpdf/r_qt1609e.pdf).

Box A explains FX swap cashflows and covered interest parity; the surrounding
discussion explains the relevance of funding and cross-currency basis.
This supports the near/far exchange structure in
[FXSwap](Instruments/FXSwap.agda) and its use in
[BrokerMargin](Examples/FX/BrokerMargin.agda). Our valuation formula uses
supplied positive spot and discount factors. It does not infer a calibrated
curve, impose frictionless covered interest parity, or model every funding
spread. Reference rates of 1 and the stated stress factors are synthetic.

<a id="bcbs-settlement-2013"></a>
## 8. BCBS: FX settlement, netting and liquidity

Basel Committee on Banking Supervision (2013), **Supervisory guidance for
managing risks associated with the settlement of foreign exchange
transactions**, February.
[Official PDF](https://www.bis.org/publications/201302-guidelines-supervisory-guidance-managing-risks-associated-settlement-foreign-exchange-transactions.pdf).

Sections 3.2–3.4 distinguish principal, replacement-cost and liquidity risks;
Annex C discusses netting. These distinctions motivate
[OppositeClaims](Examples/Netting/OppositeClaims.agda),
[TwoCurrencyExample](Examples/Settlement/TwoCurrencyExample.agda), and
[BrokerOperations](Examples/FX/BrokerOperations.agda). They explain why a zero
aggregate mark does not establish separate client exposure or currency funding
coverage. Legal netting rights and available collateral are supplied modeling
conditions, not consequences of algebraic cancellation. The ideal atomic PvP
result concerns principal settlement loss; replacement-cost and liquidity
risks can remain. A fully covered close-out claim likewise says nothing by
itself about settlement funding or whether a margin demand has actually been
paid.

<a id="bcbs-iosco-margin-2020"></a>
## 9. BCBS–IOSCO: collateral valuation and margin scope

Basel Committee on Banking Supervision and International Organization of
Securities Commissions (2020), **Margin requirements for non-centrally cleared
derivatives**, April revision.
[Official PDF](https://www.bis.org/publications/202004-standards-margin-requirements-non-centrally-cleared-derivatives.pdf).

Element 4 discusses eligible collateral, valuation haircuts and currency
mismatch. This is methodological context for the currency-sensitive collateral
in [BrokerMargin](Examples/FX/BrokerMargin.agda) and
[JointFXMargin](Examples/FX/JointFXMargin.agda), including simultaneous adverse
changes in the claim and its collateral.

**Section 1.1 excludes physically settled FX forwards and swaps from the
framework's general margin requirements.** Its discussion points to FX
settlement guidance and national implementation for variation-margin treatment.
Consequently these examples do not certify regulatory compliance, and their
20% haircut and exact cash calls are not prescribed by this publication.

The cubical equivalences, proposition truncation and quotient invariance
arguments are part of this formal development. The financial references above
explain the modeled methods, rather than claiming those type-theoretic
constructions as results of the cited authors.
