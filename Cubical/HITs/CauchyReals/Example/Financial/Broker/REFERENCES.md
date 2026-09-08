# Sources for the generic broker margin progression

These sources motivate the financial concepts and system boundaries of the eight
stages. The Agda modules supply their own constructive proofs. None of these
sources supplies a postulate, a calibrated parameter, or a correctness theorem
for this implementation. The progression has no concrete market scenario or
instrument dependency.

| Stage | Method implemented here | Relevant sources |
| --- | --- | --- |
| [01 Cash](Stage01Cash.agda) | Signed replacement claim, available cash, and the distinction between requesting and receiving cash. | [BCBS FX](#bcbs-fx-2013), especially collateral arrangements and transfer timing. |
| [02 Scenarios](Stage02Scenarios.agda) | Coverage for every allowed state; supplied rational bounds support decisions without deciding arbitrary real order. | [Robust optimization](#robust-optimization) for universal uncertainty constraints; [BCBS FX](#bcbs-fx-2013) for stressed exposure management. |
| [03 Netting sets](Stage03NettingSets.agda) | Separate authorized sets, individual coverage, and aggregate unsecured exposure. | [BCBS FX](#bcbs-fx-2013) for enforceable netting and collateral agreements. |
| [04 Collateral](Stage04Collateral.agda) | Inventory allocation, scenario-dependent eligible value, retention factors, and coverage-preserving substitution. | [BCBS FX](#bcbs-fx-2013) and [BCBS–IOSCO](#bcbs-iosco-2020) for collateral eligibility, valuation, and haircuts. |
| [05 Journal](Stage05Journal.agda) | Identified actual receipts, per-client balances, replay idempotency, and order-independent accounting. | [FINOS CDM](#cdm-event-model) for business event identity; [Saltzer, Reed, and Clark](#saltzer-1984) for application-level duplicate suppression. |
| [06 Revaluation](Stage06Revaluation.agda) | Certified adverse claim and collateral changes; an additive reserve sufficient after actual receipt. | [Brigo–Pallavicini](#brigo-pallavicini-2014) for margining and gap risk; [robust optimization](#robust-optimization) for bounds over supplied states. |
| [07 Calls](Stage07Calls.agda) | A minimum-transfer policy with a proved bound on the remaining unsecured amount. | [BCBS–IOSCO](#bcbs-iosco-2020) for the minimum-transfer concept; the precise policy is our definition. |
| [08 Controller](Stage08Controller.agda) | Composition of inventory, revaluation, transfer policy, and receipt accounting into conditional all-client guarantees. | The preceding sources motivate the components; the composition and dependent certificate transport are proved here. |

<a id="bcbs-fx-2013"></a>
## BCBS: FX settlement risk, 2013

Basel Committee on Banking Supervision, *Supervisory guidance for managing risks
associated with the settlement of foreign exchange transactions*, February 2013,
BCBS 241. [Official publication](https://www.bis.org/publ/bcbs241.htm),
[official PDF](https://www.bis.org/publications/201302-guidelines-supervisory-guidance-managing-risks-associated-settlement-foreign-exchange-transactions.pdf).

Sections 3.3.5–3.3.8 address enforceable netting agreements, collateral agreement
terms, variation margin for the specified FX counterparties, and stressed
collateral valuation with conservative haircuts. These motivate separate netting
sets and explicitly supplied collateral values. Sections 3.2, 3.4, and 3.6 treat
principal, liquidity, and legal risks separately: replacement-cost coverage alone
does not certify payment settlement, currency funding, or enforceability.
[Sections 3.3.5–3.3.8, printed page 16](https://www.bis.org/publications/201302-guidelines-supervisory-guidance-managing-risks-associated-settlement-foreign-exchange-transactions.pdf#page=22).

The model receives the legally authorized grouping and available collateral as
inputs. It does not determine applicable law, validate a collateral agreement, or
implement the guidance's operational requirements.

<a id="bcbs-iosco-2020"></a>
## BCBS–IOSCO: margin requirements, 2020

Basel Committee on Banking Supervision and International Organization of
Securities Commissions, *Margin requirements for non-centrally cleared
derivatives*, April 2020 revision.
[Official dated standard](https://www.bis.org/publications/202004-standards-margin-requirements-non-centrally-cleared-derivatives.pdf).

Requirement 2.3 discusses minimum transfer amounts; Element 4 addresses eligible
collateral and haircuts. These support the general concepts used in Stages 04 and
07. No regulatory haircut schedule, monetary threshold, entity test, or model
approval rule is encoded. The code's rule is explicit: request zero when the gap
is at most the supplied minimum transfer amount, otherwise request the whole gap.
Its equality boundary and residual-bound theorem are our formal choices.
[Requirements 2.1–2.3 and Element 4](https://www.bis.org/publications/202004-standards-margin-requirements-non-centrally-cleared-derivatives.pdf).

Requirement 1.1 excludes physically settled FX forwards and swaps from this
document's margin requirements and directs their variation-margin treatment to
supervisory guidance or national regulation, referring to BCBS 241. Thus this
source provides general margin concepts, not an assertion that this generic
controller is a regulatory implementation for FX swaps.
[Requirement 1.1](https://www.bis.org/publications/202004-standards-margin-requirements-non-centrally-cleared-derivatives.pdf#page=11).

<a id="robust-optimization"></a>
## Ben-Tal and Nemirovski: robust optimization, 1998

Aharon Ben-Tal and Arkadi Nemirovski, *Robust Convex Optimization*,
*Mathematics of Operations Research* **23**(4), 769–805, 1998.
[DOI: 10.1287/moor.23.4.769](https://doi.org/10.1287/moor.23.4.769),
[author-hosted paper](https://www2.isye.gatech.edu/~nemirovs/robmp.pdf).

The paper's robust feasibility condition requires constraints to hold for every
parameter in a specified uncertainty set. This supports the interpretation of
`Allowed` and universal coverage certificates. Our state types need not be finite
or convex; we prove implications from supplied bounds rather than implement the
paper's optimization algorithms.
[Definition in Section 1](https://www2.isye.gatech.edu/~nemirovs/robmp.pdf).

The development does not infer an uncertainty set from data, prove that future
markets stay inside it, or construct optimal real-valued bounds automatically.
Conservative rational requirements can certify coverage without being least.

<a id="brigo-pallavicini-2014"></a>
## Brigo and Pallavicini: margining and gap risk, 2014

Damiano Brigo and Andrea Pallavicini, *Nonlinear consistent valuation of CCP
cleared or CSA bilateral trades with initial margins under credit, funding and
wrong-way risks*, *Journal of Financial Engineering* **1**(1), 1450001,
1–60, 2014.
[Publisher and DOI: 10.1142/S2345768614500019](https://doi.org/10.1142/S2345768614500019).

The paper studies valuation with initial and variation margins, collateral, gap
credit risk, funding, and wrong-way risk. It motivates treating adverse changes
during the interval before collateral becomes available as an explicit part of
the model. Stage 06 uses deterministic, universally quantified change bounds;
its additive sufficient reserve is not the paper's stochastic valuation model
or a calibrated initial-margin methodology.
[Publisher abstract](https://doi.org/10.1142/S2345768614500019).

The accessible [2013 FAQ, arXiv:1312.0128](https://arxiv.org/abs/1312.0128)
by the same authors is a separate work, not an alternative bibliographic identity
for the 2014 paper. The 2014 paper is also listed in
[Brigo's author-hosted 2017 presentation](https://www.ma.imperial.ac.uk/~dbrigo/2017ScienceArtValuation.pdf).

No default probability, dependence calibration, discounting equation, BSDE, or
funding valuation adjustment is implemented in this progression. Conditional
zero unsecured closeout loss does not eliminate these other risks.

<a id="cdm-event-model"></a>
## FINOS: Common Domain Model event model

FINOS Common Domain Model, *Event Model*, official living documentation,
accessed 8 September 2026.
[Official event model](https://cdm.finos.org/docs/event-model/),
[Event Identifier](https://cdm.finos.org/docs/event-model/#event-identifier).

The documentation distinguishes business events, workflow state, message
information, and event identifiers. An event identifier supports references
from other workflow steps; it is not merely the delivery message identifier.
This motivates identifying the underlying receipt independently of a repeated
delivery. [Event and message identifiers](https://cdm.finos.org/docs/event-model/#event-identifier).

Stage 05 is a small independent ledger model, not a CDM implementation. Its finite
catalog fixes each event's owner and nonnegative amount before ingestion. A reused
ID cannot carry a changed payload through this API. Distinct IDs must represent
distinct actual receipts; corrections, reversals, identity assignment, and
authentication require an additional model. The CDM citation does not establish
those premises or prove the ledger's replay theorem.

<a id="saltzer-1984"></a>
## Saltzer, Reed, and Clark: duplicate suppression, 1984

Jerome H. Saltzer, David P. Reed, and David D. Clark, *End-to-End Arguments in
System Design*, *ACM Transactions on Computer Systems* **2**(4), 277–288,
November 1984.
[DOI: 10.1145/357401.357402](https://doi.org/10.1145/357401.357402),
[MIT-hosted author text](https://web.mit.edu/6.033/2002/wwwdocs/papers/endtoend.pdf).

The discussion of duplicate message suppression explains why application retries
can create duplicates that a communication layer cannot recognize. Application
knowledge is needed to identify the duplicated action. This motivates proving
receipt identity and balance preservation at the journal layer.
[Duplicate message suppression, PDF page 6](https://web.mit.edu/6.033/2002/wwwdocs/papers/endtoend.pdf#page=6).

Our proofs concern pure ledger transitions: replay, permutation, and batches
containing the same event IDs produce equal ledger states. They do not establish
network exactly-once delivery, crash recovery, durable commits, concurrent-store
linearizability, or the authenticity of a payment acknowledgement.

## Scope of the composed result

Stage 08 combines proved bounds for supplied claims, collateral valuations,
allowed states, and immutable actual-receipt data. Additional recorded cash must
be distinct from cash already counted in the collateral allocation. Settlement
of a computed plan is checked per client using newly credited receipts; a failed
check means that the plan is unfulfilled, since a conservative plan need not be
economically minimal.

After the required actual receipts, the controller bounds each client's residual
by its supplied transfer tolerance, and the broker's aggregate residual and
severity-weighted closeout loss by the sum of tolerances. Zero tolerance gives
complete modeled coverage. Cubical paths additionally transport the full
certificate across replay-equivalent ledger states. These are implementation
theorems with explicit premises, not claims attributed to the cited literature.

This progression makes no claim of regulatory compliance, empirical adequacy,
legal enforceability, settlement-principal protection, or native-currency
liquidity sufficiency.
