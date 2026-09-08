# Sources and presentation choices

This progression formalizes a small margin engine and its successive changes.
The financial sources motivate the concepts; the version-to-version refinements,
rational report updates and Cubical certificate paths are theorems of this
implementation. No numerical scenario or parameter calibration is supplied.

| Versions | Source | What it motivates |
| --- | --- | --- |
| V01–V03 | BCBS, *Supervisory guidance for managing risks associated with the settlement of foreign exchange transactions* (2013), §§3.3.5–3.3.8. [Official guidance](https://www.bis.org/publ/bcbs241.htm). | Replacement-cost exposure, separate authorized netting sets, and collateral availability/valuation. |
| V03–V04 | A. Ben-Tal and A. Nemirovski, *Robust Convex Optimization*, Mathematics of Operations Research 23(4), 769–805 (1998). [Author-hosted paper](https://www2.isye.gatech.edu/~nemirovs/robmp.pdf). | Interpreting coverage as a constraint that holds for every member of a supplied uncertainty set. |
| V05 | BCBS–IOSCO, *Margin requirements for non-centrally cleared derivatives*, April 2020 revision, requirement 2.3 and Element 4. [Dated standard](https://www.bis.org/publications/202004-standards-margin-requirements-non-centrally-cleared-derivatives.pdf). | Minimum transfer amounts and conservative collateral concepts. The precise full-gap-or-zero policy and equality boundary are explicit model choices. |
| V06 | FINOS, *Common Domain Model: Event Model*, living documentation, accessed 8 September 2026. [Event identity](https://cdm.finos.org/docs/event-model/#event-identifier). | Distinguishing a business event's identity from delivery/workflow messages. |
| V06 | J. H. Saltzer, D. P. Reed, and D. D. Clark, *End-to-End Arguments in System Design*, ACM TOCS 2(4), 277–288 (1984). [MIT-hosted text](https://web.mit.edu/6.033/2002/wwwdocs/papers/endtoend.pdf#page=6). | Duplicate suppression using knowledge at the application boundary. |
| V07 | D. Brigo and A. Pallavicini, *Nonlinear consistent valuation of CCP cleared or CSA bilateral trades with initial margins under credit, funding and wrong-way risks*, Journal of Financial Engineering 1(1), 1450001 (2014). [Publisher DOI](https://doi.org/10.1142/S2345768614500019). | Explicitly accounting for collateral and adverse changes before cash protection is available. Our reserve is a deterministic bound, not that paper's stochastic valuation model. |

The [earlier broker bibliography](../Broker/REFERENCES.md) supplies fuller
bibliographic details, section references and source-specific limitations.
The [presentation](PRESENTATION.md) uses these concepts to explain software
contracts rather than to reproduce the cited methodologies in full.

## Limits of attribution

The rational report interface is our constructive bridge from real risk to
executable amount decisions. For arbitrary real profiles it consumes a certified
bound. For rational profiles `RationalInputs` computes and proves exact finite
maxima. Neither behavior is attributed to a cited optimization algorithm.

The MTA theorem bounds a residual allowance after actual receipts. Physically
settled FX forwards/swaps are excluded from the 2020 standard's general margin
requirements; its requirement 1.1 points to separate variation-margin guidance
and national treatment. No assertion of regulatory applicability or compliance
is made for this generic code.

The event catalog fixes each owner and amount. Distinct IDs must denote distinct
actual receipts, separate from base collateral. The CDM and duplicate-suppression
references motivate that distinction; they do not authenticate our inputs or
establish durable, concurrent banking operations.

The final guarantee concerns modeled positive unsecured replacement exposure
and supplied severities in `[0,1]`. Settlement principal, funding liquidity,
liquidation and model adequacy require separate contracts. The proof assistant
checks consequences of the supplied data and evidence; it does not certify
that a chosen stress family describes the future market.

<a id="relational-pipeline"></a>
## Relational pipeline: representation, identity, and accounting

The [pipeline guide](Pipeline/README.md) starts with the standalone
[Implementation/Calculation](Pipeline/Implementation/Calculation.agda) function.
Its `calculate` body chains typed source rows through `deriveᵣ`, `selectᵣ`,
grouping, a maximum fold, and projection. It returns the current call table.
The `Implementation/` modules contain ordinary calculations; the separate
`Properties/` modules contain their accounting and financial proofs.

[Properties/Calculation](Pipeline/Properties/Calculation.agda) proves
`calculate-refines-model` for the actual output table, using the current exact
initial report and V06 quote. `calculate-certified` certifies every returned row;
its `upper-exact` field connects the amount to the independent indexed
`referenceBook`. `fulfilling-calculation` then gives the tolerance guarantee when
additional nonnegative actual payments meet that table's requests. The supplied
valuation functions are shared by implementation and specification; accounting
refinement is not independent pricing validation.

The optional [Margin engine](Pipeline/Implementation/Margin.agda) retains the
broader receipt/revaluation lifecycle and its
[complete output refinement](Pipeline/Properties/Refinement.agda).
Its maintained conservative quotes need not equal the standalone calculation's
recomputed exact current quote. The computed-report paths do not identify
arbitrary conservative reports. These are implementation theorems, not results
attributed to the sources below. Existing and additional receipt cash is supplied
as available at par in the common account currency; the literature does not
establish that premise for an input catalog.

| Pipeline concept | Primary source and scope |
| --- | --- |
| Separating a logical data model from a machine representation | [Codd (1970)](#codd-1970) motivates the separation; our exact accounting and model-refinement paths are proved in Agda. |
| Grouping positions into an authorized netting set and valuing available collateral | [BCBS FX guidance](../Broker/REFERENCES.md#bcbs-fx-2013), especially §§3.3.5–3.3.8. A pipeline client key must denote a permissible netting group; the source does not certify the adapter's grouping. |
| Business receipt identity independent of message delivery | [FINOS CDM](../Broker/REFERENCES.md#cdm-event-model). External labels are metadata in our schema; immutable internal keys drive actual receipt accounting. |
| Suppressing replay at the application boundary | [Saltzer, Reed, and Clark](../Broker/REFERENCES.md#saltzer-1984). The implementation proves ledger and balance identities, without a durable-storage or authentication theorem. |
| Uniform protection across supplied scenarios | [Ben-Tal and Nemirovski](../Broker/REFERENCES.md#robust-optimization) motivates requiring coverage for every supplied scenario. The exact finite calculation and its row certificate are proved here. |
| Adverse revaluation in the optional broader engine | [Brigo and Pallavicini](../Broker/REFERENCES.md#brigo-pallavicini-2014) motivates explicit margining/gap risk. Summing positive scenario changes is our sufficient reserve, not a calibrated initial-margin method or a least-reserve claim. |

Completeness, business-key uniqueness, custody availability, sufficient
instrument identifiers, and snapshot consistency remain source-adapter
conditions. The formal refinements certify consequences of those supplied data.
They do not establish that the catalog describes the external business correctly.

<a id="codd-1970"></a>
## Codd: logical data representation, 1970

E. F. Codd, *A relational model of data for large shared data banks*,
*Communications of the ACM* **13**(6), 377–387, 1 June 1970.
[Publisher DOI: 10.1145/362384.362685](https://doi.org/10.1145/362384.362685),
[IBM Research publication record](https://research.ibm.com/publications/a-relational-model-of-data-for-large-shared-data-banks).

Codd motivates protecting applications from changes in internal data
representation and introduces a relational model. This provides context for
separating pipeline row operations from their indexed financial meaning.
[Publisher abstract](https://doi.org/10.1145/362384.362685).

Our `Relation'` is a list with explicit order and multiplicity. The pipeline
implements specified projection, selection, and aggregation functions over it;
it does not claim all relational-algebra or SQL laws, query-optimizer correctness,
database normalization, or transaction isolation. The refinement proofs and
Cauchy-real risk guarantees are this implementation's results.
