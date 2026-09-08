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
