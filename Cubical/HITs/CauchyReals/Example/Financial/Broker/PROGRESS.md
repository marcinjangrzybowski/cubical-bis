# Broker progression: implementation and validation

## 8 September 2026 — generic machinery, eight stages

The requested separate folder now contains eight modules and 1,482 Agda source
lines. The progression extracts the important lessons of the earlier FX broker
example into generic machinery: client identity, sufficient versus exact margin,
actual receipt versus requested cash, collateral valuation, and composition of
whole-book guarantees. It introduces no concrete scenarios or calibrated data.

The [reading guide](README.md) describes each stage's inputs and results;
[REFERENCES.md](REFERENCES.md) connects the methods to six primary source groups.
The public [Broker.agda](../Broker.agda) entry point exports all stages, and the
reusable [Theory.agda](../Theory.agda) exposes them under `Broker`.

### Work completed

1. **Cash accounts:** least nonnegative calls, receipt composition, exact remaining
   calls, and a univalence path between payment adequacy and coverage.
2. **Scenario reports:** arbitrary admissible domains; sufficient requirements and
   rational lower/upper enclosures. Assessments distinguish proven coverage,
   proven deficiency, and uncertainty. Exact enclosures give complete decisions.
3. **Client netting:** arbitrary finite books, per-client checks, total necessary
   cash lower bounds, and full-coverage/zero-loss certificates for all severities.
4. **Collateral:** inventory-backed allocations, scenario-dependent prices and
   haircut retention, total eligible-value bounds, and coverage-preserving
   substitutions, including changed asset counts.
5. **Receipt journal:** finite immutable receipt catalog, owner attribution,
   duplicate suppression, batching/reordering paths, and exact incremental cash
   accounting. Batches may have arbitrary length and repeated IDs.
6. **Revaluation:** conservative claim-rise/collateral-fall reserves, exposure and
   loss bounds before reserve payment, coverage after receipt, and composition of
   consecutive drift bounds.
7. **Minimum transfers:** an executable full-gap-or-zero call policy; actual
   requested payments give residual bounded by MTA. Zero MTA gives full coverage.
8. **Controller:** old upper requirements plus certified rational drift reserves
   drive calls on current journal cash. A rational gate checks new receipts per
   client and returns a system certificate for the actual updated ledger.
   All client residuals and aggregate severity-weighted loss are bounded;
   zero MTA yields a whole-book zero-loss guarantee. Inventory plus extra cash
   bounds eligible value and controlled positive claims. Cubical paths identify
   replayed ledgers together with independently reconstructed certificates.

### Independent reviews

Three agents developed collateral, identified receipts, revaluation, and transfer
policy alongside the root's account, report, netting, and controller work. Reviews
cross-checked the interfaces and the final composition. No mathematical defect
remained after the normal compiler edit/check loops.

The reviews singled out conditions now stated in both code and the guide:

- A sufficient requirement describes a hypothetical protective balance; it does
  not prove that balance has already been received.
- The final gate compares requests with **newly credited** per-client receipts.
  Replaying previously credited IDs cannot satisfy another positive request.
- Journal cash is additional to base collateral inventory; asset pools and
  receipt IDs must represent distinct resources in the supplied model.
- A failed conservative plan is not necessarily an unsafe account. Only the
  exact-report assessment has a complete economic coverage decision.
- MTA gives a nonzero residual allowance; zero modeled loss needs zero MTA or
  separately proved complete coverage.
- `resources` includes unallocated inventory and gives a valuation bound, not a
  liquidity, solvency, custody, or legal-enforceability certificate.
- The complete certified-state replay path keeps catalog, valuation, claims,
  admissibility, policy, and MTA fixed. Withdrawals and reversals need new theory.

### Final compiler validation

All eight stage files were checked after their final Agda edits with
`agda-codex`. Final entry-point checks reached every stage and all existing
financial modules. Each reported **exit code 0, checked, with zero holes,
unsolved metas, constraints, and warnings**.

| Final check | UTC time on 7 September 2026 | Status |
| --- | --- | --- |
| `Broker/Stage08Controller.agda` | 22:11:36 | exit 0 |
| `Broker.agda` | 22:14:03 | exit 0 |
| `Theory.agda` | 22:14:25 | exit 0 |
| `../Financial.agda` | 22:14:52 | exit 0 |

These times are shortly after midnight on 8 September in Europe/Warsaw.
The final commands were:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Broker/Stage08Controller.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Broker.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Theory.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

Source SHA-256 values:

| File | SHA-256 |
| --- | --- |
| Stage01Cash | `af1f865bb38273ef950c7756b7e2be603c9c35e2c2049054b4c8680bfd0b5b0b` |
| Stage02Scenarios | `1df2f8e8cc9e895d7c4a4d3e1aedd2c98b77d25e8302c6dcb30c918c6e39f201` |
| Stage03NettingSets | `6682cb2eb9e9b209b28c7653ff049b171cf32077763478c6369d1a927c90e430` |
| Stage04Collateral | `b3d32858780c042726097eaf1c1625aa45605e3832002922a857c1e39aba7f3e` |
| Stage05Journal | `d52bc892eb1b118e33a03ce2c7e90b5e1f825606da88a065c5b5804a330b2b0d` |
| Stage06Revaluation | `18f6d2950934e227410ad02ae39d1afe4939634fce49ca21e82d56caf28e2a22` |
| Stage07Calls | `53043d1ddd8c72a8008ba82b0982a7fadddb5d1c4399cef200adee73ec41ee06` |
| Stage08Controller | `a21964131a7646162f195cdecb12efb5e3ea5d33955475bed6d4e5344ff7dcab` |
| Broker.agda | `207468c5f5a4f185db242b1309696cc539911411be8ee2bda48116419d0cae03` |
| Theory.agda | `490d822da6152c37958ba3cdda8866efe7d0757f53f14d70ac6ec526edf44993` |
| ../Financial.agda | `412afca06dcb966bf9d9e6e12e6c29f187a62a57550c079686594e5532655490` |

The entire financial development now has **93 Agda files and 9,327 source lines**.
An import-graph audit found every file reachable from the full umbrella and no
example or legacy-shim dependencies from the new broker progression. Theory
still imports no worked examples. All new modules use `--safe --cubical`; no
postulate, missing analysis assumption, weakened option, or new foundational
axiom was added. Local documentation links and source-reference anchors were
checked. Existing numerical examples and unrelated RealHomotopy/Spheres work
were not edited.

The deliverable is generic mathematical machinery and its conditional correctness
proofs. Receipt authenticity, stress-model adequacy, legal rights, liquidation,
settlement principal, currency funding, and operational persistence remain
explicit external obligations, not additional claims of these theorems.
