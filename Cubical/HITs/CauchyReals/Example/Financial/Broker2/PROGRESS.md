# Broker2 progress and validation

## 8 September 2026 — one engine evolved for a quant developer presentation

Implemented seven successive versions in **857 Agda source lines**. The
[reading guide](README.md) and [28-minute presentation](PRESENTATION.md) follow
one recurring `quoteCall` / `receive` / `receive-correct` contract. Every version
after V01 imports its predecessor and has an explicit projection, specialization,
or transition-refinement theorem. No concrete scenario or calibrated portfolio
was added.

### Implementation milestones

- **V01:** a self-contained account state, positive-part call calculation, actual
  receipt transition, leastness, receipt composition, and equivalent policy
  propositions identified by univalence.
- **V02:** the same operations lifted to separate client netting sets; per-client
  projection commutes with quoting and receiving. Whole-book coverage eliminates
  modeled residual and severity-weighted loss.
- **V03:** finite nonempty stress profiles with arbitrary Cauchy-real values;
  uniform least calls, receipt/report update identity, scenario projection, and
  an exact singleton regression to V02.
- **V04:** rational upper reports on current incremental calls, a decidable
  receipt gate, report updates after partial payments, and optional complete
  economic decisions under exactness. A generic rational input factory computes
  exact initial reports without an external margin oracle.
- **V05:** the same engine with minimum transfer amounts. Actual adequate
  receipts give client and aggregate loss bounds; zero MTA recovers V04's quote.
- **V06:** a market and immutable identified-receipt ledger. A state path proves
  that receiving a batch equals the previous engine receiving only newly
  credited cash. `process` returns the next state, its transition equality, a
  certified next report, and the assessment. Replay identifies the state plus
  its safety certificate.
- **V07:** a supplied bounded market update preserves the ledger and refreshes
  the incremental report with a conservative rational reserve. The same receipt
  engine then runs under the new market. An unchanged-market/zero-reserve
  specialization recovers V06. Final guarantees quantify over every supplied
  stress, client, and modeled severity.

The earlier `Broker/` progression remains independent. Reusable finite-margin,
shortfall, journal, revaluation and transfer lemmas are reused rather than copied
into each version. [Broker2.agda](../Broker2.agda) exposes version namespaces;
`Theory.Broker2` provides the reusable entry point.

### Parallel development and review

One agent implemented and checked V04 and its generic rational report factory.
A second agent wrote the presentation guide. A third independently reviewed the
version sequence and its financial/refinement boundaries while the root built
the other versions and their composition.

Reviews found no remaining correctness defect. They sharpened the following
points, which are recorded in the guide and source:

- Reports bound **incremental** calls, already accounting for existing cash.
  Receipt updates subtract new cash only; revaluation adds its reserve without
  subtracting the old ledger balance again.
- Uniform stress quotes dominate individual snapshot quotes. Equality with V02
  is the singleton specialization, not a general scenario projection claim.
- A conservative quoted plan can be unfulfilled while coverage already holds.
  Economic completeness is asserted only with an exact report.
- V06's projection represents catalog-derived rational cash. It is not a
  representation equivalence with every V05 arbitrary real balance.
- Actual partial receipts remain recorded on an unmet-quote outcome, and the
  report advances to the resulting state.
- Replay identifies state plus `Guarantee`. It does not identify arbitrary
  conservative reports or assert arbitrary revaluation-workflow idempotence.

[REFERENCES.md](REFERENCES.md) connects the progression to BCBS FX guidance,
robust feasibility, minimum transfers, event identity, duplicate suppression and
margin/gap risk. The speaker guide explains the actual theorem statements and
keeps numerical calibration and operational claims outside their scope.

### Final compiler checks

All changed Agda sources were checked with `agda-codex` after their edits. The
final entry-point checks completed on **8 September 2026 (UTC)**:

| File | Check time | Status |
| --- | --- | --- |
| `Broker2.agda` | 06:21:10 | exit 0, checked |
| `Theory.agda` | 06:22:17 | exit 0, checked |
| `../Financial.agda` | 06:22:59 | exit 0, checked |

All report **zero holes, unsolved metas, constraints, and warnings**. These
checks include the final version sources and their complete financial dependency
closure. The final commands were:

```sh
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Broker2.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial/Theory.agda
agda-codex Cubical/HITs/CauchyReals/Example/Financial.agda
```

The full development now has **101 Agda files and 10,213 source lines**. An
import-graph audit found every financial module reachable from the full umbrella,
every Broker2 successor importing its predecessor, no flat compatibility-module
dependency from Broker2, and no worked-example dependency from Theory.
All new version files and their entry point use `--safe --cubical`. No postulate,
unsafe option, missing analysis assumption, or foundational change was added.

Local documentation links, source names, recorded hashes, proof discipline and
whitespace were checked. Existing numerical examples and unrelated
RealHomotopy/Spheres work were not edited. No runtime throughput benchmark,
extraction/deployment claim, concrete market run, or deliberate mutation-test
result is asserted by this validation.

### Checked source hashes

| File | SHA-256 |
| --- | --- |
| V01Account.agda | `70916aab7555b39c35bfecc5895dfbc9a45bc307440b49763109cab4c814f25c` |
| V02Clients.agda | `e29d57d48310f2311f88ce027ab60cc96ad36941d1e0e9ca68660acdda788d3c` |
| V03Stress.agda | `a800dccf5715a45623bff6c0ec9ea2f5a976862a5eed467b9d2a837306f976f0` |
| V04Rational.agda | `76737b3dd675ae6d0553589cd4cbe82883b1bf8ec74ec49f201d5636af6cae98` |
| V05Tolerance.agda | `58d59ccb5e0b5c2e9b58c2a0cebfb43c3b229c29efb2d93030e3d93c27893ee7` |
| V06Receipts.agda | `4cfc1d900d360658da5da911214a7e9dc0fec213ea2832db23f61b90663088a5` |
| V07Revaluation.agda | `46a52af0bd391f54ec91ef5fce27504a0ff0c8e501b479ca091bbc2f29d3d32e` |
| Broker2.agda | `86344c186e5df3cd79004de51bad238623f7b2c1c06d7a94431f6c3f668de054` |
| Theory.agda | `a5a9284a13fb305ff8113a64d5fc9bd232d69f07024ea7e686ed589a057fa392` |
| Financial.agda | `412afca06dcb966bf9d9e6e12e6c29f187a62a57550c079686594e5532655490` |
