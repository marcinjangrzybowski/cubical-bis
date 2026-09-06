# Choice-free Analysis — 2026-09-06

The user requires Analysis to contain no countable-choice assumptions, even
as explicit theorem parameters. The former conditional exact-IVT and inverse
results were intentionally removed. [AGENTS.md](AGENTS.md) records the rule
for future contributors and coding agents.

## Removed

- The sequence-choice schema alias, its Completion comparison namespace,
  convergence-to-native-witness adapter, and propositional-choice adapter.
- The general choice-based exact interval-preimage and IVT construction.
- The choice-based exponential surjectivity/equivalence proof, global
  logarithm wrapper, and associated inverse/independence wrappers.
- The choice-based assembly of sine inverse moduli and approximation
  sequences, including rational-image approximation adapters.
- All dependent restricted-sine equivalence and characterized-pi wrappers,
  including the choice-based named arcsine and arccosine adapters.
- All six former choice modules and their facade imports. No replacement
  module or renamed assumption preserves these conditional results.

## Preserved

- Exponential algebra, order, continuity, interval estimates, and derivative.
- The choice-free local logarithm series and its reciprocal derivative.
- Generic inverse laws for an independently supplied equivalence. Such a
  hypothesis is not an axiom of choice and does not establish existence of
  the equivalence or an unconditional global logarithm.
- Finite approximate IVT and sine-bisection image density. The characterized
  sine-density theorem now lives in `Pi/RestrictedSine.agda`.
- Choice-free image-approximation definitions, now in
  `QuarterTurn/Restriction/Approximation/Image.agda`, and the explicit-data
  dyadic sampling helper. These do not supply a native source Cauchy witness.
- The interval closeness-reflection predicate, now with the approximate-IVT
  definitions, without an exact inverse constructor.
- Quantitative/rational inverse routes when the caller already supplies the
  actual mathematical data they require. No missing modulus is manufactured.
- The preceding unrelated algebra, calculus, integration, and trigonometry
  work in the dirty tree.

## Future boundary

Do not turn a family of merely existing witnesses into a merely existing
family by assumption. Radiuswise convergence alone does not yield the
globally bundled Cauchy modulus required by the sequential carrier. General
exact IVT and unconditional restricted trigonometric inverses must still be
built constructively.

## Subsequent choice-free inverse construction

After this removal, global log/exp equivalence was constructed using a
deterministic arithmetic iteration with geometrically bounded increments.
This supplies native Cauchy data directly; none of the removed adapters or
assumptions was restored. `Exponential/Inverse.agda` exports the equivalence
and `Logarithm/Global.agda` its named inverse and laws. See
[the logarithm notes](LOGARITHM_2026-09-06.md) for the construction and its
verification. The removal inventory above describes the earlier cleanup.

## Recovery

Before deletion, the complete Analysis directory, including uncommitted
files, was archived at:

`/tmp/cubical-analysis-before-choice-removal.gpJRDS/Analysis-before-removal.tar.gz`

This is a temporary recovery archive, outside the source tree; it is not an
importable compatibility layer and may be removed by system temporary-file
cleanup. Tracked original versions also remain in Git history.

## Verification

- All **16 changed/new Agda files** were checked with
  `agda-codex --codex-format=json` after their final edits. Both
  `Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda` were also
  checked: **18 clean checks**, exit code 0, current-source snapshots, and
  zero holes, unsolved metas, constraints, or warnings.
- The source/document audit finds no prohibited schema or adapter references
  anywhere in Analysis, and no remaining `Choice.agda` modules.
- The dependency audit reaches all **405 Analysis modules** from
  `Cubical.Analysis.Everything`, with no missing imports or orphan modules.
- A repository-wide source search found no remaining imports of the removed
  Analysis modules or uses of their removed named inverse adapters.
- `git diff --check` is clean. The pre-removal archive was used to identify
  this cleanup's edits separately from the preceding dirty working tree.
