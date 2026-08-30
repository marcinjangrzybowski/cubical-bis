# Performance audit of `Cubical.Analysis`

Date: 2026-08-30

Status: baseline audit plus the first measured implementation pass.  The
pre-optimization tree is preserved in checkpoint commit `d3bf8de33`.

## Executive summary

The main performance problem is not the amount of source code.  The 53 Analysis
entry points considered here have about 5,600 source lines, but their generated
interfaces total about 57.1 MiB.  Eight interfaces account for 69.6% of that
space.  The worst cases are `Real.Algebra.Addition` and
`Real.Algebra.Lattice.Base` at about 7.8 MiB each, and
`Completion.BinaryNonExpanding` at 5.2 MiB.

The most expensive local check is
`Completion.BinaryNonExpanding`: 44.4 seconds and 6.61 GiB peak resident memory
in the isolated measurement used below.  Its implementation constructs a
binary extension twice:

1. through sequential product completion; and
2. through regular completion, followed by comparison isometries.

It then proves the two functions equal and transports non-expansion proofs
along that equality.  Almost all of this proof machinery is transparent and
therefore remains available to normalization and is serialized into downstream
interfaces.  Addition and maximum both specialize this construction and store
the result in a bundled binary non-expanding record.  This is the most plausible
explanation for their unusually large interfaces and high memory use.

The follow-up implementation tested selective opacity first.  It did not
measurably change local checks or interface sizes and was reverted.  The
decisive improvement was to stop constructing the lift twice: unary and binary
non-expanding lifts now use the regular-completion lift transported through the
existing isometries as their sole implementation.  Their public operation,
non-expansion, extensionality, and injection theorem types are retained, as are
the original `Construction` names through compatibility aliases.

The remaining priorities are:

- add binary and ternary non-expanding/Lipschitz extensionality and use the
  weakest adequate theorem in algebraic laws;
- seal `_≤ℝ_` and `GapBound` behind small introduction/elimination lemmas;
- narrow the `Order`, `Real`, and root barrel exports; and
- prototype the newer direct binary sequential lift and
  compare its computational behavior with the now-faster transported lift.

The bounded/clamped multiplication technique from `CauchyRealsP` is valuable
for future locally uniform functions such as inversion.  It is not yet a good
first replacement for Analysis multiplication: the current multiplication
kernel has useful judgmental rational computation and is not the dominant local
hotspot.  Opacity around its completion-centred witness was tested, preserved
both `refl` rules, but did not improve the measurements and was reverted.

## Implementation follow-up

The first optimization pass applied three changes:

1. `Completion.Extensionality` now instantiates the
   construction-independent dense completion presentation and uses its direct
   extensionality theorem.  It no longer transports the compared functions
   through regular completion.
2. `Real.Extensionality` is a lightweight module imported directly by
   algebraic and order laws.  `Real.UniversalProperty` now contains only the
   stronger graph-Cauchy mapping-space API and re-exports the lightweight
   surface for compatibility.  Unused uniformly-continuous and
   completion-centred module aliases were removed.
3. `Completion.NonExpanding` and `Completion.BinaryNonExpanding` retain one
   implementation rather than building a sequential/product implementation,
   building a regular implementation, proving them equal, and transporting
   quantitative proofs between them.

The third change deliberately chooses the transported regular lift.  Thus the
exported injection equations remain available propositionally, but the lifted
functions no longer have the old sequential implementation's definitional
behavior on arbitrary sequential constructors.  All in-tree clients use the
exported computation theorems, and the complete Analysis root checks.  This
trade-off should nevertheless be considered when stabilizing the public API.

Measured before/after results are:

| Target | Wall time | Peak RSS | Interface bytes |
| --- | ---: | ---: | ---: |
| unary non-expanding lift | 9.11 → 4.51 s | 2.45 → 1.66 GiB | 2,747,938 → 1,615,301 |
| binary non-expanding lift | 44.37 → 9.29 s | 6.61 → 2.41 GiB | 5,493,985 → 2,578,501 |
| real addition | 10.68 → 4.96 s | 4.56 → 2.30 GiB | 8,222,917 → 3,882,707 |
| real lattice base | 10.87 → 5.37 s | 4.80 → 2.41 GiB | 8,232,020 → 3,876,150 |
| real universal property | 4.43 → 2.01 s | 1.64 → 0.92 GiB | 2,663,877 → 114,849 |
| Analysis root facade | 8.70 → 4.22 s | 2.71 → 1.91 GiB | — |

The new `Real.Extensionality` interface is 1,031,477 bytes.  Counting it
together with the reduced universal-property interface still halves that
surface: 2,663,877 bytes becomes 1,146,326 bytes.  Addition-laws improves more
modestly, from 3.09 to 2.92 seconds, because loading Addition itself remains
the dominant part of that check.

After a coherent root rebuild, all Analysis source interfaces—including the
new extensionality module—total 37,903,360 bytes, down from 59,909,364 bytes.
This is a 36.7% reduction while adding one module.

Two negative results are worth retaining:

- opacity around only the final unary/binary non-expansion fields did not
  alter the relevant time, memory, or interface measurements; and
- opacity around multiplication's completion-centred witness did not shrink
  its own or Multiplication-laws' interface and slightly increased its local
  check, so it was reverted.

## Scope and interpretation

This audit concerns Agda checking performance: elaboration time, normalization,
memory use, interface size, dependency fan-out, and the cost of importing public
facades.  It does not measure execution time of extracted programs.

The measured tree was an active working tree rather than a clean release
checkout.  In particular, `Cubical.Analysis` and some adjacent completion APIs
are under development.  The measurements are consequently a baseline for this
workspace, not a claim about an upstream release.  The baseline sections below
describe checkpoint `d3bf8de33`; the implementation follow-up above records the
subsequent Agda changes.

## Method

Static inspection covered:

- all 52 `.agda` files below `Cubical/Analysis`, plus
  `Cubical/Analysis.agda`;
- internal import fan-out and public module aliases;
- generated `.agdai` sizes corresponding to source files;
- `Cubical/HITs/CauchyReals` and `Cubical/HITs/CauchyRealsP`, especially their
  universal properties, algebra, order, multiplication, and migration notes;
- adjacent completion APIs already present in the working tree.

For a local-check measurement, only the target interface was moved aside,
dependencies were left current, and the target was checked with
`agda-codex --no-write-interfaces --profile=modules`.  `/usr/bin/time -l`
provided peak resident memory.  The original interface was then restored.
This isolates the cost of rechecking one module reasonably well, while still
including loading its dependency interfaces.

All reported isolated checks completed with exit status 0.  They are single
runs with a warm filesystem cache, so small differences should not be treated
as statistically significant.  The large factors and multi-GiB peaks are large
enough to guide experiments.

Machine and tool context:

- Apple M4 Pro, 14 cores, 52 GiB RAM;
- macOS 15.7.9;
- Agda 2.9.0 through `agda-codex`.

## Shape of the Analysis tree

The Analysis layer is small in source size but has a wide foundational spine.
The following modules have the largest transitive Analysis fan-out:

| Module | Downstream Analysis modules |
| --- | ---: |
| `Real.Base` | 46 |
| `Completion.Extensionality` | 45 |
| `Completion.BinaryNonExpanding` | 41 |
| `Real.Algebra.Addition` | 39 |
| `Real.UniversalProperty` | 39 |
| `Real.Algebra.AdditionLaws` | 38 |
| `Completion.NonExpanding` | 37 |
| `Real.Algebra.Negation` | 36 |
| `Real.Algebra.AdditiveGroup` | 32 |
| `Real.Algebra.Lattice.Base` | 29 |
| `Real.Algebra.Multiplication.Base` | 25 |

This means a term-size or transparency problem in a small number of modules is
multiplied across almost the whole tree.  Addition is particularly important:
it has 23 direct Analysis importers and 39 transitive dependants.

### Interface-size concentration

The 53 corresponding Analysis interfaces total 59,909,364 bytes (57.1 MiB).
The largest are:

| Interface | Bytes | MiB |
| --- | ---: | ---: |
| `Real/Algebra/Lattice/Base.agdai` | 8,232,020 | 7.85 |
| `Real/Algebra/Addition.agdai` | 8,222,917 | 7.84 |
| `Completion/BinaryNonExpanding.agdai` | 5,493,985 | 5.24 |
| `Real/Algebra/Multiplication/Base.agdai` | 5,370,424 | 5.12 |
| `Real/Algebra/AbsoluteValue.agdai` | 4,683,022 | 4.47 |
| `Real/Algebra/Negation.agdai` | 4,263,523 | 4.07 |
| `Completion/NonExpanding.agdai` | 2,747,938 | 2.62 |
| `Real/UniversalProperty.agdai` | 2,663,877 | 2.54 |

Those eight interfaces contain 41,677,706 bytes, or 69.6% of the Analysis
interface total.

For context:

| Tree | Sources/interfaces counted | Total interface bytes | Mean bytes | Interfaces over 1 MiB |
| --- | ---: | ---: | ---: | ---: |
| `Cubical.Analysis` | 53 / 53 | 59,909,364 | 1,130,365 | 10 |
| `CauchyRealsP` | 131 / 131 | 27,332,754 | 208,647 | 0 |
| `CauchyReals` | 308 / 304 present | 63,707,475 | 209,564 | 0 |

The comparison is not controlled for architecture, imports, or feature set.
It nevertheless identifies a real serialization problem: the compact Analysis
tree produces nearly as many interface bytes as the much larger legacy tree,
and more than twice as many as `CauchyRealsP`.

Examples of the scale difference are:

| Roughly corresponding modules | Analysis | Comparison | Ratio |
| --- | ---: | ---: | ---: |
| addition | 8,222,917 B | `CauchyRealsP`: 223,265 B | 36.8x |
| multiplication base | 5,370,424 B | `CauchyRealsP`: 215,181 B | 25.0x |
| negation | 4,263,523 B | `CauchyRealsP`: 180,841 B | 23.6x |
| real/foundation base | 1,011,240 B | `CauchyRealsP`: 186,761 B | 5.4x |

The lattice and absolute-value comparisons show similarly large factors, but
their module boundaries are less directly comparable.

## Representative local-check measurements

### Analysis

| Module | Wall time | Peak RSS |
| --- | ---: | ---: |
| `Completion.Extensionality` | 2.49 s | 1.20 GiB |
| `Completion.NonExpanding` | 9.11 s | 2.45 GiB |
| `Completion.BinaryNonExpanding` | 44.37 s | 6.61 GiB |
| `Real.UniversalProperty` | 4.43 s | 1.64 GiB |
| `Real.Algebra.Addition` | 10.68 s | 4.56 GiB |
| `Real.Algebra.AdditionLaws` | 3.09 s | 1.51 GiB |
| `Real.Algebra.Multiplication.Base` | 13.38 s | 2.45 GiB |
| `Real.Algebra.Lattice.Base` | 10.87 s | 4.80 GiB |
| `Real.Order.Base` | 3.92 s | 1.92 GiB |
| `Real.Order.Strict.Base` | 3.99 s | 2.01 GiB |
| `Real.Order.Strict.Located` | 5.41 s | 2.36 GiB |

### Comparison modules

| Module | Wall time | Peak RSS |
| --- | ---: | ---: |
| `CauchyRealsP.Algebra.Addition` | 1.93 s | 0.90 GiB |
| `CauchyRealsP.Algebra.AdditionLaws` | 1.75 s | 0.86 GiB |
| `CauchyRealsP.Foundation.UniversalProperty` | 1.70 s | 0.77 GiB |
| `CauchyRealsP.Algebra.Multiplication.Base` | 1.87 s | 0.90 GiB |
| `CauchyRealsP.Algebra.Order.Base` | 1.78 s | 0.84 GiB |
| `CauchyRealsP.Algebra.Order.Strict` | 1.89 s | 0.87 GiB |
| `CauchyReals.Foundation.UniversalProperty` | 1.47 s | 0.69 GiB |
| `CauchyReals.Algebra.Multiplication` | 2.44 s | 1.01 GiB |
| `CauchyReals.Algebra.Ring` | 1.84 s | 0.92 GiB |

The Analysis root and its large facades also have a meaningful import-only
cost, even with all dependency interfaces current:

| Facade | Wall time | Peak RSS |
| --- | ---: | ---: |
| `Cubical.Analysis` | 8.70 s | 2.71 GiB |
| `Cubical.Analysis.Real` | 8.87 s | 2.76 GiB |
| `Cubical.Analysis.Real.Algebra` | 4.92 s | 2.20 GiB |
| `Cubical.Analysis.Real.Order` | 4.97 s | 2.49 GiB |

For comparison, the `CauchyRealsP` and legacy algebra facades took 2.71 s /
1.03 GiB and 2.16 s / 1.06 GiB respectively.

### Rebuild observations

During recovery from a stale foundational interface, checking Addition took
62.75 seconds and 5.99 GiB.  A following check of the Analysis root regenerated
the remaining affected Analysis interfaces in 68.96 seconds and 6.37 GiB.
These are two consecutive recovery stages, not a single clean-build time.

As a separate stress probe, all Analysis interfaces were temporarily hidden and
the root was checked without writing interfaces.  It was still running after
72.8 seconds and had reached 11.87 GiB RSS, at which point it was interrupted to
avoid wasting resources.  This is deliberately recorded as a non-completing,
controlled probe, not as a cold-build benchmark.  All moved interfaces were
restored.

## Main hotspots and why they are expensive

### 1. The binary non-expanding lift builds and relates two implementations

`Completion/BinaryNonExpanding.agda` instantiates a large collection of
parameterized modules for:

- the two input completions and target completion;
- product premetrics and product completions;
- sequential and regular-completion comparison maps;
- uniformly continuous and completion-centred lifts; and
- unary and binary extensionality.

Its `Construction` first defines the desired sequential function via a product
completion.  It separately constructs a regular-completion function, transports
that function through comparison isometries, proves by nested continuous
extensionality that it is equal to the sequential implementation, and transports
non-expansion proofs across the equality.

This is mathematically modular, but it is a poor transparency boundary.  The
expensive comparison proof is needed to certify the function, not to compute
with it.  Keeping it transparent exposes a large normalization graph to every
specialization and serializes that graph into interfaces.  The 44.37 s /
6.61 GiB local check and 5.24 MiB interface make this the first target.

`Completion/NonExpanding.agda` follows the same unary pattern at smaller scale:
a sequential function, a regular lift transported through comparisons, an
equality between the two, and a transported non-expansion proof.

Recommended boundary:

- keep `sequentialFunction` and `sequentialFunction-ι` transparent;
- make the regular base, transported maps, comparison equality, and transported
  non-expansion proofs opaque;
- construct the public bundled value from the transparent function and opaque
  proof constants; and
- make the internal `Construction` and parameterized aliases private unless a
  public type genuinely requires them.

The regression gates are `liftBinaryNonExpanding-ι`, Addition's `rat+rat`, and
Lattice's `max-rat`.  They should retain their present computation/proof shape.

### 2. Addition and maximum package a small function with a very large proof

`Real/Algebra/Addition.agda` packages addition as a binary non-expanding record
and defines `_+_` by projecting its function field.  Lattice does the same for
`maxℝ`.  Their interfaces are both about 7.8 MiB, and their local checks use
4.56 and 4.80 GiB respectively.

The public operation is computationally simple, but its transparent definition
points through a record containing the expensive certification above.  A useful
local experiment is to define the function directly from the sequential lift,
and put its non-expanding fields in separate opaque definitions.  This should
reduce how often normalizing `_+_` or `maxℝ` reaches the entire proof bundle.

This separation should be attempted after, or together with, opacity inside the
generic lift.  Otherwise it may only move the large term rather than shrink it.

### 3. Real universal property mixes a common theorem with broad machinery

`Real/UniversalProperty.agda` publicly instantiates extensionality,
Cauchy-continuous, uniformly continuous, and completion-centred modules.  Within
Analysis, downstream clients predominantly import it for
`continuousExtensionality`, including its binary and ternary forms.  The
uniformly continuous and completion-centred aliases are not used by those
clients.

Split a small `Real.Extensionality` module from the complete mapping-space
universal property.  Make generic aliases private and re-export only named
theorems.  This lowers fan-out and gives law modules a cheaper import target.

There is a further structural opportunity described below: instantiate the
newer construction-independent completion presentation and prove extensionality
directly from density, rather than transporting through regular-completion
comparisons.

### 4. Extensionality is sometimes stronger than the quantitative data requires

The current Analysis completion extensionality layer provides unary
non-expanding and Lipschitz extensionality, but only continuous binary and
ternary extensionality.  Addition and lattice laws therefore use general
continuous extensionality even though their operations carry quantitative
moduli.

Add binary and ternary forms of non-expanding/Lipschitz extensionality, then use
the weakest sufficient principle in algebraic laws.  This is the pattern used
more consistently in `CauchyRealsP`.  The expected benefit is smaller
continuity witnesses and less normalization; it should be measured rather than
assumed, because the present Addition-laws check is already much cheaper than
the Addition definition itself.

### 5. Order exposes definitions that repeatedly unfold expensive operations

Analysis defines `_≤ℝ_` transparently as `maxℝ x y ≡ y`.  Strict order then
defines `GapBound` transparently using addition and this non-strict order.
Consequently, elaborating elementary order propositions can expose both large
binary operation definitions.

`CauchyRealsP` found this exact boundary important: its order relation and
`GapBound` are opaque, with small introduction and elimination lemmas.  Its
migration notes report changes from minutes to roughly seconds for the affected
checks.  Analysis should try the same shape:

- make `_≤ℝ_` opaque;
- expose focused lemmas for constructing and consuming the max equality;
- make `GapBound` opaque;
- expose `gapBoundIntro` and `gapBoundElim`; and
- use explicit `unfolding` only in the small base modules that prove the API.

The current `Real.Order.Base` and `Real.Order.Strict.Base` checks already use
about 2 GiB each despite being small source files, so this is a credible
second-wave target.

### 6. Multiplication has a large interface, but its computational rule matters

`Real/Algebra/Multiplication/Base.agda` proves a completion-centred property and
passes the proof to the sequential lift.  The result has a 5.12 MiB interface.
Unlike addition's rational rule, both `multiplyℝ²-rat` and `multiplyℝ-rat` are
currently proved by `refl`.

Do not make the multiplication function opaque indiscriminately.  First seal
only proof-only objects such as `multiplyℚ-completionCentered` and internal
bound/continuity witnesses.  After each change, require the two rational lemmas
to remain accepted with `refl`.  If an opacity boundary breaks that behavior,
keep the computational kernel transparent and expose an opaque theorem wrapper
around the heavy certification instead.

The local multiplication check, 13.38 s / 2.45 GiB, is significant but much
smaller than the binary-lift hotspot.  This argues for improving its boundaries
before replacing its construction.

### 7. Public module aliases and barrels amplify the core costs

Several generic completion files and multiplication expose many parameterized
module aliases publicly.  Search found no Analysis clients using most of these
namespaces directly.  Public aliases enlarge scope and can retain generic
environments in interfaces; any alias required only to define a named theorem
should be private.

`Real.Algebra` has already benefited from curated `using` exports, as recorded
in `PROGRESS.md`.  In contrast, `Real.Order` publicly opens thirteen modules
without a similarly narrow export list, while `Real` and the root re-export
large facades.  The 5--9 second, 2--3 GiB facade checks show that export curation
is still worthwhile.

Prefer an explicitly curated default facade.  If a comprehensive convenience
import is wanted, separate `Core` and `All` facades rather than making every
client pay for all order and analysis machinery.

## Techniques from the two Cauchy-real developments

The comparison should be treated as a source of boundaries and proof patterns,
not as evidence that Analysis should copy either architecture wholesale.

### Techniques to adopt directly

#### Selective `opaque` with narrow `unfolding`

The legacy Cauchy-real tree uses opacity extensively: 551 `opaque` blocks and
139 `unfolding` occurrences in the inspected tree.  `CauchyRealsP` uses far
fewer—15 opacity blocks and 4 unfolding occurrences—but places them at
high-leverage definitions such as order, gaps, and total multiplication.
Analysis currently has one `opaque` block.

Interface sizes strongly correlate with this difference, although opacity is
not the only cause: the legacy development also has a different HIT
architecture.  The transferable lesson is to put opacity around proof and
comparison machinery, then unfold only at a small trusted API boundary.

#### Name and seal canonical witnesses before dependent use

`CauchyRealsP` repeatedly names truncation-derived witnesses, bounds, and
canonical data before mentioning them in dependent result types.  Its migration
notes record cases where this restores checks of roughly two seconds.  This
prevents elaboration from duplicating a proof-producing expression and trying
to compare two large dependent normal forms.

Apply this in Analysis whenever a chosen approximation, positive gap, modulus,
or bound appears both in data and in a proof indexed by that data.  Bundle the
witness and its property when they naturally travel together.

#### Prefer non-dependent elimination for proposition-valued goals

The `CauchyRealsP` migration found dependent splitting to be a source of stalls.
When the target is a proposition, eliminate truncations or cases into a fixed
proposition and keep the chosen witness out of the result type.  Use dependent
elimination only when the returned data genuinely depends on the witness.

#### Prove exact equalities before quantitative consequences

Both comparison trees get better behavior by isolating a small algebraic path,
then deriving distance/order bounds from it.  They also use uniqueness of limits
or sequence paths rather than equality between proof-heavy convergence
witnesses.  This is particularly relevant to future series and limit work.

#### Use explicit local algebraic paths instead of a generic solver

`CauchyRealsP` records a case where a solver exceeded 30 seconds while an
explicit path checked in under two.  The legacy ring solver can also interact
poorly with opaque multiplication.  Analysis currently has no solver dependency
in this layer; keeping short, named algebraic paths is the right default.

#### Make parameters, endpoints, and moduli explicit at difficult boundaries

Explicit binder types and module parameters prevent metas from spanning a large
generic environment.  `CauchyRealsP` uses this together with named helper
lemmas, including splitting positive and negative branches.  This is a local,
low-risk response when a small theorem unexpectedly allocates gigabytes.

### Techniques to adapt rather than copy

#### Bounded/clamped multiplication and gluing

`CauchyRealsP` obtains total multiplication in three stages:

1. clamp rational inputs to a bounded interval, yielding a globally Lipschitz
   map;
2. prove exact compatibility when the bound is enlarged; and
3. choose merely existing natural bounds and glue the bounded operations using
   propositional truncation elimination.

Its common-bound infrastructure gives stable names to the bounds and endpoint
equalities.  This is an excellent general recipe for functions that are only
uniformly continuous on bounded sets.  Likely Analysis uses include inversion
away from zero, bounded powers, and future analytic functions.

For current multiplication it is a fallback, not the first action.  The
completion-centred Analysis construction is shorter and preserves judgmental
rational computation.  Introduce the bound hierarchy only if this module
becomes the dominant remaining hotspot or future locally uniform operations
need the shared infrastructure.

#### Opaque operation definitions

The legacy tree makes major operations opaque and selectively unfolds them in
proofs.  This gives compact interfaces, but Analysis explicitly values direct
constructor computation.  Adopt opacity for certifications and transport
proofs first.  Make an operation itself opaque only after checking all desired
`refl` rules and deciding that propositional computation is acceptable.

### Techniques not worth importing now

- Replacing the sequential-completion design with the legacy custom HIT and its
  eliminators would be a broad rewrite and would obscure the current audit.
- Building a full bounded multiplication hierarchy before testing proof opacity
  would add complexity without addressing the measured dominant hotspot.
- Adding a generic ring/order solver is unlikely to solve normalization costs
  and can make opaque-operation proofs worse.
- Compiler parallelism is not the primary remedy.  These measurements show
  single-module normalization and memory pressure; parallel checking could
  increase peak memory.

## Promising adjacent APIs in the current working tree

These APIs are not part of the requested historical comparison and appear to be
under active development, so they should first be used in prototypes.

### Direct binary Cauchy-continuous sequential lift

`Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous.Binary`
constructs a genuinely binary lift from a binary graph condition.  It avoids
forming a product premetric and product completion.  Expensive uniqueness and
limit helpers have opacity boundaries, and the module exposes direct
`ι-ι`, `ι-lim`, `lim-ι`, and nested `lim-lim` computation rules.  Its present
interface is about 0.36 MiB, compared with 5.24 MiB for Analysis binary
non-expansion.

A high-value prototype is to build a binary non-expanding wrapper on this API
and instantiate rational addition or maximum.  Measure it before migrating:
the direct lift still needs a quantitative non-expansion proof, so interface
size alone does not establish that the complete specialization will be cheap.

### Construction-independent completion presentation

`Cubical.Relation.Premetric.Completion.UniversalProperty.Base` packages a
completion premetric, a dense isometric injection, and no knowledge of its
constructors.  Its `Extensionality` module proves equality directly from density
and continuity.  `NonExpanding` packages a reusable non-expanding universal
property and extension/restriction isomorphism.

The implementation follow-up now instantiates this presentation for sequential
completion from its injection, reflection, and density theorems.  Analysis
extensionality therefore no longer transports the compared maps through
regular completion.  The local check changed little, but the proof has a
smaller and construction-independent surface.

## Prioritized improvement plan and disposition

### Completed or tested

1. **Proof-only opacity:** tested in unary and binary lifts; no measurable
   effect, reverted.
2. **Single lift construction:** implemented in unary and binary lifts; large
   reductions in time, memory, and interface size.
3. **Lightweight real extensionality:** implemented; law modules import it
   directly while `Real.UniversalProperty` re-exports it for compatibility.
4. **Construction-independent extensionality:** implemented using the dense
   completion presentation.
5. **Multiplication witness opacity:** tested with explicit local types; both
   rational `refl` rules survived, but performance did not improve, so the
   experiment was reverted.

The decision rule—revert experiments that do not shrink an interface or local
check—was useful and prevented opacity from becoming an unmeasured style
change.

### P1: remaining focused improvements

1. Add binary/ternary quantitative extensionality and use it in quantitative
   algebra/lattice laws.
2. Seal `_≤ℝ_` and `GapBound` behind focused constructors/eliminators.
3. Prototype a binary non-expanding lift over the direct binary sequential API
   if constructor computation is important enough to justify it.
4. Privatize or narrowly re-export remaining implementation module aliases.

### P2: ecosystem and maintenance work

1. Curate `Order`, `Real`, and root facade exports; consider `Core` and `All`
   variants.
2. If repeated rational specializations remain costly, create a small
   rational-to-real lift module that instantiates the generic machinery once.
3. Add a reproducible performance harness and track wall time, peak RSS, and
   interface sizes in review or CI.
4. Use the bounded/clamped and common-bound pattern when implementing future
   locally uniform maps, rather than retrofitting it everywhere now.

## Experiment log and remaining sequence

Each experiment should be a small commit or easily reversible patch.  Run the
same isolated benchmark before and after, followed by a root check.

### Experiment 1: unary proof opacity — completed, reverted

Targets:

- `Completion.NonExpanding`;
- `Real.Algebra.Negation`;
- `Real.Algebra.AbsoluteValue`.

The computation lemmas survived, but time, RSS, and interface sizes were
unchanged.  Replacing the dual construction with the transported lift then cut
the unary check by about 51% and its interface by about 41%.

### Experiment 2: binary proof opacity — completed, reverted

Targets:

- `Completion.BinaryNonExpanding`;
- `Real.Algebra.Addition`;
- `Real.Algebra.Lattice.Base`;
- Analysis root.

Opacity alone did not meet the gate.  Removing the duplicate sequential/product
implementation cut the binary check by about 79%, peak RSS by about 64%, and
the interface by about 53%.  Addition and maximum retain their exported
rational computation theorems.

### Experiment 3: function/proof separation and private aliases — pending

Do this after Experiment 2 so its effect can be distinguished from opacity.
Inspect exported names as well as raw sizes; a private alias that is retained by
a public transparent body may not reduce the interface until that body is also
sealed.

### Experiment 4: lightweight extensionality — completed

The surface moved to `Real.Extensionality`.  The universal-property check fell
from 4.43 to 2.01 seconds and its interface from 2.66 MB to 0.11 MB.  Adding
quantitative binary and ternary variants remains pending.

### Experiment 5: order boundaries

Make `_≤ℝ_` opaque first and benchmark `Order.Base`, `Strict.Base`, and
`Strict.Located`.  Add the `GapBound` boundary in a separate step.  This keeps
the source of any improvement or regression visible.

### Experiment 6: architectural prototypes

In isolated, non-exported modules:

- implement rational addition or maximum through the direct binary lift; and
- only if needed, prototype bounded/clamped multiplication.

The construction-independent completion presentation is no longer a prototype:
it is now used by `Completion.Extensionality`.

Do not migrate clients until a prototype beats the current implementation on
both resource use and proof ergonomics.

## Measurement checklist

For every performance patch, record:

- exact source revision and whether dependency interfaces were current;
- the `agda-codex` exit status;
- local-check wall time and peak RSS;
- generated `.agdai` size;
- affected downstream interface sizes;
- root/facade import cost;
- whether public names changed; and
- whether computational regression lemmas still use `refl` where intended.

Recommended sentinel set:

- `Completion.NonExpanding`;
- `Completion.BinaryNonExpanding`;
- `Real.Algebra.Addition` and `AdditionLaws`;
- `Real.Algebra.Lattice.Base`;
- `Real.Algebra.Multiplication.Base`;
- `Real.Order.Base` and `Real.Order.Strict.Base`;
- `Cubical.Analysis.Real.Algebra`;
- `Cubical.Analysis.Real.Order`;
- `Cubical.Analysis`.

Do not rely on wall time alone.  An opacity change may leave the defining module
similar while greatly shrinking downstream interfaces and checks.  Conversely,
a small source cleanup that does not change serialized terms may have no useful
effect.

## Conclusions

The audit correctly located a concentrated problem in the generic unary and
binary completion lifts, but the initial opacity hypothesis was incomplete.
Opacity did not change the measured costs because the defining function still
contained the uniformly-continuous sequential construction and its proof
argument.  Removing the duplicate implementation was the effective boundary:
the binary lift became about 4.8 times faster, its peak memory fell by about
64%, and its interface was reduced by about 53%.

Splitting extensionality from the graph-Cauchy universal property produced a
second independent improvement.  It reduced the universal-property local
check by about 55% and its own interface by about 96%; even after counting the
new lightweight extensionality interface, the combined surface is less than
half the previous size.

The Cauchy-real developments remain useful guides: keep proof APIs narrow,
name dependent witnesses, use direct density rather than comparison transport
when available, and adopt bounded/glued constructions for genuinely local
continuity.  Their opacity strategy should be applied only where a benchmark
shows that clients were unfolding the sealed term.

The next most promising work is order/`GapBound` isolation, quantitative binary
and ternary extensionality, and export curation.  The direct binary sequential
API remains worth prototyping if its constructor computation is required; the
current faster implementation instead chooses transported regular lifts and
retains propositional injection computation.
