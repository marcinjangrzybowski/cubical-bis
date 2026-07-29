# Survey of branches on the `lorenzo` remote

Survey date: 2026-07-28

## Snapshot and methodology

The remote was refreshed with:

```text
git fetch --prune lorenzo
```

The comparison point was:

```text
current branch:  book-cauchy-reals-new-solvers
current HEAD:    02bad5da61b080fed1401eadd4b04ca8e947bd7c
upstream/master: 92166033326aa59800a580b428125f3c654b5e45
lorenzo/master:  92166033326aa59800a580b428125f3c654b5e45
```

There are 40 live remote-tracking branches after pruning. Deleted remote
branches are not included.

No merge, rebase, cherry-pick, or branch checkout was performed in the main
worktree. Compatibility was estimated using:

- ancestry and commits absent from the current HEAD;
- changed-file and overlapping-file sets;
- three-way `git merge-tree` previews;
- source-level comparison of independently evolved APIs;
- representative `agda-codex` checks at selected branch tips, in isolated
  temporary worktrees that were removed afterwards.

In the tables below, a “conflict file” means a file for which the merge-tree
preview produced actual conflict markers. It does not count files changed on
both sides that Git can merge automatically. A successful branch-tip check
only establishes that the selected file checks on that branch itself; it does
not establish that a hypothetical combined tree would check.

## Executive assessment

### Best candidate: `archimedean-ring-experiment-wip`

This is the only branch that currently looks suitable for a relatively direct
merge.

- Only three commits are absent from the current HEAD.
- It changes two files.
- Both files overlap with our work, but the merge-tree preview reports no
  textual conflicts.
- Both changed files check with `agda-codex` at the branch tip.
- The additions are useful to the present real-analysis development:
  `0≤→abs·≡`, `0≤→²≤²→≤`, and a premetric reasoning combinator.

Despite the `wip` name, this is the lowest-risk and most immediately useful
branch in the remote.

### Second candidate: `logN`

This is a reasonably self-contained addition of a general natural-number
logarithm.

- Four commits are absent from HEAD, of which two are substantive source
  commits.
- It changes four files and introduces
  `Cubical.Data.Nat.Logarithm`.
- The new logarithm module checks at the branch tip.
- The merge preview has two conflict files. Both conflicts are structurally
  understandable and concern moving multiplication-cancellation lemmas from
  `Fin.Properties` to `Nat.Order`.

It is worth merging if a general computational `log` on naturals is useful,
but it is not required by the current Cauchy-real logarithm development.

### Worth mining, but not merging wholesale

The active branches `fast-rational-wip`, `archimedean-ring`,
`premetric+fast-rationals`, and `completion-alternative-wip` contain valuable
work. They should be treated as sources for selective ports, not direct
merges. Our branch independently developed the same rationals, ordered-ring,
premetric, and completion modules, often with different public structure and
module names.

## Leading candidates

| Branch | Tip | Commits absent from HEAD | Changed files | Overlap with our changes | Conflict files | Representative tip check | Recommendation |
|---|---:|---:|---:|---:|---:|---|---|
| `archimedean-ring-experiment-wip` | `c1c17821d` | 3 | 2 | 2 | 0 | status 0 for both changed modules | Merge first on a test branch |
| `logN` | `2446e1d75` | 4 | 4 | 3 | 2 | status 0 for `Data.Nat.Logarithm` | Good, manageable candidate |
| `fast-rational-wip` | `b9e085816` | 3 | 12 | 12 | 7 | status 0 for the rational OCR instance | Port selected helpers only |
| `archimedean-ring` | `31b867ed8` | 23 | 10 | 7 | 6 | status 0 for `ArchimedeanRing.Properties` | Valuable redesign; do not merge directly |
| `ocr-update` | `ab1fc6f77` | 25 | 8 | 5 | 4 | covered by the same OCR tree as `archimedean-ring` | Superseded for evaluation by `archimedean-ring` |
| `premetric+fast-rationals` | `b1f88eae2` | 44 | 30 | 24 | 19 | status 0 for the product instance | Selective port and benchmarking only |
| `completion-alternative-wip` | `747b5297a` | 43 | 36 | 26 | 21 | status 0 for the completion facade | Research/reference branch |
| `reswatson_natsIntsPR` | `a6d20c631` | 2 | 5 | 4 | 3 | not separately checked | Mostly superseded by current upstream |

## Detailed candidate analysis

### `archimedean-ring-experiment-wip`

The three commits not present in HEAD are:

```text
2d3957948 added 0≤→abs·≡ (#52)
36093133c simplify proofs using the DSL; add 0≤→²≤²→≤
c1c17821d add begin≈[_]⟨⟩_; use it in isCauchySeq→isCauchy
```

Files:

```text
Cubical/Algebra/OrderedCommRing/Properties.agda
Cubical/Relation/Premetric/Properties.agda
```

The first two commits add:

- strict monotonicity of squaring on the nonnegative part;
- recovery of `x ≤ y` from `x² ≤ y²` when `y` is nonnegative;
- compatibility of absolute value with multiplication by a nonnegative
  scalar.

The last commit extends the premetric equational-reasoning DSL with a
zero-overhead step and rewrites `isCauchySeq→isCauchy` using the DSL.

Compatibility:

- no textual conflicts in the merge-tree preview;
- both changed branch-tip files return `agda-codex` status 0;
- the branch shares most of its history with the current development, leaving
  only these three small commits to integrate;
- risk is low, although the combined result should still be checked through
  the ordered-ring, premetric, Cauchy-analysis, and Complex facades.

Recommendation: this is the first branch to try as a real merge.

### `logN`

Substantive commits:

```text
0ce9b2022 add Data.Nat.Logarithm and supporting Nat lemmas
c167baf4d rewrite isPropLogℕ using with-abstraction
```

The branch adds a `Logℕ` specification, uniqueness, a terminating
implementation, and basic monotonicity/base laws. The branch-tip
`Cubical/Data/Nat/Logarithm.agda` returns status 0.

The two conflict files are:

```text
Cubical/Data/Fin/Properties.agda
Cubical/Data/Nat/Order.agda
```

Nature of the conflicts:

- our tree still defines `≤-·sk-cancel` in `Fin.Properties`;
- our tree already defines `<-·sk-cancel` in `Nat.Order`;
- `logN` moves both cancellation lemmas to `Nat.Order`, with shorter
  inductive proofs;
- unrelated local additions in both files must be retained.

`Cubical/Data/Nat/Mod.agda` overlaps but merged automatically in the preview.
The likely resolution is to keep the current unrelated `Fin` results, remove
the old local `Fin` copy of `≤-·sk-cancel`, and reconcile the two
`Nat.Order` cancellation proofs.

Recommendation: medium-low integration difficulty and worthwhile as a
standalone library improvement.

### `fast-rational-wip`

This is recent and its branch-tip rational ordered-ring instance checks.
However, it independently implements work already present in this branch:

- Fast-Int-based preferred rationals;
- reduced/normalized representatives;
- record-wrapped rational `<` and `≤`;
- set-quotient recursion/elimination records;
- rational order and algebraic instances.

All 12 changed files overlap our changes. The seven conflict files are:

```text
Cubical/Algebra/OrderedCommRing/Instances/Rationals.agda
Cubical/Relation/Binary/Order/Loset/Instances/Rationals.agda
Cubical/Relation/Binary/Order/Pseudolattice/Instances/Rationals.agda
Cubical/Relation/Binary/Order/Toset/Instances/Rationals.agda
Cubical/Data/Rationals/Base.agda
Cubical/Data/Rationals/Order.agda
Cubical/Data/Rationals/Properties.agda
```

The current rational `Order.agda` is 802 lines, while the candidate version is
631 lines. The current rational OCR instance also contains a large
positive-rational theory absent from the candidate version. Choosing either
side wholesale would therefore lose useful work.

The most attractive isolated change is commit `b9e085816`, which adds:

```text
subst≤  subst≤L  subst≤R
subst<  subst<L  subst<R
subst#  subst#L  subst#R
```

These helpers recompute order witnesses after transport and replace repeated
`recompute` plus `subst` patterns. They fit the present performance-oriented
rational implementation and can be ported manually into the current
`Rationals.Order`.

Recommendation: do not merge this branch directly. Port the substitution
helpers and inspect proof simplifications from `b9e085816`.

### `archimedean-ring` and `ocr-update`

At their tips, `archimedean-ring` has the same tree as `ocr-update` plus:

```text
Cubical/Algebra/ArchimedeanRing/Base.agda
Cubical/Algebra/ArchimedeanRing/Properties.agda
```

It is therefore sufficient to evaluate `archimedean-ring`; merging both would
be redundant.

Attractive additions include:

- ordered-commutative-ring morphisms;
- OCR univalence;
- uniqueness and monotonicity of the canonical integer embedding;
- integer upper and lower bounds in an Archimedean ring;
- `archimedeanPropertyℕ₊₁`;
- new Fast-Int commutative-ring and OCR instances.

The branch also changes the central Archimedean axiom from a positive-natural
multiplier formulation to:

```text
∀ x y → 0 < y → ∃[ k ∈ ℤ ] x < ι k · y
```

Our `IsArchimedeanRingℝ` and downstream Cauchy-real theory use the existing
positive-natural formulation. A direct merge would therefore require a
deliberate API migration, not merely conflict-marker resolution.

Six conflict files are reported, including add/add conflicts in both current
Archimedean modules and in `OrderedCommRing.Properties`. Our
`OrderedCommRing.Properties` has independently grown to about 1533 lines,
versus about 685 on the candidate branch, so neither version should replace
the other.

Recommendation:

1. do not merge the full branch yet;
2. decide whether the generalized Archimedean axiom should replace the
   current one;
3. separately port `OrderedCommRing.Morphisms` and
   `OrderedCommRing.Univalence`;
4. adapt the integer-bound lemmas to the chosen current Archimedean API.

### `premetric+fast-rationals`

This active branch contains valuable improvements:

- maximally level-polymorphic mapping equality principles;
- sequential-continuity lemmas;
- function-space, product, and generalized subspace instances;
- pre/post-composition and binary non-expansive combinators;
- `no-eta-equality` on `IsPremetric` as a typechecking-performance fix.

Its product instance checks at the branch tip. Nevertheless, a full merge is
not compatible with the current tree:

- 24 of its 30 changed files overlap ours;
- 19 files produce textual conflicts;
- the rational and OCR foundations also conflict;
- our premetric mapping, product, function-space, and completion theories
  have independently evolved;
- the candidate uses `Instances/SubSpace.agda`, while our tree has the
  independently developed `Instances/Subspace.agda`.

The `no-eta-equality` change is especially worth benchmarking in isolation:
the current `IsPremetric` does not have it. The level-polymorphism and product
or subspace improvements should likewise be ported as small, individually
checked changes.

Recommendation: use this as a source branch for focused performance and
generality improvements, not as a merge target.

### `completion-alternative-wip`

This branch develops an alternative completion whose constructors use a sum
in the codomain rather than a difference in the domain. It includes:

- completion closeness and lifting theory;
- elimination and properties;
- a `HIITReals` instance and examples.

The completion facade returns status 0 at the branch tip. This is useful
evidence that the branch is internally coherent, but the branch remains a poor
direct merge candidate:

- 21 conflict files;
- extensive add/add conflicts with the current premetric and completion
  hierarchy;
- an explicit WIP status;
- a commit noting very slow typechecking in part of the development;
- divergence from the newer product/subspace work on
  `premetric+fast-rationals`.

Recommendation: retain it as a design/reference branch. Port a construction
only after deciding that the alternative completion should coexist with or
replace the current one.

### `reswatson_natsIntsPR`

This branch adds and simplifies natural/integer GCD results. Most of its
standard-integer content has now arrived through upstream `master`, including
`Cubical.Data.Int.GCD`.

The remaining interesting file is a Fast-Int GCD adapter, but it uses the old
module path:

```text
Cubical/Data/Fast/Int/GCD.agda
```

The current tree uses the `Cubical/Data/Int/Fast/...` layout. If a Fast-Int GCD
facade is wanted, this small module should be translated to the current path
and imports rather than merging the branch. The direct preview reports three
conflict files in the already-updated Nat/Int GCD theory.

## Cross-branch compatibility observations

### Fast integer module layout

Several Lorenzo branches use `Cubical.Data.Fast.Int` and
`Instances.Fast.Int`. The current development standardized its active Fast
integer implementation under `Cubical.Data.Int.Fast`. Code copied from those
branches will often need import and instance-path translation even when the
underlying mathematics is compatible.

### Rational API

The current branch and the active Lorenzo rational branches both use Fast
integer operations, record-wrapped order witnesses, and quotient eliminators.
The concepts are compatible, but the developments are parallel rather than
linearly related. Direct merges create add/add conflicts and can silently
discard current positive-rational or solver-facing APIs.

### Ordered commutative rings

The current OCR theory is substantially larger than the active Lorenzo OCR
tip, while the Lorenzo branch has cleanly separated morphism and univalence
modules not present here. This favors porting the new modules against the
current large `Properties` module rather than choosing one version wholesale.

### Premetrics and completion

The current branch already contains premetric spaces, mappings, products,
function spaces, subspaces, and completion. The active Lorenzo branches add
similar structures with different organization and some useful performance
or generality changes. The theories are mathematically compatible but
source-incompatible without an API reconciliation pass.

### Old Cauchy-real branches

The old Cauchy-real branches are ancestors or alternative snapshots of a much
earlier development. The current branch has hundreds of commits and a much
larger, reorganized formalization beyond them. Their value is historical or
lemma-level; they should not be merged wholesale.

## Full branch inventory

### Already contained in the current HEAD

No action is needed for:

- `master` — exactly the upstream commit already merged into HEAD;
- `fast-int-update-without-order`;
- `fast-rationals`;
- `fast-rationals-wip`;
- `premetric-e-wip`;
- `pseudolattice-update-wip`.

The latter five tips are ancestors of the current HEAD.

### Active branches worth evaluating

- `archimedean-ring-experiment-wip` — best immediate merge candidate.
- `logN` — manageable independent feature.
- `fast-rational-wip` — port selected rational-order helpers.
- `archimedean-ring` — important redesign and new theory; requires API choice.
- `ocr-update` — tree-level subset of `archimedean-ring` at the tip.
- `premetric+fast-rationals` — mine performance and generality improvements.
- `completion-alternative-wip` — alternative completion reference.
- `reswatson_natsIntsPR` — only the Fast-Int GCD adapter remains interesting.

### Historical Cauchy-real branches

Do not merge these wholesale:

- `book-cauchy-reals`;
- `book-cauchy-reals-dirty`;
- `book-cauchy-reals-uniform`;
- `book-cauchy-reals-uniform-wip-lorenzo`;
- `reals-perf`;
- `cauchy--rebase-fast`;
- `cauchy--rebase-fast-w/o-abs'`.

The two `uniform` branches differ by one tip commit. The only item that may be
worth reviewing independently is the alternative `denseℚinℝ` proof in commit
`46396e84e`. The two `cauchy--rebase-fast` branches only change old
`Data.Rationals.Fast` absolute-value APIs, while the active preferred rational
development has moved elsewhere.

### Superseded or experimental Fast-Int, order, and GCD branches

- `compatible-gcd` — conflicts with the current `Nat.GCD` and `Nat.Mod`;
  current code already uses the efficient quotient/remainder implementation.
- `efficient-gcd` — earlier standalone version superseded by
  `compatible-gcd` and current GCD work.
- `fast-int-division` — older Fast-Int division stack.
- `fast-int-order-experiments` — experimental predecessor of the current Fast
  order implementation.
- `fast-int-wip` — old large WIP branch, including generated binaries and
  obsolete layout.
- `fast-rationals-extended` — explicitly marked as not typechecking.
- `min-fix-with-anshwad10-changes` — experiment around `UsingEq`, `min`, and
  `max`; related infrastructure is already present in the current tree.
- `mod-update` — explicitly contains holes.
- `nat-boolean-builtin` — older precursor to Nat boolean/`UsingEq` changes
  already represented in the current tree.
- `ocr+pl-instances` — old, reverted experiment predating the active OCR and
  Fast-Int modules.
- `ordering` — its `Ordering` addition is already present in the current
  `Relation.Binary.Base`, despite the commit not being an ancestor.

### Superseded ordered-ring/equational-reasoning branches

- `oer+ocr`;
- `oer+ocr-ettore`;
- `oer+ocr-lorenzo`;
- `oer+ocr-wip`;
- `order-eq-reas+ordered-comm-rings`;
- `ordered-commutative-rings`.

The four `oer+ocr*` refs all point to the same commit, `2f631bf81`. They are
historical predecessors of the active `ocr-update`/`archimedean-ring` work and
of the larger current OCR theory.

### Tests and deployment

- `StrictOrderEquationalReasoning-old-tests` contains only an old dedicated
  test module. It is not a source-feature merge candidate.
- `gh-pages` is generated documentation deployment state, not a source branch.

## Recommended integration order

1. Merge `archimedean-ring-experiment-wip` on a temporary integration branch.
   Check:

   ```text
   Cubical/Algebra/OrderedCommRing/Properties.agda
   Cubical/Relation/Premetric/Properties.agda
   Cubical/HITs/CauchyReals/Analysis.agda
   Cubical/HITs/CauchyReals/Complex.agda
   ```

2. If general natural logarithms are desired, merge `logN` separately and
   manually resolve the relocation of cancellation lemmas. Check Nat order,
   modulus, Fin properties, and `Data.Nat.Logarithm`.

3. Port commit `b9e085816` conceptually into the current rational order module,
   without merging the rest of `fast-rational-wip`.

4. Benchmark adding `no-eta-equality` to the current `IsPremetric`, based on
   `b1f88eae2`, before importing the larger premetric changes.

5. Treat adoption of the new `archimedean-ring` axiom as an explicit
   refactoring project. Port OCR morphisms/univalence independently first.

6. Keep `completion-alternative-wip` as a reference until there is a deliberate
   decision between the two completion architectures.
