# Trigonometry and pi refactoring

Current policy: [AGENTS.md](AGENTS.md). The
[choice-free cleanup](CHOICE_FREE_2026-09-06.md) removed all countable-choice
adapters; generic inverse laws and finite density results are retained.

## Starting point

2026-09-04. The preceding Analysis refactor is committed as `fe2ee0d0e`.
`Cubical/Analysis/Everything.agda` checks the complete Analysis import graph.

At the starting checkpoint, the trigonometry development proved total sine and cosine, their
derivatives, addition and parity laws, sharp bounds, and quarter-turn laws.
Pi is represented by `CharacterizedHalfPi`: a positive first cosine zero with
cosine positive before it. The Bishop and damped Bishop constructions still
require convergence witnesses; there is no unconditional `piℝ`.

Restricted sine had an embedding and several conditional equivalence routes,
but no named inverse function. There was no corresponding restricted cosine
inverse API. The two substantive analytic boundaries are construction of a
characterized half-pi and restricted-sine intermediate value/surjectivity.

## Working plan

1. Trace the pi, quarter-turn, and restricted inverse dependencies; identify
   reusable arguments and redundant assumptions.
2. Simplify the pi/iteration proofs with existing sequence and continuity
   theorems, preserving the actual existence obligations.
3. Build named restricted sine and cosine inverses from the checked
   equivalence boundary, sharing interval geometry and inverse laws.
4. Reduce duplicated adapters where the simpler interfaces allow it, and
   pursue analytic gaps when existing lemmas make a local proof possible.
5. Check every changed Agda file with `agda-codex` and finish with the complete
   Analysis check. Record successful changes, failed approaches, and remaining
   mathematical obligations here.

## Progress and findings

- Initial inspection: the pi README accurately distinguishes characterization
  from existence. No convergence or choice assumptions should be silently
  removed while simplifying the API.
- Restricted cosine can be obtained from restricted sine by reflecting the
  interval about the quarter turn: `x ↦ quarter - x` sends `[0, 2*quarter]`
  to `[-quarter, quarter]`. This should share both the equivalence proof and
  inverse construction, with `arccos y = quarter - arcsin y`.
- Checked: sequence-limit uniqueness and vanishing successive differences now
  live in `Real.Sequence`; the Bishop-specific names are compatibility
  re-exports. `summableTermsTendToZero` uses the shared difference theorem.
- Checked: `Restriction.Inverse` provides a named restricted arcsine, both
  inverse laws, the real-valued sine equation, and independence from the
  chosen equivalence proof.
- Checked: reflection gives an isomorphism between the cosine half interval
  `[0, quarter + quarter]` and the sine quarter interval `[-quarter, quarter]`.
  Its geometry does not require any trigonometric assumptions.
- Checked: constructing a symmetric interval member from an absolute bound
  is now shared in `Domain.Interval`; restricted sine's former duplicated
  upper/lower-bound proof is replaced by this helper.
- Candidate further simplification: sine orientation at a first positive
  cosine zero may follow from a one-sided derivative-sign argument, avoiding
  a separate `sin(halfPi) = 1` input. This needs a checked endpoint derivative
  lemma; it is not assumed in the current interfaces.
- Checked: restricted cosine is an equivalence by composition with interval
  reflection. The named arccosine shares arcsine, satisfies both inverse laws,
  and is independent of the sine-equivalence proof. Both inverses have
  uniqueness principles stated directly in terms of the real sine/cosine.
- Checked: both inverse functions are continuous from a radiuswise sine
  closeness-reflection modulus, without selecting a global modulus or adding
  a choice assumption.
- Compiler finding: chaining a projection equality underneath transparent
  `sinℝ` caused excessive normalization. Giving the intermediate equality a
  concrete type and using a one-sided `subst` made the cosine proof check.
- A smaller orientation argument is now being pursued: differentiability at
  zero gives positive sine at small positive rational `h`; the addition law
  gives `cos(q-h) = sin(q)*sin(h)` when `cos(q)=0`. The characterization makes
  the left-hand side positive, so `sin(q)>0`. This avoids a new general
  endpoint derivative theorem.
- Checked: `Pi.Orientation` proves `firstPositiveCosineZero-sinePositive`
  and `firstPositiveCosineZero-sineOne`. The additional sine-orientation
  obligation is discharged, without changing the characterization or adding
  axioms. A small-step lemma over real variables avoids expanding the series
  while specializing to a rational witness.
- Checked: inverse endpoints are `arcsin(-1)=-quarter`, `arcsin(1)=quarter`,
  `arccos(-1)=halfTurn quarter`, and `arccos(1)=0`.
- Checked: `Pi.Inverse` specializes both inverses, both pairs of inverse laws,
  the real sine/cosine equations, and continuity to a characterized half-pi.
  The caller supplies only the characterization and the sine intermediate-
  value witness. The new equivalence adapters use the derived orientation.
- Refactoring: the opaque continuity-of-limits helper is shared in
  `Real.Sequence`, with compatibility re-exports for both Bishop variants.
  Nine bundled pi/sine equivalence adapters now reuse their corresponding
  `isEquiv` theorem instead of repeating the entire construction.

## Remaining mathematical boundaries

Finite bisection density is now checked, as recorded in the
[implementation log](IMPROVEMENTS_2026-09-05.md). It does not establish exact
surjectivity. The former choice-based inverse route was intentionally removed;
exact IVT and unconditional pi must be developed constructively.

1. An inhabitant of `CharacterizedHalfPi` is still not constructed. The
   iteration limits remain conditional on Cauchy witnesses, and the first-
   zero positivity condition must still be proved. Pi remains defined as
   twice a *supplied* characterized half-pi. No unconditional `piℝ` was added.
2. Restricted-sine intermediate value (or one of the documented approximate/
   rational construction routes) remains an input. The new inverse API does
   not pretend to establish surjectivity. No independent cosine-IVT proof is
   needed after sine is handled.
3. The radiuswise inverse-continuity theorem does not claim a chosen global
   uniform-continuity modulus. Such quantitative data must be supplied or
   constructed, not recovered by assuming a countable-choice schema.

The former sine-orientation obligation is **no longer on this list**: it is
proved from the existing first-positive-cosine-zero characterization.

## Verification

These figures describe the original refactoring pass, before the later
choice-free cleanup; current validation is recorded in its linked removal note.

- The import-graph audit finds 363 Analysis modules, all reachable from
  `Cubical.Analysis.Everything`, including every new module.
- Every new mathematical result above has checked with `agda-codex`, exit 0.
- Final validation ran `agda-codex --codex-format=json` on all 23 changed/new
  Agda files, `Cubical/Analysis/Everything.agda`, and `Cubical/Analysis.agda`:
  all 25 commands exited 0, with zero holes, unsolved metas, constraints, or
  warnings. The full Analysis graph contains 363 checked modules.
- `git diff --check` passed. No postulates, unsafe pragmas, weakened compiler
  options, or changes outside `Cubical/Analysis/` were introduced in this pass.
