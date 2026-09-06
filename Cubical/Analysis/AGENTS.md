# Choice-free Analysis

This directory must remain free of countable-choice assumptions. This is an
explicit project requirement, not merely a preference about exported APIs.

- Do not introduce positive-rational-indexed choice, sequential tail-choice
  schemas, propositional choice, or adapters that assume them, even as explicit
  theorem parameters. Do not hide the same assumption behind an alias, a new
  name, an instance, or a wrapper.
- Do not import or re-export choice-dependent completion comparisons or
  choice-dependent exact-IVT/inverse constructions. Completion modules may
  contain such results, but Analysis may use only their choice-free APIs.
- Radiuswise truncated existence is not a chosen family. Do not turn it into
  a global modulus or a native sequential Cauchy witness without a constructive
  proof. Use explicit quantitative data, finite constructions, compatible
  approximations, or the existing choice-free completion lifting machinery.
- Ordinary mathematical hypotheses remain valid: a supplied equivalence,
  convergence witness, intermediate-value witness, or quantitative modulus is
  not by itself a choice axiom. Do not silently manufacture such a witness or
  advertise a conditional inverse as an established global function.
- The earlier choice-dependent exact-IVT, logarithm/exponential-equivalence,
  and inverse-trigonometric adapters were intentionally removed. Do not
  restore them to make a proof or an import check pass. The exponential
  equivalence is now constructed by deterministic geometric iteration in
  `Real/Functions/Exponential/Inverse.agda`; preserve that choice-free route.
  General exact IVT and unconditional restricted trigonometric inverses
  remain future work.
- Preserve the choice-free local logarithm series, exponential laws, finite
  approximate IVT, sine-bisection density, and generic inverse laws.

After edits, check each changed Agda file with `agda-codex`, then check
`Cubical/Analysis/Everything.agda` and `Cubical/Analysis.agda`. Audit imports
and source references as well as type-checking; a choice-parametrized theorem
can type-check while violating this policy. Keep the progress documents in
sync with the actual exported results.
