module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Relations where

-- Implication targets, deliberately separated from proofs. None of these
-- definitions supplies an inhabitant or assumes the antecedent globally.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra using (0ℂ)
open import Cubical.Analysis.Complex.Metric using (ℂPremetricSpace)
open import Cubical.Analysis.Complex.Sequence using (ComplexSeqWitness)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion

ExactImpliesApproximateFactorization : Type₀
ExactImpliesApproximateFactorization = ExactFundamentalTheorem → ApproximateFundamentalTheorem

ExactRootFactorizationInterderivable : Type₀
ExactRootFactorizationInterderivable =
  (ExactRootExistence → ExactFundamentalTheorem) ×
  (ExactFundamentalTheorem → ExactRootExistence)

ApproximationAndStabilityToCompletion : Type₁
ApproximationAndStabilityToCompletion = ApproximateFundamentalTheorem →
  QuantitativeRootMatching → QuantitativeFactorContinuity → CompletedMultisetFundamentalTheorem

CompletionImpliesApproximateFactorization : Type₁
CompletionImpliesApproximateFactorization =
  CompletedMultisetFundamentalTheorem → ApproximateFundamentalTheorem

-- What an exact Kneser approach still has to produce. The sequence AND its
-- full native Cauchy witness lie within ONE truncation. No sequence is
-- selected from independently truncated approximate roots at each radius.
CoherentVanishingResidualConstruction : Type₀
CoherentVanishingResidualConstruction = (n : ℕ) (p : MonicPolynomial (suc n)) →
  ∥ Σ[ points ∈ (ℕ → ℂ) ] (ComplexSeqWitness points ×
    PremetricTheory.isLimitSeq ℂPremetricSpace (λ k → evaluateMonic p (points k)) 0ℂ) ∥₁

CoherentDescentImpliesExactRoots : Type₀
CoherentDescentImpliesExactRoots = CoherentVanishingResidualConstruction → ExactRootExistence
