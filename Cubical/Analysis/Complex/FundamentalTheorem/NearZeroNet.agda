module Cubical.Analysis.Complex.FundamentalTheorem.NearZeroNet where

-- One finite Gaussian net covers every point with sufficiently small
-- residual. The centers themselves have small residual. No compatible
-- sequence of nets or exact roots is selected.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin; zero)
open import Cubical.Data.Vec using (Vec; _∷_; lookup; map)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.LocalRoots
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Evaluation
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Perturbation
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.RootBounds
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.ApproximateEquivalence
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Gaussian
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.RootContainment

opaque
  nearZeroNet : NearZeroNetTheorem
  nearZeroNet n p ε = PT.rec PT.isPropPropTrunc withBound (coefficientBound-exists p)
    where
    Output : Type₀
    Output = Σ[ δ ∈ ℚ₊ ] Σ[ k ∈ ℕ ] Σ[ centers ∈ Vec GaussianRational (suc k) ]
      ((∀ i → evaluateMonic p (gaussianℂ (lookup i centers)) ∼ℂ[ ε ] 0ℂ) ×
        (∀ z → evaluateMonic p z ∼ℂ[ δ ] 0ℂ →
          PT.∥ Σ[ i ∈ Fin (suc k) ] z ∼ℂ[ ε ] gaussianℂ (lookup i centers) ∥₁))

    withBound : (Σ[ A ∈ ℚ₊ ] CoefficientsBounded p A) → PT.∥ Output ∥₁
    withBound (A , bounded) = PT.map assemble (gaussian-factor-density (suc n) p δ)
      where
      μ : ℚ₊ → ℚ₊
      μ = factorMatchingRadius (suc n) A

      B E η δ : ℚ₊
      B = coefficientRootBound (suc n) (A +₊ (1 +₊ 1))
      E = monicEvaluationLipschitz (suc n) A B
      η = scaleTolerance E ε
      δ = min₊ (μ ε) (min₊ 1 η)

      assemble : (Σ[ centers ∈ Vec GaussianRational (suc n) ]
        CoefficientCloseness p δ (gaussianFactors centers)) → Output
      assemble (centers , accurate) = (μ ε /2₊) , n , centers , centers-small , covers
        where
        roots : Vec ℂ (suc n)
        roots = map gaussianℂ centers

        near-p : CoefficientCloseness p (μ ε) (linearFactors roots)
        near-p = coefficientCloseness-monotone p (linearFactors roots) δ (μ ε)
          (min₊≤L (μ ε) (min₊ 1 η)) accurate

        near-one : CoefficientCloseness p 1 (linearFactors roots)
        near-one = coefficientCloseness-monotone p (linearFactors roots) (min₊ 1 η) 1 (min₊≤L 1 η)
          (coefficientCloseness-monotone p (linearFactors roots) δ (min₊ 1 η)
            (min₊≤R (μ ε) (min₊ 1 η)) accurate)

        near-evaluation : CoefficientCloseness (linearFactors roots) η p
        near-evaluation = coefficientCloseness-sym p (linearFactors roots) η
          (coefficientCloseness-monotone p (linearFactors roots) (min₊ 1 η) η (min₊≤R 1 η)
            (coefficientCloseness-monotone p (linearFactors roots) δ (min₊ 1 η)
              (min₊≤R (μ ε) (min₊ 1 η)) accurate))

        centers-small : ∀ i → evaluateMonic p (gaussianℂ (lookup i centers)) ∼ℂ[ ε ] 0ℂ
        centers-small i = subst (λ z → evaluateMonic p z ∼ℂ[ ε ] 0ℂ) (lookup-gaussian centers i)
          (modulusℂ-small→closeZero (evaluateMonic p (lookup i roots)) ε
            (monicEvaluation-nearZero (linearFactors roots) p (lookup i roots) A B ε bounded
              (factorRootsBounded roots (A +₊ (1 +₊ 1))
                (nearbyCoefficient-bound p (linearFactors roots) A bounded near-one) i)
              (linearFactors-root roots i) near-evaluation))

        covers : ∀ z → evaluateMonic p z ∼ℂ[ μ ε /2₊ ] 0ℂ →
          PT.∥ Σ[ i ∈ Fin (suc n) ] z ∼ℂ[ ε ] gaussianℂ (lookup i centers) ∥₁
        covers z small = PT.rec PT.isPropPropTrunc
          (λ { (others , close) → PT.map (λ { (σ , matched) → equivFun σ zero ,
            subst (z ∼ℂ[ ε ]_) (lookup-gaussian centers (equivFun σ zero)) (matched zero) })
            (factorMatchingAt-bound p A bounded ε (z ∷ others) roots close near-p) })
          (approximateFactors-at-small-residual p z (μ ε) small)
