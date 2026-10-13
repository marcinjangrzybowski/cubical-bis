module Cubical.Analysis.Complex.FundamentalTheorem.Matching.ApproximateEquivalence where

-- A direct reverse reduction from coefficient approximation to small
-- residuals. Only finitely many bounds and one approximate factorization
-- are used for each requested tolerance; no family of roots is selected.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.FinData using (zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Analysis.Real.Base using (rat)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Modulus.Metric
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.Polynomial.Newton.Remainder using (normℂ-ballBound)
open import Cubical.Analysis.Complex.FundamentalTheorem.Statement
open import Cubical.Analysis.Complex.FundamentalTheorem.Reduction
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic using (ApproximateFormulationsInterderivable)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Evaluation
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Perturbation
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.RootBounds

private
  normBound-exists : ∀ z → PT.∥ Σ[ A ∈ ℚ₊ ] (normℂ z ≤ℝ ⟦ A ⟧₊) ∥₁
  normBound-exists z = PT.map
    (λ (k , bounded) → naturalBound k , <ℝ-weaken (normℂ z) (rat (naturalRational k)) bounded)
    (∃naturalUpperBound (normℂ z))

coefficientBound-exists : ∀ {n} (p : MonicPolynomial n) → PT.∥ Σ[ A ∈ ℚ₊ ] CoefficientsBounded p A ∥₁
coefficientBound-exists [] = PT.∣ 1 , (λ ()) ∣₁
coefficientBound-exists (a ∷ p) = PT.map2 combine (normBound-exists a) (coefficientBound-exists p)
  where
  combine : (Σ[ A ∈ ℚ₊ ] (normℂ a ≤ℝ ⟦ A ⟧₊)) → (Σ[ B ∈ ℚ₊ ] CoefficientsBounded p B) →
    Σ[ C ∈ ℚ₊ ] CoefficientsBounded (a ∷ p) C
  combine (A , ab) (B , pb) = A +₊ B , λ
    { zero → ≤ℝ-trans (normℂ a) ⟦ A ⟧₊ ⟦ A +₊ B ⟧₊ ab (radius-sumL A B)
    ; (suc i) → ≤ℝ-trans (normℂ (lookup i p)) ⟦ B ⟧₊ ⟦ A +₊ B ⟧₊ (pb i) (radius-sumR A B) }

nearbyCoefficient-bound : ∀ {n} (p q : MonicPolynomial n) A →
  CoefficientsBounded p A → CoefficientCloseness p 1 q → CoefficientsBounded q (A +₊ (1 +₊ 1))
nearbyCoefficient-bound p q A bounded close i =
  subst (normℂ (lookup i q) ≤ℝ_)
    (cong (⟦ A ⟧₊ +_) (rat+rat 1 1) ∙ rat+rat (fst A) (fst (1 +₊ 1)))
    (normℂ-ballBound (lookup i p) ⟦ A ⟧₊ (⟦ 1 ⟧₊ + ⟦ 1 ⟧₊) (lookup i q) (bounded i)
      (closeness→differenceBound (lookup i q) (lookup i p) 1 (sym∼ℂ (lookup i p) (lookup i q) 1 (close i))))

opaque
  approximateFactorization→roots : ApproximateFundamentalTheorem → ApproximateRootExistence
  approximateFactorization→roots approximate n p ε = PT.rec PT.isPropPropTrunc withBound (coefficientBound-exists p)
    where
    withBound : (Σ[ A ∈ ℚ₊ ] CoefficientsBounded p A) →
      PT.∥ Σ[ z ∈ ℂ ] (evaluateMonic p z ∼ℂ[ ε ] 0ℂ) ∥₁
    withBound (A , bounded) = PT.map fromFactors (approximate (suc n) p δ)
      where
      B E δ : ℚ₊
      B = coefficientRootBound (suc n) (A +₊ (1 +₊ 1))
      E = monicEvaluationLipschitz (suc n) A B
      δ = min₊ 1 (scaleTolerance E ε)

      fromFactors : (Σ[ roots ∈ Vec ℂ (suc n) ] CoefficientCloseness p δ (linearFactors roots)) →
        Σ[ z ∈ ℂ ] (evaluateMonic p z ∼ℂ[ ε ] 0ℂ)
      fromFactors (r ∷ roots , close) = r , modulusℂ-small→closeZero (evaluateMonic p r) ε
        (monicEvaluation-nearZero q p r A B ε bounded
          (factorRootsBounded (r ∷ roots) (A +₊ (1 +₊ 1))
            (nearbyCoefficient-bound p q A bounded
              (coefficientCloseness-monotone p q δ 1 (min₊≤L 1 (scaleTolerance E ε)) close)) zero)
          (linearFactors-root (r ∷ roots) zero)
          (λ i → sym∼ℂ (lookup i p) (lookup i q) (scaleTolerance E ε)
            (coefficientCloseness-monotone p q δ (scaleTolerance E ε)
              (min₊≤R 1 (scaleTolerance E ε)) close i)))
        where
        q : MonicPolynomial (suc n)
        q = linearFactors (r ∷ roots)

approximateFormulationsInterderivable : ApproximateFormulationsInterderivable
approximateFormulationsInterderivable = approximateRoots→factorization , approximateFactorization→roots
