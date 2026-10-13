module Cubical.Analysis.Complex.Transcendental.Exponential.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Derivative

private
  subZeroℂ : ∀ z → z -ℂ 0ℂ ≡ z
  subZeroℂ z = cong (z +ℂ_) ℂRing.0Selfinverse ∙ +ℂIdR z

  opaque
    originError : ∀ h → complexDerivativeErrorAlong (idfun ℂ) expℂ (expℂ 0ℂ) 0ℂ h ≡ (expℂ h -ℂ 1ℂ) -ℂ h
    originError h = cong₂ _-ℂ_ (cong (λ v → expℂ h -ℂ v) expℂ-zero)
      (cong₂ _·ℂ_ expℂ-zero (subZeroℂ h) ∙ ·ℂComm 1ℂ h ∙ ·ℂIdR h)

    translatedError : ∀ z w → complexDerivativeErrorAlong (idfun ℂ) expℂ (expℂ z) z w ≡
      expℂ z ·ℂ ((expℂ (w -ℂ z) -ℂ 1ℂ) -ℂ (w -ℂ z))
    translatedError z w =
      cong (λ v → (v -ℂ expℂ z) -ℂ expℂ z ·ℂ (w -ℂ z))
        (cong expℂ (sym (+ℂComm z (w -ℂ z) ∙ ℂRing.minusPlus w z)) ∙ expℂ-add z (w -ℂ z))
      ∙ cong (_-ℂ expℂ z ·ℂ (w -ℂ z))
        (cong (λ v → expℂ z ·ℂ expℂ (w -ℂ z) -ℂ v) (sym (·ℂIdR (expℂ z)))
          ∙ sym (ℂRing.·DistR- (expℂ z) (expℂ (w -ℂ z)) 1ℂ))
      ∙ sym (ℂRing.·DistR- (expℂ z) (expℂ (w -ℂ z) -ℂ 1ℂ) (w -ℂ z))

-- The derivative at zero and the exponential addition law give a uniform
-- estimate wherever the exponential values have a common norm bound.
-- This reuses the native exponential, without constructing another series.
opaque
  expℂHasUniformDerivativeAlongBounded : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate : A → ℂ) (B : ℚ₊) →
    (∀ x → normℂ (expℂ (coordinate x)) ≤ℝ rat (fst B)) →
    IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate (expℂ ∘ coordinate) (expℂ ∘ coordinate)
  expℂHasUniformDerivativeAlongBounded source coordinate B bounded continuous ε = do
    (δ , derivativeNear) ← expℂHasSelfDerivative 0ℂ (ε ₊／₊ B)
    (η , coordinateNear) ← continuous δ
    return (η , λ x y close →
      subst (λ error → normℂ error ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
        (sym (translatedError (coordinate x) (coordinate y)))
        (boundedComplexErrorProduct (expℂ (coordinate x))
          ((expℂ (coordinate y -ℂ coordinate x) -ℂ 1ℂ) -ℂ (coordinate y -ℂ coordinate x))
          (normℂ (coordinate y -ℂ coordinate x)) B ε (bounded x)
          (subst2 _≤ℝ_ (cong normℂ (originError (coordinate y -ℂ coordinate x)))
            (cong (rat (fst (ε ₊／₊ B)) ·_) (cong normℂ (subZeroℂ (coordinate y -ℂ coordinate x))))
            (derivativeNear (coordinate y -ℂ coordinate x)
              (subst (λ z → z ∼ℂ[ δ ] (coordinate y -ℂ coordinate x)) (+ℂInvR (coordinate x))
                (addℂ-presClosenessR (-ℂ coordinate x) (coordinate x) (coordinate y) δ (coordinateNear x y close)))))))
