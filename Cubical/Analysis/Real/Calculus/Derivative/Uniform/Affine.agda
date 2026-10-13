module Cubical.Analysis.Real.Calculus.Derivative.Uniform.Affine where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication using (mulPres≤R-0≤)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Slack using (positiveSlack)
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform

private module R = Ring.RingTheory (CommRing→Ring ℝCommRing)

opaque
  exactDifferenceGivesUniformDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate function derivative : A → ℝ) →
    (∀ x y → function y - function x ≡ derivative x · (coordinate y - coordinate x)) →
    IsRadiuswiseUniformDerivativeAlong source coordinate function derivative
  exactDifferenceGivesUniformDerivativeAlong source coordinate function derivative exact ε =
    ∣ ε , (λ x y _ → subst (λ e → absℝ e ≤ℝ rat (fst ε) · absℝ (coordinate y - coordinate x))
      (sym (cong (_- derivative x · (coordinate y - coordinate x)) (exact x y)
        ∙ subSelf (derivative x · (coordinate y - coordinate x))))
      (subst (_≤ℝ rat (fst ε) · absℝ (coordinate y - coordinate x))
        (R.0LeftAnnihilates (absℝ (coordinate y - coordinate x)) ∙ sym absZero)
        (mulPres≤R-0≤ 0ℝ (rat (fst ε)) (absℝ (coordinate y - coordinate x))
          (absNonnegative (coordinate y - coordinate x)) (<ℝ-weaken 0ℝ (rat (fst ε)) (positiveSlack ε))))) ∣₁

  affineHasUniformDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate : A → ℝ) c d →
    IsRadiuswiseUniformDerivativeAlong source coordinate (λ x → c + d · coordinate x) (λ _ → d)
  affineHasUniformDerivativeAlong source coordinate c d =
    exactDifferenceGivesUniformDerivativeAlong source coordinate (λ x → c + d · coordinate x) (λ _ → d)
      (λ x y → differenceOfSums c (d · coordinate y) c (d · coordinate x)
        ∙ cong (_+ (d · coordinate y - d · coordinate x)) (subSelf c)
        ∙ addIdL (d · coordinate y - d · coordinate x) ∙ sym (R.·DistR- d (coordinate y) (coordinate x)))
