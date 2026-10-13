module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Basic where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication using (mulPres≤R-0≤)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Slack using (positiveSlack)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
import Cubical.Analysis.Complex.Algebra.Identities as Identities

private
  module R = Ring.RingTheory (CommRing→Ring ℝCommRing)
  module C = Identities.Identities ℂCommRing

opaque
  exactComplexDifferenceGivesUniformDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate function derivative : A → ℂ) →
    (∀ x y → function y -ℂ function x ≡ derivative x ·ℂ (coordinate y -ℂ coordinate x)) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate function derivative
  exactComplexDifferenceGivesUniformDerivativeAlong source coordinate function derivative exact ε =
    ∣ ε , (λ x y _ → subst (λ e → normℂ e ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
      (sym (cong (_-ℂ derivative x ·ℂ (coordinate y -ℂ coordinate x)) (exact x y)
        ∙ +ℂInvR (derivative x ·ℂ (coordinate y -ℂ coordinate x))))
      (subst (_≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
        (R.0LeftAnnihilates (normℂ (coordinate y -ℂ coordinate x)) ∙ sym normℂ-zero)
        (mulPres≤R-0≤ 0ℝ (rat (fst ε)) (normℂ (coordinate y -ℂ coordinate x))
          (normℂ-nonnegative (coordinate y -ℂ coordinate x)) (<ℝ-weaken 0ℝ (rat (fst ε)) (positiveSlack ε))))) ∣₁

  affineHasUniformComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate : A → ℂ) c d →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate (λ x → c +ℂ d ·ℂ coordinate x) (λ _ → d)
  affineHasUniformComplexDerivativeAlong source coordinate c d =
    exactComplexDifferenceGivesUniformDerivativeAlong source coordinate (λ x → c +ℂ d ·ℂ coordinate x) (λ _ → d)
      (λ x y → C.sumDifference c (d ·ℂ coordinate y) c (d ·ℂ coordinate x)
        ∙ ℂRing.+IdL' (c -ℂ c) (d ·ℂ coordinate y -ℂ d ·ℂ coordinate x) (+ℂInvR c)
        ∙ sym (ℂRing.·DistR- d (coordinate y) (coordinate x)))
