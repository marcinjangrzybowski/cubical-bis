module Cubical.Analysis.Complex.Calculus.Derivative.Basic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Factor


constantHasComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate : A → ℂ) c →
  IsComplexDerivativeAlong source coordinate (λ _ → c) (λ _ → 0ℂ)
constantHasComplexDerivativeAlong source coordinate c x =
  continuousComplexDifferenceFactorGivesDerivativeAt source coordinate (λ _ → c) 0ℂ x (λ _ → 0ℂ)
    (λ y → +ℂInvR c ∙ sym (ℂRing.0RightAnnihilates (coordinate y -ℂ coordinate x)))
    refl (constantℂ-isContinuous source 0ℂ x)

coordinateHasComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate : A → ℂ) →
  IsComplexDerivativeAlong source coordinate coordinate (λ _ → 1ℂ)
coordinateHasComplexDerivativeAlong source coordinate x =
  continuousComplexDifferenceFactorGivesDerivativeAt source coordinate coordinate 1ℂ x (λ _ → 1ℂ)
    (λ y → sym (·ℂIdR (coordinate y -ℂ coordinate x)))
    refl (constantℂ-isContinuous source 1ℂ x)

constantHasComplexDerivative : ∀ c → IsComplexDerivative (λ _ → c) (λ _ → 0ℂ)
constantHasComplexDerivative = constantHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ)

identityHasComplexDerivative : IsComplexDerivative (idfun ℂ) (λ _ → 1ℂ)
identityHasComplexDerivative = coordinateHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ)

linearHasComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (coordinate : A → ℂ) c →
  IsComplexDerivativeAlong source coordinate (λ x → c ·ℂ coordinate x) (λ _ → c)
linearHasComplexDerivativeAlong source coordinate c x = continuousComplexDifferenceFactorGivesDerivativeAt
  source coordinate (λ y → c ·ℂ coordinate y) c x (λ _ → c)
  (λ y → sym (ℂRing.·DistR- c (coordinate y) (coordinate x)) ∙ ·ℂComm c (coordinate y -ℂ coordinate x))
  refl (constantℂ-isContinuous source c x)

linearHasComplexDerivative : ∀ c → IsComplexDerivative (c ·ℂ_) (λ _ → c)
linearHasComplexDerivative = linearHasComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ)
