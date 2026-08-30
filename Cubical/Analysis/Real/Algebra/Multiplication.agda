module Cubical.Analysis.Real.Algebra.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open CategoryStructures


infixl 7 _·_

_·_ : ℝ → ℝ → ℝ
_·_ = multiplyℝ

mul-rat : ∀ p q → rat p · rat q ≡ rat (p ℚ.· q)
mul-rat = multiplyℝ-rat

mul-isContinuous₁ : ∀ y → isContinuous
  (ℝPremetricSpace .snd) (λ x → x · y) (ℝPremetricSpace .snd)
mul-isContinuous₁ = multiplyℝ-isContinuous₁

mul-isContinuous₂ : ∀ x → isContinuous
  (ℝPremetricSpace .snd) (x ·_) (ℝPremetricSpace .snd)
mul-isContinuous₂ = multiplyℝ-isContinuous₂


module _
  {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  where

  mulOfContinuousIsContinuous :
    (f g : A → ℝ) →
    isContinuous source f (ℝPremetricSpace .snd) →
    isContinuous source g (ℝPremetricSpace .snd) →
    isContinuous source (λ x → f x · g x) (ℝPremetricSpace .snd)
  mulOfContinuousIsContinuous f g f-cont g-cont = snd
    (multiplyOnProductᶜ ∘C
      pairC (f , f-cont) (g , g-cont))
