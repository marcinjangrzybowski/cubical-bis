module Cubical.HITs.CauchyReals.Complex.Inverse.Cancellation where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse using
  (invℝ; x·invℝ[x])

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition


opaque
  ·invℂ : ∀ z (0#z : 0ℂ #ℂ z) → z ·ℂ invℂ z 0#z ≡ 1ℂ
  ·invℂ z 0#z =
    let r = invℝ (normSq z) (normSqApart z 0#z)
    in ·ℂAssoc z (fromℝ r) (conj z)
      ∙ cong (_·ℂ conj z) (·ℂComm z (fromℝ r))
      ∙ sym (·ℂAssoc (fromℝ r) z (conj z))
      ∙ cong (fromℝ r ·ℂ_) (mul-conj z)
      ∙ sym (fromℝ-pres· r (normSq z))
      ∙ cong fromℝ
          (·ᵣComm r (normSq z)
          ∙ x·invℝ[x] (normSq z) (normSqApart z 0#z))


opaque
  invℂ· : ∀ z (0#z : 0ℂ #ℂ z) → invℂ z 0#z ·ℂ z ≡ 1ℂ
  invℂ· z 0#z = ·ℂComm _ z ∙ ·invℂ z 0#z


opaque
  [x·y]/yℂ : ∀ x y (0#y : 0ℂ #ℂ y) →
    (x ·ℂ y) ／ℂ[ y , 0#y ] ≡ x
  [x·y]/yℂ x y 0#y =
    sym (·ℂAssoc x y (invℂ y 0#y))
    ∙ cong (x ·ℂ_) (·invℂ y 0#y)
    ∙ ·ℂIdR x


opaque
  [x/y]·yℂ : ∀ x y (0#y : 0ℂ #ℂ y) →
    (x ／ℂ[ y , 0#y ]) ·ℂ y ≡ x
  [x/y]·yℂ x y 0#y =
    sym (·ℂAssoc x (invℂ y 0#y) y)
    ∙ cong (x ·ℂ_) (invℂ· y 0#y)
    ∙ ·ℂIdR x
