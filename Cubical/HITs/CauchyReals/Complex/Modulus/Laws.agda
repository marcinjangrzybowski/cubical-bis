module Cubical.HITs.CauchyReals.Complex.Modulus.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative
open import Cubical.HITs.CauchyReals.Analysis.Metric.PNorm.Base
  using (nth-rootNonNegDist·)
open NonNegativeReals using (_·₀₊_)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
  modulus1 : modulus 1ℂ ≡ 1
  modulus1 =
    modulusOfNormSqSquare 1ℂ 1 (normSq1 ∙ ℝ!)
    ∙ absᵣPos 1 decℚ<ᵣ?


opaque
  modulusi : modulus iℂ ≡ 1
  modulusi =
    modulusOfNormSqSquare iℂ 1 (normSqi ∙ ℝ!)
    ∙ absᵣPos 1 decℚ<ᵣ?


opaque
  modulus-neg : ∀ z → modulus (-ℂ z) ≡ modulus z
  modulus-neg z = cong (fst ∘ nth-rootNonNeg 2) (ℝ₀₊≡ (normSq-neg z))


opaque
  modulus-conj : ∀ z → modulus (conj z) ≡ modulus z
  modulus-conj z = cong (fst ∘ nth-rootNonNeg 2) (ℝ₀₊≡ (normSq-conj z))


opaque
  modulus-mul : ∀ z w → modulus (z ·ℂ w) ≡ modulus z ·ᵣ modulus w
  modulus-mul z w =
    cong (fst ∘ nth-rootNonNeg 2)
      (ℝ₀₊≡ {x = normSq₀₊ (z ·ℂ w)}
             {y = normSq₀₊ z ·₀₊ normSq₀₊ w}
             (normSq-mul z w))
    ∙ sym (nth-rootNonNegDist· 2 (normSq₀₊ z) (normSq₀₊ w))


opaque
  modulus-fromℝ : ∀ x → modulus (fromℝ x) ≡ absᵣ x
  modulus-fromℝ x = modulusOfNormSqSquare (fromℝ x) x (normSq-fromℝ x)


opaque
  modulus-imag : ∀ x → modulus (imagℂ x) ≡ absᵣ x
  modulus-imag x = modulusOfNormSqSquare (imagℂ x) x (normSq-imag x)
