module Cubical.HITs.CauchyReals.Complex.Modulus.Definition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.NormSquared


normSq₀₊ : ℂ → ℝ₀₊
normSq₀₊ z = normSq z , normSqNonNeg z


modulus₀₊ : ℂ → ℝ₀₊
modulus₀₊ z = nth-rootNonNeg 2 (normSq₀₊ z)


modulus : ℂ → ℝ
modulus = fst ∘ modulus₀₊


modulusNonNeg : ∀ z → 0 ≤ᵣ modulus z
modulusNonNeg z = snd (modulus₀₊ z)


modulusSq : ∀ z → modulus z ·ᵣ modulus z ≡ normSq z
modulusSq z =
  sym (x^²=x·x (modulus z))
  ∙ cong fst (Iso.sec (nth-pow-root-iso₀₊ 2) (normSq₀₊ z))


square₀₊ : ℝ → ℝ₀₊
square₀₊ x = x ·ᵣ x , squareNonNeg x


sqrtSquareAbs : ∀ x → fst (nth-rootNonNeg 2 (square₀₊ x)) ≡ absᵣ x
sqrtSquareAbs x =
  cong (fst ∘ nth-rootNonNeg 2)
    (ℝ₀₊≡
      (x·x≡∣x∣·∣x∣ x ∙ sym (x^²=x·x (absᵣ x))))
  ∙ cong fst
      (Iso.ret (nth-pow-root-iso₀₊ 2) (absᵣ x , 0≤absᵣ x))


modulusOfNormSqSquare : ∀ z x → normSq z ≡ x ·ᵣ x → modulus z ≡ absᵣ x
modulusOfNormSqSquare z x norm≡x² =
  cong (fst ∘ nth-rootNonNeg 2)
    (ℝ₀₊≡ {x = normSq₀₊ z} {y = square₀₊ x} norm≡x²)
  ∙ sqrtSquareAbs x
