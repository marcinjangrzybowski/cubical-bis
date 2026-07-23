module Cubical.HITs.CauchyReals.Complex.Modulus.Triangle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Power.Order
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative
open import Cubical.HITs.CauchyReals.Analysis.Metric.PNorm.Base
  using (nth-rootNonNegMonotone; 𝒑-norm×-lem)
open NonNegativeReals using (_+₀₊_; _^₀₊_)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws


absComplex : ℂ → ℂ
absComplex z = absᵣ (re z) , absᵣ (im z)


opaque
  normSq-absComplex : ∀ z → normSq z ≡ normSq (absComplex z)
  normSq-absComplex z = cong₂ _+ᵣ_
    (x·x≡∣x∣·∣x∣ (re z))
    (x·x≡∣x∣·∣x∣ (im z))


opaque
  modulus-absComplex : ∀ z → modulus (absComplex z) ≡ modulus z
  modulus-absComplex z =
    cong (fst ∘ nth-rootNonNeg 2) (ℝ₀₊≡ (sym (normSq-absComplex z)))


opaque
  squareMonotoneNonNeg : ∀ x y → 0 ≤ᵣ x → x ≤ᵣ y → x ·ᵣ x ≤ᵣ y ·ᵣ y
  squareMonotoneNonNeg x y 0≤x x≤y =
    isTrans≡≤ᵣ _ _ _
      (sym (x^²=x·x x))
      (isTrans≤≡ᵣ _ _ _
        (^ⁿ-Monotone 2 0≤x x≤y)
        (x^²=x·x y))


opaque
  modulusMonotoneNormSq : ∀ z w → normSq z ≤ᵣ normSq w → modulus z ≤ᵣ modulus w
  modulusMonotoneNormSq z w =
    nth-rootNonNegMonotone 2 (normSq₀₊ z) (normSq₀₊ w)


opaque
  modulusMonotoneAbsCoords : ∀ z w
    → absᵣ (re z) ≤ᵣ absᵣ (re w)
    → absᵣ (im z) ≤ᵣ absᵣ (im w)
    → modulus z ≤ᵣ modulus w
  modulusMonotoneAbsCoords z w re≤ im≤ = modulusMonotoneNormSq z w $
    isTrans≡≤ᵣ _ _ _ (normSq-absComplex z) $
    isTrans≤≡ᵣ _ _ _
      (≤ᵣMonotone+ᵣ _ _ _ _
        (squareMonotoneNonNeg _ _ (0≤absᵣ _) re≤)
        (squareMonotoneNonNeg _ _ (0≤absᵣ _) im≤))
      (sym (normSq-absComplex w))


powerNorm : (x y : ℝ₀₊) → ℝ₀₊
powerNorm x y = (x ^₀₊ 2) +₀₊ (y ^₀₊ 2)

opaque
  modulus-power-square : ∀ (a b : ℝ) (0≤a : 0 ≤ᵣ a) (0≤b : 0 ≤ᵣ b) →
    (modulus (a , b) ^ⁿ 2) ≡ fst (powerNorm (a , 0≤a) (b , 0≤b))
  modulus-power-square a b 0≤a 0≤b =
    x^²=x·x (modulus (a , b))
    ∙ modulusSq (a , b)
    ∙ cong₂ _+ᵣ_ (sym (x^²=x·x a)) (sym (x^²=x·x b))

opaque
  modulus-to-power-root : ∀ (a b : ℝ) (0≤a : 0 ≤ᵣ a) (0≤b : 0 ≤ᵣ b) →
    modulus (a , b) ≡
      fst (nth-rootNonNeg 2 (powerNorm (a , 0≤a) (b , 0≤b)))
  modulus-to-power-root a b 0≤a 0≤b =
    cong (fst ∘ nth-rootNonNeg 2) $ ℝ₀₊≡ $
      cong₂ _+ᵣ_ (sym (x^²=x·x a)) (sym (x^²=x·x b))
