module Cubical.HITs.CauchyReals.Complex.Modulus.Zero where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative
open import Cubical.HITs.CauchyReals.Analysis.Metric.PNorm.Base
  using (0≡ℝ₀₊+ℝ₀₊→both≡0)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


squareZero→zero : ∀ x → x ·ᵣ x ≡ 0 → x ≡ 0
squareZero→zero x x²≡0 = absᵣx=0→x=0 x $
  sym (sqrtSquareAbs x)
  ∙ cong (fst ∘ nth-rootNonNeg 2)
      (ℝ₀₊≡ {x = square₀₊ x} {y = 0 , ≤ᵣ-refl 0} x²≡0)
  ∙ sym (nth-rootNonNeg0 2 (≤ᵣ-refl 0))


normSqZero→zero : ∀ z → normSq z ≡ 0 → z ≡ 0ℂ
normSqZero→zero (a , b) norm≡0 =
  let both = 0≡ℝ₀₊+ℝ₀₊→both≡0
        (square₀₊ a) (square₀₊ b) (sym norm≡0)
  in ℂ≡
       (squareZero→zero a (sym (fst both)))
       (squareZero→zero b (sym (snd both)))


zero→normSqZero : ∀ z → z ≡ 0ℂ → normSq z ≡ 0
zero→normSqZero z z≡0 = cong normSq z≡0 ∙ normSq0


opaque
  modulusZero→zero : ∀ z → modulus z ≡ 0 → z ≡ 0ℂ
  modulusZero→zero z |z|≡0 = normSqZero→zero z $
    sym (modulusSq z)
    ∙ cong₂ _·ᵣ_ |z|≡0 |z|≡0
    ∙ ℝ!


zero→modulusZero : ∀ z → z ≡ 0ℂ → modulus z ≡ 0
zero→modulusZero z z≡0 =
  cong (fst ∘ nth-rootNonNeg 2)
    (ℝ₀₊≡ {x = normSq₀₊ z} {y = 0 , ≤ᵣ-refl 0}
      (zero→normSqZero z z≡0))
  ∙ sym (nth-rootNonNeg0 2 (≤ᵣ-refl 0))


opaque
  modulus0 : modulus 0ℂ ≡ 0
  modulus0 = zero→modulusZero 0ℂ refl
