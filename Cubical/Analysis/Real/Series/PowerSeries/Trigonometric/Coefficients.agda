module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; fromNat)
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients


private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- The two rational sign masks form the four-cycle
--   sin : 0, 1, 0, -1, ...
--   cos : 1, 0, -1, 0, ...
-- Multiplying these masks by 1/n! gives exact rational coefficients.

mutual
  sineRationalSign : ℕ → ℚ
  sineRationalSign zero = 0
  sineRationalSign (suc n) = cosineRationalSign n

  cosineRationalSign : ℕ → ℚ
  cosineRationalSign zero = 1
  cosineRationalSign (suc n) = ℚ.- sineRationalSign n


sineRationalSign-zero : sineRationalSign zero ≡ 0
sineRationalSign-zero = refl


cosineRationalSign-zero : cosineRationalSign zero ≡ 1
cosineRationalSign-zero = refl


sineRationalSign-suc : ∀ n →
  sineRationalSign (suc n) ≡ cosineRationalSign n
sineRationalSign-suc n = refl


cosineRationalSign-suc : ∀ n →
  cosineRationalSign (suc n) ≡ ℚ.- sineRationalSign n
cosineRationalSign-suc n = refl


sineRationalCoefficient : ℕ → ℚ
sineRationalCoefficient n =
  sineRationalSign n ℚ.· exponentialRationalCoefficient n


cosineRationalCoefficient : ℕ → ℚ
cosineRationalCoefficient n =
  cosineRationalSign n ℚ.· exponentialRationalCoefficient n


sineRationalCoefficient-zero :
  sineRationalCoefficient zero ≡ 0
sineRationalCoefficient-zero =
  ℚRing.0LeftAnnihilates (exponentialRationalCoefficient zero)


cosineRationalCoefficient-zero :
  cosineRationalCoefficient zero ≡ 1
cosineRationalCoefficient-zero =
  ℚ.·IdL (exponentialRationalCoefficient zero)
  ∙ exponentialRationalCoefficient-zero


sineRationalCoefficient-suc : ∀ n →
  fromNat (suc n) ℚ.· sineRationalCoefficient (suc n)
    ≡ cosineRationalCoefficient n
sineRationalCoefficient-suc n =
  ℚ.·Assoc
    (fromNat (suc n))
    (cosineRationalSign n)
    (exponentialRationalCoefficient (suc n))
  ∙ cong
      (λ x → x ℚ.· exponentialRationalCoefficient (suc n))
      (ℚ.·Comm (fromNat (suc n)) (cosineRationalSign n))
  ∙ sym
      (ℚ.·Assoc
        (cosineRationalSign n)
        (fromNat (suc n))
        (exponentialRationalCoefficient (suc n)))
  ∙ cong
      (λ x → cosineRationalSign n ℚ.· x)
      (exponentialRationalCoefficient-suc n)


cosineRationalCoefficient-suc : ∀ n →
  fromNat (suc n) ℚ.· cosineRationalCoefficient (suc n)
    ≡ ℚ.- sineRationalCoefficient n
cosineRationalCoefficient-suc n =
  ℚ.·Assoc
    (fromNat (suc n))
    (ℚ.- sineRationalSign n)
    (exponentialRationalCoefficient (suc n))
  ∙ cong
      (λ x → x ℚ.· exponentialRationalCoefficient (suc n))
      (ℚ.·Comm (fromNat (suc n)) (ℚ.- sineRationalSign n))
  ∙ sym
      (ℚ.·Assoc
        (ℚ.- sineRationalSign n)
        (fromNat (suc n))
        (exponentialRationalCoefficient (suc n)))
  ∙ cong
      (λ x → (ℚ.- sineRationalSign n) ℚ.· x)
      (exponentialRationalCoefficient-suc n)
  ∙ ℚRing.-DistL·
      (sineRationalSign n)
      (exponentialRationalCoefficient n)


sineCoefficients : RealSequence
sineCoefficients n = rat (sineRationalCoefficient n)


cosineCoefficients : RealSequence
cosineCoefficients n = rat (cosineRationalCoefficient n)


sineCoefficients-value : ∀ n →
  sineCoefficients n ≡ rat (sineRationalCoefficient n)
sineCoefficients-value n = refl


cosineCoefficients-value : ∀ n →
  cosineCoefficients n ≡ rat (cosineRationalCoefficient n)
cosineCoefficients-value n = refl


sineCoefficients-zero : sineCoefficients zero ≡ 0ℝ
sineCoefficients-zero = cong rat sineRationalCoefficient-zero


cosineCoefficients-zero : cosineCoefficients zero ≡ 1ℝ
cosineCoefficients-zero = cong rat cosineRationalCoefficient-zero


sineCoefficients-suc : ∀ n →
  realNatural (suc n) · sineCoefficients (suc n)
    ≡ cosineCoefficients n
sineCoefficients-suc n =
  mul-rat (fromNat (suc n)) (sineRationalCoefficient (suc n))
  ∙ cong rat (sineRationalCoefficient-suc n)


cosineCoefficients-suc : ∀ n →
  realNatural (suc n) · cosineCoefficients (suc n)
    ≡ - sineCoefficients n
cosineCoefficients-suc n =
  mul-rat (fromNat (suc n)) (cosineRationalCoefficient (suc n))
  ∙ cong rat (cosineRationalCoefficient-suc n)
  ∙ sym (neg-rat (sineRationalCoefficient n))


formalDerivative-sineCoefficients-pointwise : ∀ n →
  formalDerivative sineCoefficients n ≡ cosineCoefficients n
formalDerivative-sineCoefficients-pointwise = sineCoefficients-suc


formalDerivative-sineCoefficients :
  formalDerivative sineCoefficients ≡ cosineCoefficients
formalDerivative-sineCoefficients =
  funExt formalDerivative-sineCoefficients-pointwise


formalDerivative-cosineCoefficients-pointwise : ∀ n →
  formalDerivative cosineCoefficients n ≡ - sineCoefficients n
formalDerivative-cosineCoefficients-pointwise = cosineCoefficients-suc


formalDerivative-cosineCoefficients :
  formalDerivative cosineCoefficients ≡ (λ n → - sineCoefficients n)
formalDerivative-cosineCoefficients =
  funExt formalDerivative-cosineCoefficients-pointwise
