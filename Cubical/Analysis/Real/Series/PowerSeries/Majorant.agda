module Cubical.Analysis.Real.Series.PowerSeries.Majorant where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative


CoefficientMajorizedBy :
  RealSequence → RealSequence → Type₀
CoefficientMajorizedBy coefficients majorant =
  ∀ n → absℝ (coefficients n) ≤ℝ majorant n


NonnegativeCoefficients : RealSequence → Type₀
NonnegativeCoefficients coefficients =
  ∀ n → 0ℝ ≤ℝ coefficients n


-- A coefficient majorant is automatically nonnegative, so later comparison
-- theorems do not need a second pointwise positivity hypothesis.

coefficientMajorantIsNonnegative :
  ∀ coefficients majorant →
  CoefficientMajorizedBy coefficients majorant →
  NonnegativeCoefficients majorant
coefficientMajorantIsNonnegative
  coefficients majorant majorized n =
  ≤ℝ-trans
    0ℝ (absℝ (coefficients n)) (majorant n)
    (absNonnegative (coefficients n))
    (majorized n)


nonnegativeCoefficientsSelfMajorized :
  ∀ coefficients →
  NonnegativeCoefficients coefficients →
  CoefficientMajorizedBy coefficients coefficients
nonnegativeCoefficientsSelfMajorized
  coefficients nonnegative n =
  subst
    (_≤ℝ coefficients n)
    (sym
      (absOfNonnegative
        (coefficients n) (nonnegative n)))
    (≤ℝ-refl (coefficients n))


powerSeriesTermAbsBoundByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy coefficients majorant →
  absℝ x ≤ℝ radius →
  ∀ n →
  absℝ (powerSeriesTerms coefficients x n) ≤ℝ
  powerSeriesTerms majorant radius n
powerSeriesTermAbsBoundByCoefficientMajorant
  coefficients majorant x radius
  coefficients-majorized absx≤radius n =
  subst
    (_≤ℝ powerSeriesTerms majorant radius n)
    (sym absolute-term-path)
    product-bound
  where
  absolute-term-path :
    absℝ (powerSeriesTerms coefficients x n) ≡
    absℝ (coefficients n) · powℝ (absℝ x) n
  absolute-term-path =
    absMul (coefficients n) (powℝ x n)
    ∙ cong
        (absℝ (coefficients n) ·_)
        (absPow x n)

  radius-power-bound :
    powℝ (absℝ x) n ≤ℝ powℝ radius n
  radius-power-bound =
    powMono n (absNonnegative x) absx≤radius

  product-bound :
    absℝ (coefficients n) · powℝ (absℝ x) n ≤ℝ
    powerSeriesTerms majorant radius n
  product-bound =
    mulPres≤
      (absℝ (coefficients n)) (majorant n)
      (powℝ (absℝ x) n) (powℝ radius n)
      (coefficientMajorantIsNonnegative
        coefficients majorant coefficients-majorized n)
      (powNonnegative
        (absℝ x) n (absNonnegative x))
      (coefficients-majorized n)
      radius-power-bound


formalDerivativeMajorant : RealSequence → RealSequence
formalDerivativeMajorant majorant n =
  realNatural (suc n) · majorant (suc n)


formalDerivativeMajorant-nonnegative :
  ∀ majorant →
  NonnegativeCoefficients majorant →
  NonnegativeCoefficients
    (formalDerivativeMajorant majorant)
formalDerivativeMajorant-nonnegative
  majorant nonnegative n =
  isNonnegative→0≤
    (formalDerivativeMajorant majorant n)
    (mulPresIsNonnegative
      (realNatural (suc n))
      (majorant (suc n))
      (0≤→isNonnegative
        (realNatural (suc n))
        (realNatural-nonnegative (suc n)))
      (0≤→isNonnegative
        (majorant (suc n))
        (nonnegative (suc n))))


formalDerivativePresCoefficientMajorant :
  ∀ coefficients majorant →
  CoefficientMajorizedBy coefficients majorant →
  CoefficientMajorizedBy
    (formalDerivative coefficients)
    (formalDerivativeMajorant majorant)
formalDerivativePresCoefficientMajorant
  coefficients majorant majorized n =
  subst
    (_≤ℝ formalDerivativeMajorant majorant n)
    (sym absolute-path)
    product-bound
  where
  absolute-path :
    absℝ (formalDerivative coefficients n) ≡
    realNatural (suc n) ·
      absℝ (coefficients (suc n))
  absolute-path =
    absMul
      (realNatural (suc n))
      (coefficients (suc n))
    ∙ cong
        (_· absℝ (coefficients (suc n)))
        (absOfNonnegative
          (realNatural (suc n))
          (realNatural-nonnegative (suc n)))

  product-bound :
    realNatural (suc n) ·
        absℝ (coefficients (suc n))
      ≤ℝ
    formalDerivativeMajorant majorant n
  product-bound =
    mulPres≤
      (realNatural (suc n))
      (realNatural (suc n))
      (absℝ (coefficients (suc n)))
      (majorant (suc n))
      (realNatural-nonnegative (suc n))
      (absNonnegative (coefficients (suc n)))
      (≤ℝ-refl (realNatural (suc n)))
      (majorized (suc n))
