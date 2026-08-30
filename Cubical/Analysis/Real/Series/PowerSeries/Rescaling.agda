module Cubical.Analysis.Real.Series.PowerSeries.Rescaling where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.PowerSeries.Base


-- Coefficientwise representation of the substitution x ↦ c·x.
rescaleCoefficients : ℝ → RealSequence → RealSequence
rescaleCoefficients c coefficients n =
  coefficients n · powℝ c n


private
  onePow : ∀ n → powℝ 1ℝ n ≡ 1ℝ
  onePow zero = refl
  onePow (suc n) =
    cong (1ℝ ·_) (onePow n)
    ∙ mulIdL 1ℝ

  reorderFourFactors : ∀ x y u v →
    (x · y) · (u · v) ≡ (x · u) · (y · v)
  reorderFourFactors x y u v =
    mulAssoc (x · y) u v
    ∙ cong (_· v)
        ( sym (mulAssoc x y u)
        ∙ cong (x ·_) (mulComm y u)
        ∙ mulAssoc x u y
        )
    ∙ sym (mulAssoc (x · u) y v)

  powMul : ∀ x y n →
    powℝ (x · y) n ≡ powℝ x n · powℝ y n
  powMul x y zero = sym (mulIdL 1ℝ)
  powMul x y (suc n) =
    cong ((x · y) ·_) (powMul x y n)
    ∙ reorderFourFactors x y (powℝ x n) (powℝ y n)


rescaleCoefficients-one : ∀ coefficients →
  rescaleCoefficients 1ℝ coefficients ≡ coefficients
rescaleCoefficients-one coefficients =
  funExt
    (λ n →
      cong (coefficients n ·_) (onePow n)
      ∙ mulIdR (coefficients n))


rescaleCoefficients-compose : ∀ c d coefficients →
  rescaleCoefficients c (rescaleCoefficients d coefficients)
    ≡
  rescaleCoefficients (d · c) coefficients
rescaleCoefficients-compose c d coefficients =
  funExt
    (λ n →
      sym
        (mulAssoc
          (coefficients n) (powℝ d n) (powℝ c n))
      ∙ cong
          (coefficients n ·_)
          (sym (powMul d c n)))


powerSeriesTerms-rescale : ∀ c coefficients x n →
  powerSeriesTerms (rescaleCoefficients c coefficients) x n
    ≡
  powerSeriesTerms coefficients (c · x) n
powerSeriesTerms-rescale c coefficients x n =
  sym
    (mulAssoc
      (coefficients n) (powℝ c n) (powℝ x n))
  ∙ cong
      (coefficients n ·_)
      (sym (powMul c x n))


powerSeriesTerms-rescale-sequence : ∀ c coefficients x →
  powerSeriesTerms (rescaleCoefficients c coefficients) x
    ≡
  powerSeriesTerms coefficients (c · x)
powerSeriesTerms-rescale-sequence c coefficients x =
  funExt (powerSeriesTerms-rescale c coefficients x)


rescalePowerSeriesIsCauchy : ∀ c coefficients x →
  IsCauchySeries (powerSeriesTerms coefficients (c · x)) →
  IsCauchySeries
    (powerSeriesTerms (rescaleCoefficients c coefficients) x)
rescalePowerSeriesIsCauchy c coefficients x cauchy =
  subst IsCauchySeries
    (sym (powerSeriesTerms-rescale-sequence c coefficients x))
    cauchy


rescalePowerSeriesReflectsIsCauchy : ∀ c coefficients x →
  IsCauchySeries
      (powerSeriesTerms (rescaleCoefficients c coefficients) x) →
  IsCauchySeries (powerSeriesTerms coefficients (c · x))
rescalePowerSeriesReflectsIsCauchy c coefficients x cauchy =
  subst IsCauchySeries
    (powerSeriesTerms-rescale-sequence c coefficients x)
    cauchy


rescalePowerSeriesIsAbsolutelyCauchy : ∀ c coefficients x →
  IsAbsolutelyCauchySeries
      (powerSeriesTerms coefficients (c · x)) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms (rescaleCoefficients c coefficients) x)
rescalePowerSeriesIsAbsolutelyCauchy c coefficients x cauchy =
  subst IsAbsolutelyCauchySeries
    (sym (powerSeriesTerms-rescale-sequence c coefficients x))
    cauchy


rescalePowerSeriesReflectsIsAbsolutelyCauchy :
  ∀ c coefficients x →
  IsAbsolutelyCauchySeries
      (powerSeriesTerms (rescaleCoefficients c coefficients) x) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients (c · x))
rescalePowerSeriesReflectsIsAbsolutelyCauchy
  c coefficients x cauchy =
    subst IsAbsolutelyCauchySeries
      (powerSeriesTerms-rescale-sequence c coefficients x)
      cauchy


rescalePowerSeriesSummable : ∀ c coefficients x →
  PowerSeriesSummableAt coefficients (c · x) →
  PowerSeriesSummableAt (rescaleCoefficients c coefficients) x
rescalePowerSeriesSummable c coefficients x summable =
  subst Summable
    (sym (powerSeriesTerms-rescale-sequence c coefficients x))
    summable


rescalePowerSeriesReflectsSummable : ∀ c coefficients x →
  PowerSeriesSummableAt (rescaleCoefficients c coefficients) x →
  PowerSeriesSummableAt coefficients (c · x)
rescalePowerSeriesReflectsSummable c coefficients x summable =
  subst Summable
    (powerSeriesTerms-rescale-sequence c coefficients x)
    summable


rescalePowerSeriesHasSum : ∀ c coefficients x value →
  HasSum (powerSeriesTerms coefficients (c · x)) value →
  HasSum
    (powerSeriesTerms (rescaleCoefficients c coefficients) x) value
rescalePowerSeriesHasSum c coefficients x value has-sum =
  subst (λ terms → HasSum terms value)
    (sym (powerSeriesTerms-rescale-sequence c coefficients x))
    has-sum


rescalePowerSeriesReflectsHasSum : ∀ c coefficients x value →
  HasSum
      (powerSeriesTerms (rescaleCoefficients c coefficients) x) value →
  HasSum (powerSeriesTerms coefficients (c · x)) value
rescalePowerSeriesReflectsHasSum c coefficients x value has-sum =
  subst (λ terms → HasSum terms value)
    (powerSeriesTerms-rescale-sequence c coefficients x)
    has-sum


powerSeriesValue-rescale : ∀ c coefficients x →
  (original-summable :
    PowerSeriesSummableAt coefficients (c · x)) →
  (rescaled-summable :
    PowerSeriesSummableAt (rescaleCoefficients c coefficients) x) →
  powerSeriesValue
      (rescaleCoefficients c coefficients) x rescaled-summable
    ≡
  powerSeriesValue coefficients (c · x) original-summable
powerSeriesValue-rescale
  c coefficients x original-summable rescaled-summable =
  seriesSumPresPath
    (powerSeriesTerms (rescaleCoefficients c coefficients) x)
    (powerSeriesTerms coefficients (c · x))
    (powerSeriesTerms-rescale-sequence c coefficients x)
    rescaled-summable original-summable
