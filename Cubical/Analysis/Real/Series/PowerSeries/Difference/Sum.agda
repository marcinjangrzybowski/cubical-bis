module Cubical.Analysis.Real.Series.PowerSeries.Difference.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Tails
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference


powerSeriesDifferenceFactorDiagonalValue :
  ∀ coefficients x →
  (factor-summable :
    Summable
      (powerSeriesDifferenceFactor coefficients x x)) →
  (derivative-summable :
    PowerSeriesSummableAt
      (formalDerivative coefficients) x) →
  seriesSum
      (powerSeriesDifferenceFactor coefficients x x)
      factor-summable
    ≡
  powerSeriesValue
    (formalDerivative coefficients) x derivative-summable
powerSeriesDifferenceFactorDiagonalValue
  coefficients x factor-summable derivative-summable =
  seriesSumPresPath
    (powerSeriesDifferenceFactor coefficients x x)
    (powerSeriesTerms (formalDerivative coefficients) x)
    (powerSeriesDifferenceFactor-diagonal coefficients x)
    factor-summable derivative-summable


powerSeriesValueDifferenceFactorization :
  ∀ coefficients x y →
  (x-summable :
    PowerSeriesSummableAt coefficients x) →
  (y-summable :
    PowerSeriesSummableAt coefficients y) →
  (factor-summable :
    Summable
      (powerSeriesDifferenceFactor coefficients x y)) →
  powerSeriesValue coefficients y y-summable
      - powerSeriesValue coefficients x x-summable
    ≡
  (y - x) ·
    seriesSum
      (powerSeriesDifferenceFactor coefficients x y)
      factor-summable
powerSeriesValueDifferenceFactorization
  coefficients x y
  x-summable y-summable factor-summable =
  sym
    (seriesSum-sub
      y-terms x-terms
      y-summable x-summable difference-summable)
  ∙ seriesSum-from-drop
      (suc zero) difference-terms
      tail-summable difference-summable
  ∙ cong
      (_+ seriesSum tail-terms tail-summable)
      first-partial-sum-zero
  ∙ addIdL (seriesSum tail-terms tail-summable)
  ∙ seriesSumPresPath
      tail-terms scaled-factor-terms
      tail-path
      tail-summable scaled-factor-summable
  ∙ seriesSum-scale
      (y - x) factor-terms
      factor-summable scaled-factor-summable
  where
  x-terms : RealSequence
  x-terms =
    powerSeriesTerms coefficients x

  y-terms : RealSequence
  y-terms =
    powerSeriesTerms coefficients y

  factor-terms : RealSequence
  factor-terms =
    powerSeriesDifferenceFactor coefficients x y

  difference-terms : RealSequence
  difference-terms n =
    y-terms n - x-terms n

  scaled-factor-terms : RealSequence
  scaled-factor-terms =
    scaleSeries (y - x) factor-terms

  difference-summable : Summable difference-terms
  difference-summable =
    subSummable
      y-terms x-terms y-summable x-summable

  tail-terms : RealSequence
  tail-terms =
    dropSeries (suc zero) difference-terms

  tail-summable : Summable tail-terms
  tail-summable =
    dropSeriesSummable
      (suc zero) difference-terms difference-summable

  scaled-factor-summable : Summable scaled-factor-terms
  scaled-factor-summable =
    scaleSummable
      (y - x) factor-terms factor-summable

  first-partial-sum-zero :
    partialSum difference-terms (suc zero) ≡ 0ℝ
  first-partial-sum-zero =
    addIdL (difference-terms zero)
    ∙ cong₂ _-_
        (mulIdR (coefficients zero))
        (mulIdR (coefficients zero))
    ∙ subSelf (coefficients zero)

  tail-path : tail-terms ≡ scaled-factor-terms
  tail-path =
    funExt λ n →
      cong
        difference-terms
        (ℕ.+-suc n zero
          ∙ cong suc (ℕ.+-zero n))
      ∙ powerSeriesDifferenceFactor-identity
          coefficients x y n
