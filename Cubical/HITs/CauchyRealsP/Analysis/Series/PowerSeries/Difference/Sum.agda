module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference

powerSeriesDifferenceFactorDiagonalValue :
  ∀ coefficients x →
  (factor-summable :
    Summable
      (powerSeriesDifferenceFactor
        coefficients x x)) →
  (derivative-summable :
    PowerSeriesSummableAt
      (formalDerivative coefficients)
      x) →
  seriesSum
      (powerSeriesDifferenceFactor
        coefficients x x)
      factor-summable
    ≡
  powerSeriesValue
    (formalDerivative coefficients)
    x derivative-summable
powerSeriesDifferenceFactorDiagonalValue
  coefficients x
  factor-summable derivative-summable =
    seriesSumPresPath
      (powerSeriesDifferenceFactor
        coefficients x x)
      (powerSeriesTerms
        (formalDerivative coefficients)
        x)
      (powerSeriesDifferenceFactor-diagonal
        coefficients x)
      factor-summable derivative-summable

powerSeriesValueDifferenceFactorization :
  ∀ coefficients x y →
  (x-summable :
    PowerSeriesSummableAt coefficients x) →
  (y-summable :
    PowerSeriesSummableAt coefficients y) →
  (factor-summable :
    Summable
      (powerSeriesDifferenceFactor
        coefficients x y)) →
  powerSeriesValue
      coefficients y y-summable
    -
  powerSeriesValue
      coefficients x x-summable
    ≡
  (y - x)
    · seriesSum
        (powerSeriesDifferenceFactor
          coefficients x y)
        factor-summable
powerSeriesValueDifferenceFactorization
  coefficients x y
  x-summable y-summable factor-summable =
    cong fst
      (isPropLimitSeq
        right-partial-sums
        ( value-difference
        , right-limit-from-finite-identity
        )
        ( factorized-value
        , right-limit
        ))
  where
  x-terms : RealSequence
  x-terms =
    powerSeriesTerms coefficients x

  y-terms : RealSequence
  y-terms =
    powerSeriesTerms coefficients y

  factor-terms : RealSequence
  factor-terms =
    powerSeriesDifferenceFactor
      coefficients x y

  value-difference : ℝ
  value-difference =
    powerSeriesValue coefficients y y-summable
      - powerSeriesValue coefficients x x-summable

  factorized-value : ℝ
  factorized-value =
    (y - x)
      · seriesSum factor-terms factor-summable

  left-partial-sums : RealSequence
  left-partial-sums n =
    partialSum y-terms (suc n)
      - partialSum x-terms (suc n)

  right-partial-sums : RealSequence
  right-partial-sums n =
    (y - x) · partialSum factor-terms n

  left-limit :
    isLimitSeq
      left-partial-sums value-difference
  left-limit =
    subPresIsLimitSeq
      (shiftSeq 1 (partialSum y-terms))
      (shiftSeq 1 (partialSum x-terms))
      (powerSeriesValue
        coefficients y y-summable)
      (powerSeriesValue
        coefficients x x-summable)
      (shiftPresIsLimitSeq
        1 (partialSum y-terms)
        (powerSeriesValue
          coefficients y y-summable)
        (seriesSumHasSum
          y-terms y-summable))
      (shiftPresIsLimitSeq
        1 (partialSum x-terms)
        (powerSeriesValue
          coefficients x x-summable)
        (seriesSumHasSum
          x-terms x-summable))

  finite-identity :
    EventuallyEqualSeq
      left-partial-sums
      right-partial-sums
  finite-identity =
    0
    , λ n _ →
        finitePowerSeriesDifference
          coefficients x y n

  right-limit-from-finite-identity :
    isLimitSeq
      right-partial-sums value-difference
  right-limit-from-finite-identity =
    eventuallyEqualSeqPresIsLimitSeq
      left-partial-sums
      right-partial-sums
      value-difference
      finite-identity
      left-limit

  right-limit :
    isLimitSeq
      right-partial-sums factorized-value
  right-limit =
    mulPresIsLimitSeq
      (λ _ → y - x)
      (partialSum factor-terms)
      (y - x)
      (seriesSum factor-terms factor-summable)
      (constantIsLimitSeq (y - x))
      (seriesSumHasSum
        factor-terms factor-summable)
