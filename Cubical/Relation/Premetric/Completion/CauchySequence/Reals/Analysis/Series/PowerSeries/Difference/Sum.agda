module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference


powerSeriesDifferenceFactorDiagonalValue :
  ∀ coefficients x →
  (factor-summable :
    Summable (powerSeriesDifferenceFactor coefficients x x)) →
  (derivative-summable :
    PowerSeriesSummableAt (formalDerivative coefficients) x) →
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
  (x-summable : PowerSeriesSummableAt coefficients x) →
  (y-summable : PowerSeriesSummableAt coefficients y) →
  (factor-summable :
    Summable (powerSeriesDifferenceFactor coefficients x y)) →
  powerSeriesValue coefficients y y-summable Group.-
    powerSeriesValue coefficients x x-summable
    ≡
  (y Group.- x) Mul.·
    seriesSum
      (powerSeriesDifferenceFactor coefficients x y)
      factor-summable
powerSeriesValueDifferenceFactorization
  coefficients x y x-summable y-summable factor-summable =
  cong fst
    (isPropSequenceLimit
      right-partial-sums
      (value-difference , right-limit-from-finite-identity)
      (factorized-value , right-limit))
  where
  x-terms : RealSequence
  x-terms = powerSeriesTerms coefficients x

  y-terms : RealSequence
  y-terms = powerSeriesTerms coefficients y

  factor-terms : RealSequence
  factor-terms = powerSeriesDifferenceFactor coefficients x y

  value-difference : Real.ℝ
  value-difference =
    powerSeriesValue coefficients y y-summable Group.-
      powerSeriesValue coefficients x x-summable

  factorized-value : Real.ℝ
  factorized-value =
    (y Group.- x) Mul.· seriesSum factor-terms factor-summable

  left-partial-sums : RealSequence
  left-partial-sums n =
    partialSum y-terms (suc n) Group.-
      partialSum x-terms (suc n)

  right-partial-sums : RealSequence
  right-partial-sums n =
    (y Group.- x) Mul.· partialSum factor-terms n

  left-limit : isLimitSequence left-partial-sums value-difference
  left-limit =
    subPresIsLimitSequence
      (shiftPresIsLimitSequence
        1 (partialSum y-terms)
        (powerSeriesValue coefficients y y-summable)
        (seriesSumHasSum y-terms y-summable))
      (shiftPresIsLimitSequence
        1 (partialSum x-terms)
        (powerSeriesValue coefficients x x-summable)
        (seriesSumHasSum x-terms x-summable))

  finite-identity :
    EventuallyEqualSequence left-partial-sums right-partial-sums
  finite-identity =
    ∣ 0 , (λ n _ → finitePowerSeriesDifference coefficients x y n) ∣₁

  right-limit-from-finite-identity :
    isLimitSequence right-partial-sums value-difference
  right-limit-from-finite-identity =
    eventuallyEqualPresIsLimitSequence finite-identity left-limit

  right-limit :
    isLimitSequence right-partial-sums factorized-value
  right-limit =
    mulPresIsLimitSequence
      (constantIsLimitSequence (y Group.- x))
      (seriesSumHasSum factor-terms factor-summable)
