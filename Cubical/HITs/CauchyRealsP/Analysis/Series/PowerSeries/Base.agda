module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (zero)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations

powerSeriesTerms :
  RealSequence → ℝ → RealSequence
powerSeriesTerms coefficients x n =
  coefficients n · x ^ⁿ n

CoefficientAbsBound :
  ℚ₊ → RealSequence → Type
CoefficientAbsBound C coefficients =
  ∀ n →
  absℝ (coefficients n)
    ≤ℝ rat (fst C)

PowerSeriesSummableAt :
  RealSequence → ℝ → Type
PowerSeriesSummableAt coefficients x =
  Summable (powerSeriesTerms coefficients x)

powerSeriesValue :
  ∀ coefficients x →
  PowerSeriesSummableAt coefficients x →
  ℝ
powerSeriesValue coefficients x summable =
  seriesSum
    (powerSeriesTerms coefficients x)
    summable

powerSeriesTerms-zero : ∀ coefficients →
  powerSeriesTerms coefficients 0 zero ≡
  coefficients zero
powerSeriesTerms-zero coefficients =
  mulIdR (coefficients zero)

powerSeriesTerms-add : ∀ a b x n →
  powerSeriesTerms
      (λ k → a k + b k) x n
    ≡
  powerSeriesTerms a x n
    + powerSeriesTerms b x n
powerSeriesTerms-add a b x n =
  mulDistL
    (a n) (b n) (x ^ⁿ n)

powerSeriesTerms-scale : ∀ c coefficients x n →
  powerSeriesTerms
      (scaleSeries c coefficients)
      x n
    ≡
  scaleSeries c
    (powerSeriesTerms coefficients x)
    n
powerSeriesTerms-scale c coefficients x n =
  mulAssoc c (coefficients n) (x ^ⁿ n)
