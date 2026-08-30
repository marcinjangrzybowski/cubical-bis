module Cubical.Analysis.Real.Series.PowerSeries.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (zero)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations

open PositiveRationals using (ℚ₊)


powerSeriesTerms : RealSequence → ℝ → RealSequence
powerSeriesTerms coefficients x n =
  coefficients n · powℝ x n


CoefficientAbsBound : ℚ₊ → RealSequence → Type₀
CoefficientAbsBound bound coefficients =
  ∀ n → absℝ (coefficients n) ≤ℝ rat (fst bound)


PowerSeriesSummableAt : RealSequence → ℝ → Type₀
PowerSeriesSummableAt coefficients x =
  Summable (powerSeriesTerms coefficients x)


powerSeriesValue : ∀ coefficients x →
  PowerSeriesSummableAt coefficients x → ℝ
powerSeriesValue coefficients x =
  seriesSum (powerSeriesTerms coefficients x)


powerSeriesTerms-zero : ∀ coefficients →
  powerSeriesTerms coefficients 0ℝ zero ≡ coefficients zero
powerSeriesTerms-zero coefficients =
  mulIdR (coefficients zero)


powerSeriesTerms-add : ∀ a b x n →
  powerSeriesTerms (λ k → a k + b k) x n ≡
  powerSeriesTerms a x n + powerSeriesTerms b x n
powerSeriesTerms-add a b x n =
  mulDistL (a n) (b n) (powℝ x n)


powerSeriesTerms-scale : ∀ c coefficients x n →
  powerSeriesTerms (scaleSeries c coefficients) x n ≡
  scaleSeries c (powerSeriesTerms coefficients x) n
powerSeriesTerms-scale c coefficients x n =
  sym (mulAssoc c (coefficients n) (powℝ x n))
