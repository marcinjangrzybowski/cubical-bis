module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Summands where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Algebra.CommRing.BinomialThm

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Signs
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Algebra


private
  module ℝBinomial = BinomialThm ℝCommRing


-- This is the sole divided-power fact needed by the trigonometric summand
-- calculation.  Naming the interface keeps the sign algebra reusable while
-- the factorial/binomial development remains independent.

ExponentialProductSummandBinomial : Type₀
ExponentialProductSummandBinomial =
  ∀ x y n k → (k≤n : k ℕ.≤ n) →
  powerSeriesTerms exponentialCoefficients x k ·
      powerSeriesTerms exponentialCoefficients y (n ∸ k)
    ≡
  exponentialCoefficients n ·
    ((ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k))


sineAdditionProductSummandFromDividedPowers :
  ExponentialProductSummandBinomial →
  ∀ x y n k → (k≤n : k ℕ.≤ n) →
  ( powerSeriesTerms sineCoefficients x k ·
      powerSeriesTerms cosineCoefficients y (n ∸ k))
    +
  ( powerSeriesTerms cosineCoefficients x k ·
      powerSeriesTerms sineCoefficients y (n ∸ k))
    ≡
  sineCoefficients n ·
    ((ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k))
sineAdditionProductSummandFromDividedPowers
    exponential-summand x y n k k≤n =
  expand-coefficients
  ∙ combine-sine-products
      (sineSign k) (cosineSign k)
      (sineSign remainder) (cosineSign remainder)
      (exponentialCoefficients k) (powℝ x k)
      (exponentialCoefficients remainder) (powℝ y remainder)
  ∙ cong (_· (left-term · right-term))
      (fst (trigonometricSign-addition k remainder))
  ∙ cong
      (λ index → sineSign index · (left-term · right-term))
      total-index
  ∙ cong (sineSign n ·_)
      (exponential-summand x y n k k≤n)
  ∙ mulAssoc
      (sineSign n) (exponentialCoefficients n) binomial-term
  ∙ cong (_· binomial-term)
      (sym (sineCoefficient-as-sign n))
  where
  remainder : ℕ
  remainder = n ∸ k

  left-term right-term binomial-term : ℝ
  left-term = exponentialCoefficients k · powℝ x k
  right-term = exponentialCoefficients remainder · powℝ y remainder
  binomial-term =
    (ℝBinomial._choose_ n k · powℝ x k) · powℝ y remainder

  total-index : k ℕ.+ remainder ≡ n
  total-index =
    ℕ.+-comm k remainder ∙ ℕ.≤-∸-+-cancel k≤n

  expand-coefficients :
    ( powerSeriesTerms sineCoefficients x k ·
        powerSeriesTerms cosineCoefficients y remainder)
      +
    ( powerSeriesTerms cosineCoefficients x k ·
        powerSeriesTerms sineCoefficients y remainder)
      ≡
    (((sineSign k · exponentialCoefficients k) · powℝ x k) ·
      ((cosineSign remainder · exponentialCoefficients remainder) ·
        powℝ y remainder))
      +
    (((cosineSign k · exponentialCoefficients k) · powℝ x k) ·
      ((sineSign remainder · exponentialCoefficients remainder) ·
        powℝ y remainder))
  expand-coefficients =
    cong₂ _+_
      (cong₂ _·_
        (cong (_· powℝ x k) (sineCoefficient-as-sign k))
        (cong (_· powℝ y remainder)
          (cosineCoefficient-as-sign remainder)))
      (cong₂ _·_
        (cong (_· powℝ x k) (cosineCoefficient-as-sign k))
        (cong (_· powℝ y remainder)
          (sineCoefficient-as-sign remainder)))


cosineAdditionProductSummandFromDividedPowers :
  ExponentialProductSummandBinomial →
  ∀ x y n k → (k≤n : k ℕ.≤ n) →
  ( powerSeriesTerms cosineCoefficients x k ·
      powerSeriesTerms cosineCoefficients y (n ∸ k))
    -
  ( powerSeriesTerms sineCoefficients x k ·
      powerSeriesTerms sineCoefficients y (n ∸ k))
    ≡
  cosineCoefficients n ·
    ((ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k))
cosineAdditionProductSummandFromDividedPowers
    exponential-summand x y n k k≤n =
  expand-coefficients
  ∙ combine-cosine-products
      (sineSign k) (cosineSign k)
      (sineSign remainder) (cosineSign remainder)
      (exponentialCoefficients k) (powℝ x k)
      (exponentialCoefficients remainder) (powℝ y remainder)
  ∙ cong (_· (left-term · right-term))
      (snd (trigonometricSign-addition k remainder))
  ∙ cong
      (λ index → cosineSign index · (left-term · right-term))
      total-index
  ∙ cong (cosineSign n ·_)
      (exponential-summand x y n k k≤n)
  ∙ mulAssoc
      (cosineSign n) (exponentialCoefficients n) binomial-term
  ∙ cong (_· binomial-term)
      (sym (cosineCoefficient-as-sign n))
  where
  remainder : ℕ
  remainder = n ∸ k

  left-term right-term binomial-term : ℝ
  left-term = exponentialCoefficients k · powℝ x k
  right-term = exponentialCoefficients remainder · powℝ y remainder
  binomial-term =
    (ℝBinomial._choose_ n k · powℝ x k) · powℝ y remainder

  total-index : k ℕ.+ remainder ≡ n
  total-index =
    ℕ.+-comm k remainder ∙ ℕ.≤-∸-+-cancel k≤n

  expand-coefficients :
    ( powerSeriesTerms cosineCoefficients x k ·
        powerSeriesTerms cosineCoefficients y remainder)
      -
    ( powerSeriesTerms sineCoefficients x k ·
        powerSeriesTerms sineCoefficients y remainder)
      ≡
    (((cosineSign k · exponentialCoefficients k) · powℝ x k) ·
      ((cosineSign remainder · exponentialCoefficients remainder) ·
        powℝ y remainder))
      -
    (((sineSign k · exponentialCoefficients k) · powℝ x k) ·
      ((sineSign remainder · exponentialCoefficients remainder) ·
        powℝ y remainder))
  expand-coefficients =
    cong₂ _-_
      (cong₂ _·_
        (cong (_· powℝ x k) (cosineCoefficient-as-sign k))
        (cong (_· powℝ y remainder)
          (cosineCoefficient-as-sign remainder)))
      (cong₂ _·_
        (cong (_· powℝ x k) (sineCoefficient-as-sign k))
        (cong (_· powℝ y remainder)
          (sineCoefficient-as-sign remainder)))
