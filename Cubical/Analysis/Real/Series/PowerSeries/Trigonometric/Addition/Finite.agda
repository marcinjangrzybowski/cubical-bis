module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.DividedPowers
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Summands
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.HasSum


private
  module ℝBinomial = BinomialThm ℝCommRing
  module ℝExponentiation = Exponentiation ℝCommRing
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

  powℝ-as-ringPower : ∀ x n →
    powℝ x n ≡ ℝExponentiation._^_ x n
  powℝ-as-ringPower x ℕ.zero = refl
  powℝ-as-ringPower x (suc n) =
    cong (x ·_) (powℝ-as-ringPower x n)

  powℝ-binomial : ∀ n x y →
    powℝ (x + y) n ≡
    ℝSum.∑ {n = suc n}
      ((λ k →
        (ℝBinomial._choose_ n k · powℝ x k) ·
          powℝ y (n ∸ k)) ∘ toℕ)
  powℝ-binomial n x y =
    powℝ-as-ringPower (x + y) n
    ∙ ℝBinomial.BinomialThm n x y
    ∙ ℝSum.∑Ext (λ (i : Fin (suc n)) →
        cong₂ _·_
          (cong (ℝBinomial._choose_ n (toℕ i) ·_)
            (sym (powℝ-as-ringPower x (toℕ i))))
          (sym (powℝ-as-ringPower y (n ∸ toℕ i))))


sineAdditionProductSummand : ∀ x y n k →
  (k≤n : k ℕ.≤ n) →
  ( powerSeriesTerms sineCoefficients x k ·
      powerSeriesTerms cosineCoefficients y (n ∸ k))
    +
  ( powerSeriesTerms cosineCoefficients x k ·
      powerSeriesTerms sineCoefficients y (n ∸ k))
    ≡
  sineCoefficients n ·
    ((ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k))
sineAdditionProductSummand =
  sineAdditionProductSummandFromDividedPowers
    exponentialProductSummand-binomial


cosineAdditionProductSummand : ∀ x y n k →
  (k≤n : k ℕ.≤ n) →
  ( powerSeriesTerms cosineCoefficients x k ·
      powerSeriesTerms cosineCoefficients y (n ∸ k))
    -
  ( powerSeriesTerms sineCoefficients x k ·
      powerSeriesTerms sineCoefficients y (n ∸ k))
    ≡
  cosineCoefficients n ·
    ((ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k))
cosineAdditionProductSummand =
  cosineAdditionProductSummandFromDividedPowers
    exponentialProductSummand-binomial


sineAdditionConvolutionTerm : ∀ x y n →
  sineAdditionConvolutionTerms x y n
    ≡ powerSeriesTerms sineCoefficients (x + y) n
sineAdditionConvolutionTerm x y n =
  sym
    (partialSum-add
      (λ k →
        powerSeriesTerms sineCoefficients x k ·
          powerSeriesTerms cosineCoefficients y (n ∸ k))
      (λ k →
        powerSeriesTerms cosineCoefficients x k ·
          powerSeriesTerms sineCoefficients y (n ∸ k))
      (suc n))
  ∙ partialSum-pointwiseBefore
      (λ k →
        (powerSeriesTerms sineCoefficients x k ·
          powerSeriesTerms cosineCoefficients y (n ∸ k))
        +
        (powerSeriesTerms cosineCoefficients x k ·
          powerSeriesTerms sineCoefficients y (n ∸ k)))
      (scaleSeries (sineCoefficients n) binomial-terms)
      (suc n)
      (λ k k<sucn →
        sineAdditionProductSummand x y n k
          (ℕ.pred-≤-pred k<sucn))
  ∙ partialSum-scale
      (sineCoefficients n) binomial-terms (suc n)
  ∙ cong (sineCoefficients n ·_)
      (partialSum-as-finSum binomial-terms (suc n))
  ∙ cong (sineCoefficients n ·_)
      (sym (powℝ-binomial n x y))
  where
  binomial-terms : RealSequence
  binomial-terms k =
    (ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k)


cosineAdditionConvolutionTerm : ∀ x y n →
  cosineAdditionConvolutionTerms x y n
    ≡ powerSeriesTerms cosineCoefficients (x + y) n
cosineAdditionConvolutionTerm x y n =
  sym
    (partialSum-sub
      (λ k →
        powerSeriesTerms cosineCoefficients x k ·
          powerSeriesTerms cosineCoefficients y (n ∸ k))
      (λ k →
        powerSeriesTerms sineCoefficients x k ·
          powerSeriesTerms sineCoefficients y (n ∸ k))
      (suc n))
  ∙ partialSum-pointwiseBefore
      (λ k →
        (powerSeriesTerms cosineCoefficients x k ·
          powerSeriesTerms cosineCoefficients y (n ∸ k))
        -
        (powerSeriesTerms sineCoefficients x k ·
          powerSeriesTerms sineCoefficients y (n ∸ k)))
      (scaleSeries (cosineCoefficients n) binomial-terms)
      (suc n)
      (λ k k<sucn →
        cosineAdditionProductSummand x y n k
          (ℕ.pred-≤-pred k<sucn))
  ∙ partialSum-scale
      (cosineCoefficients n) binomial-terms (suc n)
  ∙ cong (cosineCoefficients n ·_)
      (partialSum-as-finSum binomial-terms (suc n))
  ∙ cong (cosineCoefficients n ·_)
      (sym (powℝ-binomial n x y))
  where
  binomial-terms : RealSequence
  binomial-terms k =
    (ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k)


sineAdditionConvolutionTerms-sequence : ∀ x y →
  sineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms sineCoefficients (x + y)
sineAdditionConvolutionTerms-sequence x y =
  funExt (sineAdditionConvolutionTerm x y)


cosineAdditionConvolutionTerms-sequence : ∀ x y →
  cosineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms cosineCoefficients (x + y)
cosineAdditionConvolutionTerms-sequence x y =
  funExt (cosineAdditionConvolutionTerm x y)
