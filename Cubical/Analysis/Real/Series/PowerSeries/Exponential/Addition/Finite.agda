module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.DividedPowers
  using (exponentialProductSummand-binomial; partialSum-as-finSum)


private
  module ℝBinomial = BinomialThm ℝCommRing
  module ℝExponentiation = Exponentiation ℝCommRing
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

  powℝ-as-ringPower : ∀ x n →
    powℝ x n ≡ ℝExponentiation._^_ x n
  powℝ-as-ringPower x zero = refl
  powℝ-as-ringPower x (suc n) =
    cong (x ·_) (powℝ-as-ringPower x n)

  powℝ-binomial : ∀ n x y →
    powℝ (x + y) n ≡
    ℝSum.∑ {n = suc n}
      ((λ k →
        (ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k)) ∘ toℕ)
  powℝ-binomial n x y =
    powℝ-as-ringPower (x + y) n
    ∙ ℝBinomial.BinomialThm n x y
    ∙ ℝSum.∑Ext (λ (i : Fin (suc n)) →
        cong₂ _·_
          (cong (ℝBinomial._choose_ n (toℕ i) ·_)
            (sym (powℝ-as-ringPower x (toℕ i))))
          (sym (powℝ-as-ringPower y (n ∸ toℕ i))))


-- The existing divided-power identity identifies each finite anti-diagonal
-- with a binomial expansion.  No rearrangement of an infinite sum occurs here.
exponentialAdditionConvolutionTerm : ∀ x y n →
  cauchyProduct
    (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesTerms exponentialCoefficients y) n
  ≡ powerSeriesTerms exponentialCoefficients (x + y) n
exponentialAdditionConvolutionTerm x y n =
  partialSum-pointwiseBefore
    (λ k →
      powerSeriesTerms exponentialCoefficients x k ·
      powerSeriesTerms exponentialCoefficients y (n ∸ k))
    (scaleSeries (exponentialCoefficients n) binomial-terms)
    (suc n)
    (λ k k<sucn →
      exponentialProductSummand-binomial x y n k
        (ℕ.pred-≤-pred k<sucn))
  ∙ partialSum-scale
      (exponentialCoefficients n) binomial-terms (suc n)
  ∙ cong (exponentialCoefficients n ·_)
      (partialSum-as-finSum binomial-terms (suc n))
  ∙ cong (exponentialCoefficients n ·_) (sym (powℝ-binomial n x y))
  where
  binomial-terms : RealSequence
  binomial-terms k =
    (ℝBinomial._choose_ n k · powℝ x k) · powℝ y (n ∸ k)

exponentialAdditionConvolutionTerms : ∀ x y →
  cauchyProduct
    (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesTerms exponentialCoefficients y)
  ≡ powerSeriesTerms exponentialCoefficients (x + y)
exponentialAdditionConvolutionTerms x y =
  funExt (exponentialAdditionConvolutionTerm x y)
