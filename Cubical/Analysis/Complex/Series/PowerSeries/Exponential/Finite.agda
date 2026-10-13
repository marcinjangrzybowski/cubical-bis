module Cubical.Analysis.Complex.Series.PowerSeries.Exponential.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat as ℕ using (zero; suc; _∸_) renaming (_choose_ to _chooseℕ_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData using (toℕ)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Analysis.Real.Algebra.Natural using (realNatural)
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients as Real
open import Cubical.Analysis.Real.Algebra.CommRing
import Cubical.Analysis.Real.FiniteSum.Reindexing as Real
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Product.Finite as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.DividedPowers as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.Product.Finite
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Algebra as Algebra

private
  module B = BinomialThm ℂCommRing
  module BH = Algebra.BinomialHom realToComplexHom
  module A = Algebra.FiniteAlgebra ℂCommRing

-- Reuse the real divided-factorial identity, transporting its binomial
-- coefficient through the existing real-to-complex ring homomorphism.
opaque
  exponentialCoefficientℂ-product : ∀ n k → k ℕ.≤ n →
    exponentialCoefficientsℂ k ·ℂ exponentialCoefficientsℂ (n ∸ k)
      ≡ B._choose_ n k ·ℂ exponentialCoefficientsℂ n
  exponentialCoefficientℂ-product n k below = sym (fromℝ-pres· (Real.exponentialCoefficients k) (Real.exponentialCoefficients (n ∸ k)))
    ∙ cong fromℝ (Real.exponentialCoefficient-product n k below)
    ∙ fromℝ-pres· (realNatural (_chooseℕ_ n k)) (Real.exponentialCoefficients n)
    ∙ cong (_·ℂ exponentialCoefficientsℂ n)
        (cong fromℝ (sym (Real.realBinomialCoefficient-agreesNatural n k)) ∙ BH.preservesBinomial n k)

opaque
  partialSumℂ-as-finSum : ∀ terms n → partialSumℂ terms n ≡ Sum.∑ (CommRing→Ring ℂCommRing) {n = n} (terms ∘ toℕ)
  partialSumℂ-as-finSum = A.prefixSumToFinSum partialSumℂ (λ _ → refl)
    (λ terms n → ℂ≡ (Real.partialSum-first (re ∘ terms) n) (Real.partialSum-first (im ∘ terms) n))

opaque
  exponentialAdditionConvolutionℂTerm : ∀ z w n →
    cauchyProductℂ (powerSeriesTermsℂ exponentialCoefficientsℂ z) (powerSeriesTermsℂ exponentialCoefficientsℂ w) n
      ≡ powerSeriesTermsℂ exponentialCoefficientsℂ (z +ℂ w) n
  exponentialAdditionConvolutionℂTerm z w n = partialSumℂ-as-finSum
    (λ k → powerSeriesTermsℂ exponentialCoefficientsℂ z k ·ℂ powerSeriesTermsℂ exponentialCoefficientsℂ w (n ∸ k)) (suc n)
    ∙ A.dividedPowerAddition exponentialCoefficientsℂ exponentialCoefficientℂ-product z w n
