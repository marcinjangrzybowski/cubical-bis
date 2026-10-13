module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as Nat
import Cubical.Data.Rationals.Inverse as Rational
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative as Real
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.DividedPowers as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Algebra as Elementary
import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Algebra as Algebra

private
  module A = Algebra.TranslationAlgebra ℝCommRing
  module B = BinomialThm ℂCommRing
  module BH = Elementary.BinomialHom realToComplexHom

-- Reuse the exponential fixed-point and existing divided-power identity.
-- No second factorial or binomial recurrence is introduced.
opaque
  normalizedDerivativeMultiplier : ∀ order index →
    Real.exponentialCoefficients order · realNatural (Real.derivativeNaturalProduct index order)
      ≡ realNatural (Nat._choose_ (index Nat.+ order) order)
  normalizedDerivativeMultiplier order index = A.cancelRightWithInverse
    (Real.exponentialCoefficients order · realNatural (Real.derivativeNaturalProduct index order))
    (realNatural (Nat._choose_ total order)) (Real.exponentialCoefficients total)
    (rat (fst (Real.exponentialRationalFactorial total)))
    (mul-rat (Real.exponentialRationalCoefficient total) (fst (Real.exponentialRationalFactorial total))
      ∙ cong rat (Rational.invℚ₊[x]·x (Real.exponentialRationalFactorial total)))
    (sym (mulAssoc (Real.exponentialCoefficients order) (realNatural (Real.derivativeNaturalProduct index order))
        (Real.exponentialCoefficients total))
      ∙ cong (Real.exponentialCoefficients order ·_)
          (sym (Real.repeatedFormalDerivative-coefficient order Real.exponentialCoefficients index)
            ∙ funExt⁻ (Real.repeatedFormalDerivative-exponentialCoefficients order) index)
      ∙ cong (Real.exponentialCoefficients order ·_)
          (cong Real.exponentialCoefficients (sym (Nat.+∸ index order)))
      ∙ Real.exponentialCoefficient-product total order (index , refl))
    where
    total : ℕ
    total = index Nat.+ order

binomialCoefficientℂ : ℕ → ℕ → ℂ
binomialCoefficientℂ n k = fromℝ (realNatural (Nat._choose_ n k))

opaque
  binomialCoefficientℂ-agreesRing : ∀ n k → binomialCoefficientℂ n k ≡ B._choose_ n k
  binomialCoefficientℂ-agreesRing n k =
    cong fromℝ (sym (Real.realBinomialCoefficient-agreesNatural n k)) ∙ BH.preservesBinomial n k

  normalizedDerivativeMultiplierℂ : ∀ order index →
    exponentialCoefficientsℂ order ·ℂ fromℝ (realNatural (Real.derivativeNaturalProduct index order))
      ≡ binomialCoefficientℂ (index Nat.+ order) order
  normalizedDerivativeMultiplierℂ order index =
    sym (fromℝ-pres· (Real.exponentialCoefficients order) (realNatural (Real.derivativeNaturalProduct index order)))
      ∙ cong fromℝ (normalizedDerivativeMultiplier order index)
