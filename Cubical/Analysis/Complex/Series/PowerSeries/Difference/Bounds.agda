module Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base using (RealSequence)
import Cubical.Analysis.Real.Series.PowerSeries.Difference as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference

-- Compare with the already proved real divided difference on the diagonal.
-- Its diagonal identity supplies the familiar (n + 1) R^n bound.
opaque
  private
    factorBound : ∀ x y radius → normℂ x ≤ℝ radius → normℂ y ≤ℝ radius → ∀ n →
      normℂ (powerDifferenceFactorℂ x y n) ≤ℝ Real.powerDifferenceFactor radius radius n
    factorBound x y radius bx by zero = subst (_≤ℝ 1ℝ)
      (sym (cong normℂ (powerDifferenceFactorℂ-zero x y) ∙ normℂ-one)) (≤ℝ-refl 1ℝ)
    factorBound x y radius bx by (suc n) = subst
      (λ z → normℂ z ≤ℝ Real.powerDifferenceFactor radius radius (suc n))
      (sym (powerDifferenceFactorℂ-step x y n)) (normℂ-addBound
      (y ^ℂ suc n) (x ·ℂ powerDifferenceFactorℂ x y n)
      (powℝ radius (suc n)) (radius · Real.powerDifferenceFactor radius radius n)
      (complexPowerNormBoundOn y radius by (suc n))
      (normℂ-mulBound x (powerDifferenceFactorℂ x y n) radius (Real.powerDifferenceFactor radius radius n)
        bx (factorBound x y radius bx by n)))

opaque
  powerDifferenceFactorℂBound : ∀ x y radius → normℂ x ≤ℝ radius → normℂ y ≤ℝ radius → ∀ n →
    normℂ (powerDifferenceFactorℂ x y n) ≤ℝ realNatural (suc n) · powℝ radius n
  powerDifferenceFactorℂBound x y radius bx by n =
    subst (normℂ (powerDifferenceFactorℂ x y n) ≤ℝ_) (Real.powerDifferenceFactor-diagonal radius n)
      (factorBound x y radius bx by n)

-- A single real majorant controls both the divided-difference series and
-- the formal derivative. Its native Cauchy witness will be supplied once.
complexPowerSeriesDerivativeMajorant : ComplexSequence → ℝ → RealSequence
complexPowerSeriesDerivativeMajorant coefficients radius n =
  normℂ (coefficients (suc n)) · (realNatural (suc n) · powℝ radius n)

opaque
  powerSeriesDifferenceFactorℂBound : ∀ coefficients x y radius →
    normℂ x ≤ℝ radius → normℂ y ≤ℝ radius → ∀ n →
    normℂ (powerSeriesDifferenceFactorℂ coefficients x y n) ≤ℝ complexPowerSeriesDerivativeMajorant coefficients radius n
  powerSeriesDifferenceFactorℂBound coefficients x y radius bx by n =
    normℂ-mulBound (coefficients (suc n)) (powerDifferenceFactorℂ x y n)
      (normℂ (coefficients (suc n))) (realNatural (suc n) · powℝ radius n)
      (≤ℝ-refl (normℂ (coefficients (suc n)))) (powerDifferenceFactorℂBound x y radius bx by n)

opaque
  formalDerivativeℂTermBound : ∀ coefficients x radius → normℂ x ≤ℝ radius → ∀ n →
    normℂ (powerSeriesTermsℂ (formalDerivativeℂ coefficients) x n) ≤ℝ complexPowerSeriesDerivativeMajorant coefficients radius n
  formalDerivativeℂTermBound coefficients x radius bx n =
    subst (λ z → normℂ z ≤ℝ complexPowerSeriesDerivativeMajorant coefficients radius n)
      (powerSeriesDifferenceFactorℂ-diagonal coefficients x n)
      (powerSeriesDifferenceFactorℂBound coefficients x x radius bx bx n)
