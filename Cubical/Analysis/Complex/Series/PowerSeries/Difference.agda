module Cubical.Analysis.Complex.Series.PowerSeries.Difference where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Continuity.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Algebra as Algebra

private
  module D = Algebra.DifferenceAlgebra ℂCommRing

opaque
  powerDifferenceFactorℂ : ℂ → ℂ → ℕ → ℂ
  powerDifferenceFactorℂ = D.factor

opaque
  unfolding powerDifferenceFactorℂ

  powerDifferenceFactorℂ-zero : ∀ x y → powerDifferenceFactorℂ x y zero ≡ 1ℂ
  powerDifferenceFactorℂ-zero = D.zeroEquation

  powerDifferenceFactorℂ-step : ∀ x y n →
    powerDifferenceFactorℂ x y (suc n) ≡ (y ^ℂ suc n) +ℂ x ·ℂ powerDifferenceFactorℂ x y n
  powerDifferenceFactorℂ-step = D.stepEquation

-- Weight the shifted coefficients by the existing native real natural.
formalDerivativeℂ : ComplexSequence → ComplexSequence
formalDerivativeℂ coefficients n = fromℝ (realNatural (suc n)) ·ℂ coefficients (suc n)

powerSeriesDifferenceFactorℂ : ComplexSequence → ℂ → ℂ → ComplexSequence
powerSeriesDifferenceFactorℂ coefficients x y n = coefficients (suc n) ·ℂ powerDifferenceFactorℂ x y n

opaque
  unfolding powerDifferenceFactorℂ

  powerDifferenceFactorℂ-identity : ∀ x y n →
    (y ^ℂ suc n) -ℂ (x ^ℂ suc n) ≡ (y -ℂ x) ·ℂ powerDifferenceFactorℂ x y n
  powerDifferenceFactorℂ-identity = D.identity

  powerSeriesDifferenceFactorℂ-identity : ∀ coefficients x y n →
    powerSeriesTermsℂ coefficients y (suc n) -ℂ powerSeriesTermsℂ coefficients x (suc n)
      ≡ (y -ℂ x) ·ℂ powerSeriesDifferenceFactorℂ coefficients x y n
  powerSeriesDifferenceFactorℂ-identity coefficients x y n = D.coefficientIdentity (coefficients (suc n)) x y n


opaque
  unfolding powerDifferenceFactorℂ

  powerSeriesDifferenceFactorℂ-diagonal : ∀ coefficients x n →
    powerSeriesDifferenceFactorℂ coefficients x x n ≡ powerSeriesTermsℂ (formalDerivativeℂ coefficients) x n
  powerSeriesDifferenceFactorℂ-diagonal coefficients x n =
    D.coefficientDiagonal (λ k → fromℝ (realNatural k)) refl
      (λ k → cong fromℝ (realNatural-suc k) ∙ fromℝ-pres+ (realNatural k) 1ℝ) (coefficients (suc n)) x n

