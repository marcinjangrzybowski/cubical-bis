module Cubical.Analysis.Complex.Series.PowerSeries.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat as ℕ using (suc; _∸_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.Product.Finite
open import Cubical.Analysis.Complex.Series.Product.Convergence
open import Cubical.Analysis.Complex.Series.Product.Absolute
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence

private
  module Power = Exponentiation ℂCommRing
  module Ring = CommRingTheory ℂCommRing

opaque
  -- This is a finite identity, with no convergence assumptions. Reuse the
  -- generic ring power and interchange laws before summing the diagonal.
  powerSeriesTermsℂ-cauchyProduct : ∀ a b z n →
    powerSeriesTermsℂ (cauchyProductℂ a b) z n ≡
    cauchyProductℂ (powerSeriesTermsℂ a z) (powerSeriesTermsℂ b z) n
  powerSeriesTermsℂ-cauchyProduct a b z n =
    sym (partialSumℂ-right-scale (λ k → a k ·ℂ b (n ∸ k)) (z ^ℂ n) (suc n))
    ∙ partialSumℂ-pointwiseBefore
        (λ k → (a k ·ℂ b (n ∸ k)) ·ℂ (z ^ℂ n))
        (λ k → (a k ·ℂ (z ^ℂ k)) ·ℂ (b (n ∸ k) ·ℂ (z ^ℂ (n ∸ k)))) (suc n)
        (λ k before → cong ((a k ·ℂ b (n ∸ k)) ·ℂ_)
          (sym (Power.·-of-^-is-^-of-+ z k (n ∸ k)
            ∙ cong (z ^ℂ_) (ℕ.+-comm k (n ∸ k) ∙ ℕ.≤-∸-+-cancel (ℕ.pred-≤-pred before))))
          ∙ Ring.·CommAssocSwap (a k) (b (n ∸ k)) (z ^ℂ k) (z ^ℂ (n ∸ k)))

-- A complex version of the native real power-series Mertens interface.
-- Only one evaluated factor needs absolute native Cauchy data.
powerSeriesCauchyProductℂHasSum : ∀ a b z x y →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ a z) →
  IsComplexCauchySeries (powerSeriesTermsℂ b z) →
  HasComplexSum (powerSeriesTermsℂ a z) x → HasComplexSum (powerSeriesTermsℂ b z) y →
  HasComplexSum (powerSeriesTermsℂ (cauchyProductℂ a b) z) (x ·ℂ y)
powerSeriesCauchyProductℂHasSum a b z x y absolute cauchy first second =
  complexHasSumPointwise (cauchyProductℂ (powerSeriesTermsℂ a z) (powerSeriesTermsℂ b z))
    (powerSeriesTermsℂ (cauchyProductℂ a b) z) (λ n → sym (powerSeriesTermsℂ-cauchyProduct a b z n)) (x ·ℂ y)
    (mertensCauchyProductℂHasSum (powerSeriesTermsℂ a z) (powerSeriesTermsℂ b z) x y absolute cauchy first second)

powerSeriesCauchyProductℂSummable : ∀ a b z →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ a z) →
  IsComplexCauchySeries (powerSeriesTermsℂ b z) → ComplexPowerSeriesSummableAt (cauchyProductℂ a b) z
powerSeriesCauchyProductℂSummable a b z absolute cauchy =
  subst ComplexSummable (sym (funExt (powerSeriesTermsℂ-cauchyProduct a b z)))
    (mertensCauchyProductℂSummable (powerSeriesTermsℂ a z) (powerSeriesTermsℂ b z) absolute cauchy)

powerSeriesCauchyProductℂAbsolutelyCauchy : ∀ a b z →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ a z) →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ b z) →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ (cauchyProductℂ a b) z)
powerSeriesCauchyProductℂAbsolutelyCauchy a b z first second =
  subst IsComplexAbsolutelyCauchySeries (sym (funExt (powerSeriesTermsℂ-cauchyProduct a b z)))
    (cauchyProductℂIsAbsolutelyCauchy (powerSeriesTermsℂ a z) (powerSeriesTermsℂ b z) first second)

-- Radius-majorant data is the common user-facing source of these witnesses.
powerSeriesCauchyProductℂAbsolutelyCauchyOn : ∀ a b radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant a radius) →
  Real.IsCauchySeries (complexPowerSeriesMajorant b radius) →
  ∀ z → normℂ z ≤ℝ radius → IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ (cauchyProductℂ a b) z)
powerSeriesCauchyProductℂAbsolutelyCauchyOn a b radius first second z bounded =
  powerSeriesCauchyProductℂAbsolutelyCauchy a b z
    (complexPowerSeriesAbsolutelyCauchyOn a radius first z bounded)
    (complexPowerSeriesAbsolutelyCauchyOn b radius second z bounded)

powerSeriesValueℂ-cauchyProduct : ∀ a b z →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ a z) →
  IsComplexCauchySeries (powerSeriesTermsℂ b z) →
  (first : ComplexPowerSeriesSummableAt a z) (second : ComplexPowerSeriesSummableAt b z)
  (product : ComplexPowerSeriesSummableAt (cauchyProductℂ a b) z) →
  powerSeriesValueℂ (cauchyProductℂ a b) z product ≡ powerSeriesValueℂ a z first ·ℂ powerSeriesValueℂ b z second
powerSeriesValueℂ-cauchyProduct a b z absolute cauchy first second product =
  complexSumUnique (powerSeriesTermsℂ (cauchyProductℂ a b) z) (fst product) (fst first ·ℂ fst second) (snd product)
    (powerSeriesCauchyProductℂHasSum a b z (fst first) (fst second) absolute cauchy (snd first) (snd second))
