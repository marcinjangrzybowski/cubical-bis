module Cubical.Analysis.Complex.Series.PowerSeries.Product.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ; absMul)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absOfNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication using (mulPres≤R-0≤)
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.Product.Finite as Real
import Cubical.Analysis.Real.Series.Product.AbsoluteNative as Real
import Cubical.Analysis.Real.Series.PowerSeries.Product as Real
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.Product.Finite
open import Cubical.Analysis.Complex.Series.Product.Absolute
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds

opaque
  complexPowerSeriesMajorantAbs : ∀ coefficients radius → 0ℝ ≤ℝ radius → ∀ n →
    absℝ (complexPowerSeriesMajorant coefficients radius n) ≡ complexPowerSeriesMajorant coefficients radius n
  complexPowerSeriesMajorantAbs coefficients radius nonnegative n =
    absMul (normℂ (coefficients n)) (powℝ radius n)
    ∙ cong₂ _·_ (absOfNonnegative (normℂ (coefficients n)) (normℂ-nonnegative (coefficients n)))
      (absOfNonnegative (powℝ radius n) (powNonnegative radius n nonnegative))

complexPowerSeriesMajorantIsAbsolutelyCauchy : ∀ coefficients radius → 0ℝ ≤ℝ radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius) →
  Real.IsAbsolutelyCauchySeries (complexPowerSeriesMajorant coefficients radius)
complexPowerSeriesMajorantIsAbsolutelyCauchy coefficients radius nonnegative =
  subst Real.IsCauchySeries (sym (funExt (complexPowerSeriesMajorantAbs coefficients radius nonnegative)))

opaque
  -- The coefficient-product majorant is bounded by the real Cauchy product
  -- of the original majorants, at the same radius (no radius loss).
  complexPowerSeriesProductMajorantBound : ∀ a b radius → 0ℝ ≤ℝ radius → ∀ n →
    complexPowerSeriesMajorant (cauchyProductℂ a b) radius n ≤ℝ
      Real.cauchyProduct (complexPowerSeriesMajorant a radius) (complexPowerSeriesMajorant b radius) n
  complexPowerSeriesProductMajorantBound a b radius nonnegative n =
    subst (complexPowerSeriesMajorant (cauchyProductℂ a b) radius n ≤ℝ_)
      (Real.powerSeriesTerms-cauchyProduct (normℂ ∘ a) (normℂ ∘ b) radius n)
      (mulPres≤R-0≤ (normℂ (cauchyProductℂ a b n))
        (Real.cauchyProduct (normℂ ∘ a) (normℂ ∘ b) n) (powℝ radius n)
        (powNonnegative radius n nonnegative) (cauchyProductℂNormBound a b n))

  -- Preserve the stronger radius hypothesis itself. The existing uniform
  -- convergence and continuity API can then be applied to the product.
  complexPowerSeriesProductMajorantIsCauchy : ∀ a b radius → 0ℝ ≤ℝ radius →
    Real.IsCauchySeries (complexPowerSeriesMajorant a radius) →
    Real.IsCauchySeries (complexPowerSeriesMajorant b radius) →
    Real.IsCauchySeries (complexPowerSeriesMajorant (cauchyProductℂ a b) radius)
  complexPowerSeriesProductMajorantIsCauchy a b radius nonnegative first second =
    Real.dominatedCauchySeriesIsCauchy (complexPowerSeriesMajorant (cauchyProductℂ a b) radius)
      (Real.cauchyProduct (complexPowerSeriesMajorant a radius) (complexPowerSeriesMajorant b radius))
      (λ n → subst
        (_≤ℝ Real.cauchyProduct (complexPowerSeriesMajorant a radius) (complexPowerSeriesMajorant b radius) n)
        (sym (complexPowerSeriesMajorantAbs (cauchyProductℂ a b) radius nonnegative n))
        (complexPowerSeriesProductMajorantBound a b radius nonnegative n))
      (Real.absoluteCauchySeriesIsCauchy
        (Real.cauchyProduct (complexPowerSeriesMajorant a radius) (complexPowerSeriesMajorant b radius))
        (Real.nativeCauchyProductIsAbsolutelyCauchy-sealed
          (complexPowerSeriesMajorant a radius) (complexPowerSeriesMajorant b radius)
          (complexPowerSeriesMajorantIsAbsolutelyCauchy a radius nonnegative first)
          (complexPowerSeriesMajorantIsAbsolutelyCauchy b radius nonnegative second)))
