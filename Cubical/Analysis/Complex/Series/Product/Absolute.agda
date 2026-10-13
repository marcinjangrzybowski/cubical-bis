module Cubical.Analysis.Complex.Series.Product.Absolute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (suc; _∸_)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence.Eventually using (pointwiseLePresLimits)
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Bounds as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.Product.Finite as Real
import Cubical.Analysis.Real.Series.Product.Native as Real
import Cubical.Analysis.Real.Series.Product.AbsoluteNative as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Bounds
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.Product.Finite

-- The l1 norm is submultiplicative, which is sufficient here. The majorant
-- is exactly the existing real convolution of the two nonnegative norms.
opaque
  cauchyProductℂNormBound : ∀ a b n → normℂ (cauchyProductℂ a b n) ≤ℝ
    Real.cauchyProduct (normℂ ∘ a) (normℂ ∘ b) n
  cauchyProductℂNormBound a b n = partialSumℂBoundBy
    (λ k → a k ·ℂ b (n ∸ k)) (λ k → normℂ (a k) · normℂ (b (n ∸ k)))
    (λ k → normℂ-submultiplicative (a k) (b (n ∸ k))) (suc n)

  cauchyProductℂNormMajorantIsCauchy : ∀ a b →
    IsComplexAbsolutelyCauchySeries a → IsComplexAbsolutelyCauchySeries b →
    Real.IsCauchySeries (Real.cauchyProduct (normℂ ∘ a) (normℂ ∘ b))
  cauchyProductℂNormMajorantIsCauchy a b first second =
    Real.absoluteCauchySeriesIsCauchy (Real.cauchyProduct (normℂ ∘ a) (normℂ ∘ b))
      (Real.nativeCauchyProductIsAbsolutelyCauchy-sealed (normℂ ∘ a) (normℂ ∘ b)
        (complexNormSeriesIsAbsolutelyCauchy a first) (complexNormSeriesIsAbsolutelyCauchy b second))

cauchyProductℂIsAbsolutelyCauchy : ∀ a b →
  IsComplexAbsolutelyCauchySeries a → IsComplexAbsolutelyCauchySeries b →
  IsComplexAbsolutelyCauchySeries (cauchyProductℂ a b)
cauchyProductℂIsAbsolutelyCauchy a b first second =
  dominatedComplexSeriesIsAbsolutelyCauchy (cauchyProductℂ a b)
    (Real.cauchyProduct (normℂ ∘ a) (normℂ ∘ b)) (cauchyProductℂNormBound a b)
    (cauchyProductℂNormMajorantIsCauchy a b first second)

cauchyProductℂIsCauchy : ∀ a b →
  IsComplexAbsolutelyCauchySeries a → IsComplexAbsolutelyCauchySeries b →
  IsComplexCauchySeries (cauchyProductℂ a b)
cauchyProductℂIsCauchy a b first second = absoluteComplexCauchySeriesIsCauchy (cauchyProductℂ a b)
  (cauchyProductℂIsAbsolutelyCauchy a b first second)

-- The sum of the norms of the product is bounded by the product of the
-- sums of the norms. All three displayed sums may be supplied independently.
opaque
  cauchyProductℂAbsoluteSumBound : ∀ a b →
    IsComplexAbsolutelyCauchySeries a → IsComplexAbsolutelyCauchySeries b →
    (first : ComplexAbsolutelySummable a) (second : ComplexAbsolutelySummable b)
    (product : ComplexAbsolutelySummable (cauchyProductℂ a b)) →
    Real.seriesSum (normℂ ∘ cauchyProductℂ a b) product ≤ℝ
      Real.seriesSum (normℂ ∘ a) first · Real.seriesSum (normℂ ∘ b) second
  cauchyProductℂAbsoluteSumBound a b aAbsolute bAbsolute first second product =
    pointwiseLePresLimits
      (Real.partialSumMono (normℂ ∘ cauchyProductℂ a b)
        (Real.cauchyProduct (normℂ ∘ a) (normℂ ∘ b)) (cauchyProductℂNormBound a b))
      (snd product)
      (Real.nativeMertensCauchyProductHasSum (normℂ ∘ a) (normℂ ∘ b) (fst first) (fst second)
        (complexNormSeriesIsAbsolutelyCauchy a aAbsolute) bAbsolute (snd first) (snd second))
