module Cubical.Analysis.Real.Series.PowerSeries.Geometric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
  using (zero; suc; _∸_)
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.BoundedReal
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Product
open import Cubical.Analysis.Real.Series.PowerSeries.Product.Native


-- The geometric series is the power series with every coefficient equal to
-- one.  Naming the coefficients makes subsequent transports state the power
-- series side explicitly.
geometricCoefficients : RealSequence
geometricCoefficients _ = 1ℝ


powerSeriesTerms-geometric-pointwise : ∀ x n →
  powerSeriesTerms geometricCoefficients x n
    ≡ geometricTerms x n
powerSeriesTerms-geometric-pointwise x n =
  mulIdL (geometricTerms x n)


powerSeriesTerms-geometric : ∀ x →
  powerSeriesTerms geometricCoefficients x
    ≡ geometricTerms x
powerSeriesTerms-geometric x =
  funExt (powerSeriesTerms-geometric-pointwise x)


geometricPowerSeriesIsCauchyByRationalBound : ∀ x r →
  RationalContractionBound x r →
  IsCauchySeries (powerSeriesTerms geometricCoefficients x)
geometricPowerSeriesIsCauchyByRationalBound x r bound =
  subst IsCauchySeries
    (sym (powerSeriesTerms-geometric x))
    (realGeometricSeriesIsCauchyByRationalBound x r bound)


geometricPowerSeriesSummableByRationalBound : ∀ x r →
  RationalContractionBound x r →
  PowerSeriesSummableAt geometricCoefficients x
geometricPowerSeriesSummableByRationalBound x r bound =
  subst Summable
    (sym (powerSeriesTerms-geometric x))
    (realGeometricSeriesSummableByRationalBound x r bound)


geometricPowerSeriesHasSumByRationalBound : ∀ x r →
  (bound : RationalContractionBound x r) →
  HasSum (powerSeriesTerms geometricCoefficients x)
    (positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound))
geometricPowerSeriesHasSumByRationalBound x r bound =
  subst
    (λ terms → HasSum terms
      (positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)))
    (sym (powerSeriesTerms-geometric x))
    (realGeometricSeriesHasSumByRationalBound x r bound)


powerSeriesValue-geometricByRationalBound : ∀ x r →
  (bound : RationalContractionBound x r) →
  (summable : PowerSeriesSummableAt geometricCoefficients x) →
  powerSeriesValue geometricCoefficients x summable
    ≡
  positiveReciprocal (1ℝ - x)
    (realGeometricPositiveDenominatorByRationalBound
      x r bound)
powerSeriesValue-geometricByRationalBound x r bound summable =
  seriesSumIndependent
    (powerSeriesTerms geometricCoefficients x)
    summable
    ( positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)
    , geometricPowerSeriesHasSumByRationalBound x r bound
    )


-- Absolute convergence uses the same rational majorant: taking absolute
-- values merely replaces the centre x by |x| in the geometric terms.
geometricPowerSeriesIsAbsolutelyCauchyByRationalBound : ∀ x r →
  RationalContractionBound x r →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms geometricCoefficients x)
geometricPowerSeriesIsAbsolutelyCauchyByRationalBound
    x r (absx≤r , absr<1) =
  subst IsCauchySeries
    (sym absoluteTermsPath)
    (realGeometricSeriesIsCauchyByRationalBound
      (absℝ x) r
      ( subst (_≤ℝ rat r)
          (sym (absIdem x)) absx≤r
      , absr<1
      ))
  where
  absoluteTermsPath :
    (absℝ ∘ powerSeriesTerms geometricCoefficients x)
      ≡ geometricTerms (absℝ x)
  absoluteTermsPath =
    funExt λ n →
      cong absℝ
        (powerSeriesTerms-geometric-pointwise x n)
      ∙ absPow x n


-- The coefficients n + 1 arise as the diagonal convolution of two copies
-- of the constant-one coefficient sequence.
linearGrowthCoefficients : RealSequence
linearGrowthCoefficients =
  cauchyProduct geometricCoefficients geometricCoefficients


partialSum-geometricCoefficients : ∀ n →
  partialSum geometricCoefficients n ≡ realNatural n
partialSum-geometricCoefficients zero = refl
partialSum-geometricCoefficients (suc n) =
  cong (_+ 1ℝ) (partialSum-geometricCoefficients n)
  ∙ sym (realNatural-suc n)


linearGrowthCoefficients-value : ∀ n →
  linearGrowthCoefficients n ≡ realNatural (suc n)
linearGrowthCoefficients-value n =
  partialSum-pointwise
    (λ k →
      geometricCoefficients k ·
      geometricCoefficients (n ∸ k))
    geometricCoefficients
    (λ k → mulIdL 1ℝ)
    (suc n)
  ∙ partialSum-geometricCoefficients (suc n)


powerSeriesTerms-linearGrowth-value : ∀ x n →
  powerSeriesTerms linearGrowthCoefficients x n
    ≡ realNatural (suc n) · geometricTerms x n
powerSeriesTerms-linearGrowth-value x n =
  cong (_· geometricTerms x n)
    (linearGrowthCoefficients-value n)


powerSeriesTerms-linearGrowth-cauchyProduct : ∀ x n →
  powerSeriesTerms linearGrowthCoefficients x n
    ≡
  cauchyProduct
    (powerSeriesTerms geometricCoefficients x)
    (powerSeriesTerms geometricCoefficients x) n
powerSeriesTerms-linearGrowth-cauchyProduct x n =
  powerSeriesTerms-cauchyProduct
    geometricCoefficients geometricCoefficients x n


powerSeriesTerms-linearGrowth-cauchyProduct-sequence : ∀ x →
  powerSeriesTerms linearGrowthCoefficients x
    ≡
  cauchyProduct
    (powerSeriesTerms geometricCoefficients x)
    (powerSeriesTerms geometricCoefficients x)
powerSeriesTerms-linearGrowth-cauchyProduct-sequence x =
  powerSeriesTerms-cauchyProduct-sequence
    geometricCoefficients geometricCoefficients x


linearGrowthPowerSeriesSummableByRationalBound : ∀ x r →
  RationalContractionBound x r →
  PowerSeriesSummableAt linearGrowthCoefficients x
linearGrowthPowerSeriesSummableByRationalBound x r bound =
  powerSeriesNativeCauchyProductSummable
    geometricCoefficients geometricCoefficients x
    (geometricPowerSeriesIsAbsolutelyCauchyByRationalBound
      x r bound)
    (geometricPowerSeriesIsCauchyByRationalBound x r bound)


linearGrowthPowerSeriesHasSumByRationalBound : ∀ x r →
  (bound : RationalContractionBound x r) →
  HasSum (powerSeriesTerms linearGrowthCoefficients x)
    ( positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)
    · positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)
    )
linearGrowthPowerSeriesHasSumByRationalBound x r bound =
  powerSeriesNativeCauchyProductHasSum
    geometricCoefficients geometricCoefficients x
    reciprocal reciprocal
    (geometricPowerSeriesIsAbsolutelyCauchyByRationalBound
      x r bound)
    (geometricPowerSeriesIsCauchyByRationalBound x r bound)
    (geometricPowerSeriesHasSumByRationalBound x r bound)
    (geometricPowerSeriesHasSumByRationalBound x r bound)
  where
  reciprocal : ℝ
  reciprocal =
    positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound)


powerSeriesValue-linearGrowthByRationalBound : ∀ x r →
  (bound : RationalContractionBound x r) →
  (summable : PowerSeriesSummableAt linearGrowthCoefficients x) →
  powerSeriesValue linearGrowthCoefficients x summable
    ≡
  positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound)
    ·
  positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound)
powerSeriesValue-linearGrowthByRationalBound
    x r bound summable =
  seriesSumIndependent
    (powerSeriesTerms linearGrowthCoefficients x)
    summable
    ( reciprocal · reciprocal
    , linearGrowthPowerSeriesHasSumByRationalBound
        x r bound
    )
  where
  reciprocal : ℝ
  reciprocal =
    positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound)
