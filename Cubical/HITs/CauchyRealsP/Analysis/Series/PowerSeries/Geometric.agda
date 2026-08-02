module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Geometric where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _∸_)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Convergence
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Product

unitCoefficientBound : ℚ₊
unitCoefficientBound =
  1 , ℚ.0<sucN 0

unitCoefficients : RealSequence
unitCoefficients _ =
  1

unitCoefficientsBounded :
  CoefficientAbsBound
    unitCoefficientBound
    unitCoefficients
unitCoefficientsBounded n =
  subst
    (_≤ℝ rat (fst unitCoefficientBound))
    (sym absOne)
    (≤ℝ-refl 1)

powerSeriesTerms-unitCoefficients :
  ∀ x n →
  powerSeriesTerms
      unitCoefficients x n
    ≡
  geometricTerms x n
powerSeriesTerms-unitCoefficients x n =
  mulIdL (x ^ⁿ n)

powerSeriesTerms-unitCoefficients-sequence :
  ∀ x →
  powerSeriesTerms unitCoefficients x
    ≡
  geometricTerms x
powerSeriesTerms-unitCoefficients-sequence x =
  funExt
    (powerSeriesTerms-unitCoefficients x)

unitPowerSeriesSummable :
  ∀ x →
  RationalContractionBound x →
  PowerSeriesSummableAt
    unitCoefficients x
unitPowerSeriesSummable x contraction =
  powerSeriesIsSummable
    unitCoefficientBound
    unitCoefficients x
    unitCoefficientsBounded
    contraction

powerSeriesValue-unitCoefficients :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  (summable :
    PowerSeriesSummableAt
      unitCoefficients x) →
  powerSeriesValue
      unitCoefficients x summable
    ≡
  positiveReciprocal
    (1 - x)
    (positiveSub x 1
      (rationalContractionBound→x<1
        x contraction))
powerSeriesValue-unitCoefficients
  x contraction summable =
    seriesSumIndependent
      (powerSeriesTerms
        unitCoefficients x)
      summable
      reciprocal-summable
  where
  reciprocal : ℝ
  reciprocal =
    positiveReciprocal
      (1 - x)
      (positiveSub x 1
        (rationalContractionBound→x<1
          x contraction))

  geometric-has-sum :
    HasSum
      (geometricTerms x)
      reciprocal
  geometric-has-sum =
    geometricSeriesHasSumByRationalContraction
      x contraction

  unit-has-sum :
    HasSum
      (powerSeriesTerms
        unitCoefficients x)
      reciprocal
  unit-has-sum =
    subst
      (λ terms → HasSum terms reciprocal)
      (sym
        (powerSeriesTerms-unitCoefficients-sequence
          x))
      geometric-has-sum

  reciprocal-summable :
    PowerSeriesSummableAt
      unitCoefficients x
  reciprocal-summable =
    reciprocal , unit-has-sum

linearGrowthCoefficients :
  RealSequence
linearGrowthCoefficients =
  cauchyProduct
    unitCoefficients
    unitCoefficients

partialSum-unitCoefficients :
  ∀ n →
  partialSum unitCoefficients n
    ≡
  realNatural n
partialSum-unitCoefficients zero =
  refl
partialSum-unitCoefficients (suc n) =
  cong (_+ 1)
    (partialSum-unitCoefficients n)

linearGrowthCoefficients-value :
  ∀ n →
  linearGrowthCoefficients n
    ≡
  realNatural (suc n)
linearGrowthCoefficients-value n =
  partialSum-pointwise
    (λ k →
      unitCoefficients k
        · unitCoefficients (n ∸ k))
    unitCoefficients
    (λ k → mulIdL 1)
    (suc n)
  ∙ partialSum-unitCoefficients
      (suc n)

linearGrowthPowerSeriesSummable :
  ∀ x →
  RationalContractionBound x →
  PowerSeriesSummableAt
    linearGrowthCoefficients x
linearGrowthPowerSeriesSummable
  x contraction =
    powerSeriesCauchyProductSummable
      unitCoefficientBound
      unitCoefficientBound
      unitCoefficients
      unitCoefficients
      x
      unitCoefficientsBounded
      unitCoefficientsBounded
      contraction

powerSeriesValue-linearGrowth :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  (summable :
    PowerSeriesSummableAt
      linearGrowthCoefficients x) →
  powerSeriesValue
      linearGrowthCoefficients x
      summable
    ≡
  positiveReciprocal
    (1 - x)
    (positiveSub x 1
      (rationalContractionBound→x<1
        x contraction))
  ·
  positiveReciprocal
    (1 - x)
    (positiveSub x 1
      (rationalContractionBound→x<1
        x contraction))
powerSeriesValue-linearGrowth
  x contraction summable =
    powerSeriesValue-cauchyProduct
      unitCoefficientBound
      unitCoefficientBound
      unitCoefficients
      unitCoefficients
      x
      unitCoefficientsBounded
      unitCoefficientsBounded
      contraction
      unit-summable
      unit-summable
      summable
  ∙ cong₂ _·_
      (powerSeriesValue-unitCoefficients
        x contraction unit-summable)
      (powerSeriesValue-unitCoefficients
        x contraction unit-summable)
  where
  unit-summable :
    PowerSeriesSummableAt
      unitCoefficients x
  unit-summable =
    unitPowerSeriesSummable
      x contraction
