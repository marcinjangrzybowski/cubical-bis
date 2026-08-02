module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Mertens
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Convolution
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Product
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.AbsoluteProduct
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Geometric

unitPowerSeriesIsAbsolutelyCauchy :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      unitCoefficients x)
unitPowerSeriesIsAbsolutelyCauchy
  x contraction =
    subst
      IsAbsolutelyCauchySeries
      (sym
        (powerSeriesTerms-unitCoefficients-sequence
          x))
      (geometricAbsoluteCauchy
        x contraction)

unitPowerSeriesAbsoluteSumBound :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  AbsoluteCauchySeriesSumBound
    (geometricContractionSumBound
      x contraction)
    (powerSeriesTerms
      unitCoefficients x)
    (unitPowerSeriesIsAbsolutelyCauchy
      x contraction)
unitPowerSeriesAbsoluteSumBound
  x contraction =
    absoluteCauchySeriesSumBoundPresPath
      (geometricContractionSumBound
        x contraction)
      (sym
        (powerSeriesTerms-unitCoefficients-sequence
          x))
      (geometricAbsoluteCauchy
        x contraction)
      (unitPowerSeriesIsAbsolutelyCauchy
        x contraction)
      (geometricAbsoluteSeriesSumBound
        x contraction)

opaque
  unitPowerSeriesAbsoluteData :
    ∀ x →
    (contraction :
      RationalContractionBound x) →
    PowerSeriesAbsoluteWithBound
      (geometricContractionSumBound
        x contraction)
      unitCoefficients x
  unitPowerSeriesAbsoluteData
    x contraction =
      unitPowerSeriesIsAbsolutelyCauchy
        x contraction
      ,
      unitPowerSeriesAbsoluteSumBound
        x contraction

iteratedGeometricCoefficients :
  ℕ → RealSequence
iteratedGeometricCoefficients zero =
  unitCoefficients
iteratedGeometricCoefficients (suc order) =
  cauchyProduct
    unitCoefficients
    (iteratedGeometricCoefficients order)

iteratedGeometricCoefficients-one :
  iteratedGeometricCoefficients (suc zero)
    ≡
  linearGrowthCoefficients
iteratedGeometricCoefficients-one =
  refl

iteratedGeometricSumBound :
  ∀ x →
  RationalContractionBound x →
  ℕ → ℚ₊
iteratedGeometricSumBound
  x contraction zero =
    geometricContractionSumBound
      x contraction
iteratedGeometricSumBound
  x contraction (suc order) =
    geometricContractionSumBound
      x contraction
    ·₊
    iteratedGeometricSumBound
      x contraction order

opaque
  iteratedGeometricPowerSeriesAbsoluteData :
    ∀ x →
    (contraction :
      RationalContractionBound x) →
    ∀ order →
    PowerSeriesAbsoluteWithBound
      (iteratedGeometricSumBound
        x contraction order)
      (iteratedGeometricCoefficients
        order)
      x
  iteratedGeometricPowerSeriesAbsoluteData
    x contraction zero =
      unitPowerSeriesAbsoluteData
        x contraction
  iteratedGeometricPowerSeriesAbsoluteData
    x contraction (suc order) =
      powerSeriesCauchyProductWithBound
        (geometricContractionSumBound
          x contraction)
        (iteratedGeometricSumBound
          x contraction order)
        unitCoefficients
        (iteratedGeometricCoefficients
          order)
        x
        (unitPowerSeriesAbsoluteData
          x contraction)
        (iteratedGeometricPowerSeriesAbsoluteData
          x contraction order)

iteratedGeometricPowerSeriesIsAbsolutelyCauchy :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  ∀ order →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients
        order)
      x)
iteratedGeometricPowerSeriesIsAbsolutelyCauchy
  x contraction order =
    fst
      (iteratedGeometricPowerSeriesAbsoluteData
        x contraction order)

iteratedGeometricPowerSeriesAbsoluteSumBound :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  ∀ order →
  AbsoluteCauchySeriesSumBound
    (iteratedGeometricSumBound
      x contraction order)
    (powerSeriesTerms
      (iteratedGeometricCoefficients
        order)
      x)
    (iteratedGeometricPowerSeriesIsAbsolutelyCauchy
      x contraction order)
iteratedGeometricPowerSeriesAbsoluteSumBound
  x contraction order =
    snd
      (iteratedGeometricPowerSeriesAbsoluteData
        x contraction order)

iteratedGeometricPowerSeriesSummable :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  ∀ order →
  PowerSeriesSummableAt
    (iteratedGeometricCoefficients
      order)
    x
iteratedGeometricPowerSeriesSummable
  x contraction order =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms
        (iteratedGeometricCoefficients
          order)
        x)
      (iteratedGeometricPowerSeriesIsAbsolutelyCauchy
        x contraction order)

iteratedProduct :
  ℕ → ℝ → ℝ
iteratedProduct zero value =
  value
iteratedProduct (suc order) value =
  value · iteratedProduct order value

iteratedGeometricPowerSeriesValue :
  ∀ x →
  (contraction :
    RationalContractionBound x) →
  ∀ order →
  (summable :
    PowerSeriesSummableAt
      (iteratedGeometricCoefficients
        order)
      x) →
  powerSeriesValue
      (iteratedGeometricCoefficients
        order)
      x summable
    ≡
  iteratedProduct order
    (positiveReciprocal
      (1 - x)
      (positiveSub x 1
        (rationalContractionBound→x<1
          x contraction)))
iteratedGeometricPowerSeriesValue
  x contraction zero summable =
    powerSeriesValue-unitCoefficients
      x contraction summable
iteratedGeometricPowerSeriesValue
  x contraction (suc order)
  summable =
    powerSeriesValue-cauchyProductWithBound
      (geometricContractionSumBound
        x contraction)
      (iteratedGeometricSumBound
        x contraction order)
      unitCoefficients
      (iteratedGeometricCoefficients
        order)
      x
      (unitPowerSeriesAbsoluteData
        x contraction)
      (iteratedGeometricPowerSeriesAbsoluteData
        x contraction order)
      unit-summable
      previous-summable
      summable
    ∙ cong₂ _·_
        (powerSeriesValue-unitCoefficients
          x contraction unit-summable)
        (iteratedGeometricPowerSeriesValue
          x contraction order
          previous-summable)
  where
  unit-summable :
    PowerSeriesSummableAt
      unitCoefficients x
  unit-summable =
    unitPowerSeriesSummable
      x contraction

  previous-summable :
    PowerSeriesSummableAt
      (iteratedGeometricCoefficients
        order)
      x
  previous-summable =
    iteratedGeometricPowerSeriesSummable
      x contraction order
