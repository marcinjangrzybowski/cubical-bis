module Cubical.Analysis.Real.Series.PowerSeries.IteratedGeometric where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ; zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.BoundedReal
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.AbsoluteNative
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Product
open import Cubical.Analysis.Real.Series.PowerSeries.Product.Native
open import
  Cubical.Analysis.Real.Series.PowerSeries.IteratedGeometric.Coefficients


-- There are order + 1 geometric factors: order zero is the ordinary
-- geometric series and every successor adds one factor on the left.
iteratedGeometricProduct : ℕ → ℝ → ℝ
iteratedGeometricProduct zero value = value
iteratedGeometricProduct (suc order) value =
  value · iteratedGeometricProduct order value


powerSeriesTerms-iteratedGeometric-zero : ∀ x →
  powerSeriesTerms (iteratedGeometricCoefficients zero) x
    ≡ powerSeriesTerms geometricCoefficients x
powerSeriesTerms-iteratedGeometric-zero x = refl


powerSeriesTerms-iteratedGeometric-successor-pointwise :
  ∀ order x n →
  powerSeriesTerms
      (iteratedGeometricCoefficients (suc order)) x n
    ≡
  cauchyProduct
    (powerSeriesTerms geometricCoefficients x)
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
    n
powerSeriesTerms-iteratedGeometric-successor-pointwise
    order x n =
  powerSeriesTerms-cauchyProduct
    geometricCoefficients
    (iteratedGeometricCoefficients order)
    x n


powerSeriesTerms-iteratedGeometric-successor :
  ∀ order x →
  powerSeriesTerms
      (iteratedGeometricCoefficients (suc order)) x
    ≡
  cauchyProduct
    (powerSeriesTerms geometricCoefficients x)
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
powerSeriesTerms-iteratedGeometric-successor order x =
  powerSeriesTerms-cauchyProduct-sequence
    geometricCoefficients
    (iteratedGeometricCoefficients order)
    x


iteratedGeometricPowerSeriesIsAbsolutelyCauchy-zeroByRationalBound :
  ∀ x r →
  RationalContractionBound x r →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients zero) x)
iteratedGeometricPowerSeriesIsAbsolutelyCauchy-zeroByRationalBound
    x r bound =
  geometricPowerSeriesIsAbsolutelyCauchyByRationalBound
    x r bound


-- The quantitative product closure is sealed at the series layer, so this
-- induction exposes a small absolute-Cauchy family without repeatedly
-- normalizing its selected moduli and rational bounds.

opaque
  iteratedGeometricPowerSeriesIsAbsolutelyCauchyByRationalBound :
    ∀ x r →
    RationalContractionBound x r →
    ∀ order →
    IsAbsolutelyCauchySeries
      (powerSeriesTerms
        (iteratedGeometricCoefficients order) x)
  iteratedGeometricPowerSeriesIsAbsolutelyCauchyByRationalBound
      x r bound zero =
    iteratedGeometricPowerSeriesIsAbsolutelyCauchy-zeroByRationalBound
      x r bound
  iteratedGeometricPowerSeriesIsAbsolutelyCauchyByRationalBound
      x r bound (suc order) =
    subst
      IsAbsolutelyCauchySeries
      (sym
        (powerSeriesTerms-iteratedGeometric-successor order x))
      (nativeCauchyProductIsAbsolutelyCauchy-sealed
        (powerSeriesTerms geometricCoefficients x)
        (powerSeriesTerms
          (iteratedGeometricCoefficients order) x)
        (geometricPowerSeriesIsAbsolutelyCauchyByRationalBound
          x r bound)
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchyByRationalBound
          x r bound order))


iteratedGeometricPowerSeriesIsCauchy-zeroByRationalBound :
  ∀ x r →
  RationalContractionBound x r →
  IsCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients zero) x)
iteratedGeometricPowerSeriesIsCauchy-zeroByRationalBound
    x r bound =
  geometricPowerSeriesIsCauchyByRationalBound x r bound


iteratedGeometricPowerSeriesSummable-successorByRationalBound :
  ∀ x r →
  (bound : RationalContractionBound x r) →
  ∀ order →
  IsCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x) →
  PowerSeriesSummableAt
    (iteratedGeometricCoefficients (suc order)) x
iteratedGeometricPowerSeriesSummable-successorByRationalBound
    x r bound order previousCauchy =
  powerSeriesNativeCauchyProductSummable
    geometricCoefficients
    (iteratedGeometricCoefficients order)
    x
    (geometricPowerSeriesIsAbsolutelyCauchyByRationalBound
      x r bound)
    previousCauchy


-- This is the exact native Mertens induction step.  Its previous-order
-- Cauchy witness is explicit: ordinary summability cannot construct such a
-- witness without an additional choice principle.
iteratedGeometricPowerSeriesHasSum-successorByRationalBound :
  ∀ x r →
  (bound : RationalContractionBound x r) →
  ∀ order previousValue →
  IsCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x) →
  HasSum
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
    previousValue →
  HasSum
    (powerSeriesTerms
      (iteratedGeometricCoefficients (suc order)) x)
    ( positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)
    · previousValue
    )
iteratedGeometricPowerSeriesHasSum-successorByRationalBound
    x r bound order previousValue
    previousCauchy previousHasSum =
  powerSeriesNativeCauchyProductHasSum
    geometricCoefficients
    (iteratedGeometricCoefficients order)
    x reciprocal previousValue
    (geometricPowerSeriesIsAbsolutelyCauchyByRationalBound
      x r bound)
    previousCauchy
    (geometricPowerSeriesHasSumByRationalBound x r bound)
    previousHasSum
  where
  reciprocal : ℝ
  reciprocal =
    positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound)


-- A family of native absolute-Cauchy witnesses is deliberately kept
-- separate from ordinary summability.  It is a reusable input to the native
-- Mertens induction; the quantitative product closure constructs it below
-- from a rational contraction bound.
IteratedGeometricAbsoluteFamily : ℝ → Type₀
IteratedGeometricAbsoluteFamily x =
  ∀ order →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)


iteratedGeometricPowerSeriesIsCauchyByAbsoluteFamily : ∀ x →
  IteratedGeometricAbsoluteFamily x →
  ∀ order →
  IsCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
iteratedGeometricPowerSeriesIsCauchyByAbsoluteFamily
    x absolute order =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
    (absolute order)


iteratedGeometricPowerSeriesSummableByAbsoluteFamily : ∀ x →
  IteratedGeometricAbsoluteFamily x →
  ∀ order →
  PowerSeriesSummableAt
    (iteratedGeometricCoefficients order) x
iteratedGeometricPowerSeriesSummableByAbsoluteFamily
    x absolute order =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
    (absolute order)


iteratedGeometricPowerSeriesHasSumByAbsoluteFamily : ∀ x r →
  (bound : RationalContractionBound x r) →
  IteratedGeometricAbsoluteFamily x →
  ∀ order →
  HasSum
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
    (iteratedGeometricProduct order
      (positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)))
iteratedGeometricPowerSeriesHasSumByAbsoluteFamily
    x r bound absolute zero =
  geometricPowerSeriesHasSumByRationalBound x r bound
iteratedGeometricPowerSeriesHasSumByAbsoluteFamily
    x r bound absolute (suc order) =
  iteratedGeometricPowerSeriesHasSum-successorByRationalBound
    x r bound order (iteratedGeometricProduct order reciprocal)
    (iteratedGeometricPowerSeriesIsCauchyByAbsoluteFamily
      x absolute order)
    (iteratedGeometricPowerSeriesHasSumByAbsoluteFamily
      x r bound absolute order)
  where
  reciprocal : ℝ
  reciprocal =
    positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound)


powerSeriesValue-iteratedGeometricByAbsoluteFamily : ∀ x r →
  (bound : RationalContractionBound x r) →
  (absolute : IteratedGeometricAbsoluteFamily x) →
  ∀ order →
  (summable : PowerSeriesSummableAt
    (iteratedGeometricCoefficients order) x) →
  powerSeriesValue
      (iteratedGeometricCoefficients order) x summable
    ≡
  iteratedGeometricProduct order
    (positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound))
powerSeriesValue-iteratedGeometricByAbsoluteFamily
    x r bound absolute order summable =
  seriesSumIndependent
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
    summable
    ( iteratedGeometricProduct order reciprocal
    , iteratedGeometricPowerSeriesHasSumByAbsoluteFamily
        x r bound absolute order
    )
  where
  reciprocal : ℝ
  reciprocal =
    positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound)


iteratedGeometricAbsoluteFamilyByRationalBound : ∀ x r →
  RationalContractionBound x r →
  IteratedGeometricAbsoluteFamily x
iteratedGeometricAbsoluteFamilyByRationalBound
  x r bound order =
  iteratedGeometricPowerSeriesIsAbsolutelyCauchyByRationalBound
    x r bound order


iteratedGeometricPowerSeriesIsCauchyByRationalBound :
  ∀ x r →
  RationalContractionBound x r →
  ∀ order →
  IsCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
iteratedGeometricPowerSeriesIsCauchyByRationalBound
  x r bound =
  iteratedGeometricPowerSeriesIsCauchyByAbsoluteFamily
    x
    (iteratedGeometricAbsoluteFamilyByRationalBound x r bound)


iteratedGeometricPowerSeriesSummableByRationalBound :
  ∀ x r →
  RationalContractionBound x r →
  ∀ order →
  PowerSeriesSummableAt
    (iteratedGeometricCoefficients order) x
iteratedGeometricPowerSeriesSummableByRationalBound
  x r bound =
  iteratedGeometricPowerSeriesSummableByAbsoluteFamily
    x
    (iteratedGeometricAbsoluteFamilyByRationalBound x r bound)


iteratedGeometricPowerSeriesHasSumByRationalBound :
  ∀ x r →
  (bound : RationalContractionBound x r) →
  ∀ order →
  HasSum
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
    (iteratedGeometricProduct order
      (positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)))
iteratedGeometricPowerSeriesHasSumByRationalBound
  x r bound =
  iteratedGeometricPowerSeriesHasSumByAbsoluteFamily
    x r bound
    (iteratedGeometricAbsoluteFamilyByRationalBound x r bound)


powerSeriesValue-iteratedGeometricByRationalBound :
  ∀ x r →
  (bound : RationalContractionBound x r) →
  ∀ order →
  (summable :
    PowerSeriesSummableAt
      (iteratedGeometricCoefficients order) x) →
  powerSeriesValue
      (iteratedGeometricCoefficients order) x summable
    ≡
  iteratedGeometricProduct order
    (positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound))
powerSeriesValue-iteratedGeometricByRationalBound
  x r bound =
  powerSeriesValue-iteratedGeometricByAbsoluteFamily
    x r bound
    (iteratedGeometricAbsoluteFamilyByRationalBound x r bound)
