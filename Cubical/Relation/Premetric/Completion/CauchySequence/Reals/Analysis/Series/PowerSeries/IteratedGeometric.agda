module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionAbsolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Geometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LinearGrowth


private
  absContraction→value<1 : ∀ value →
    Abs.absℝ value <ℝ Real.ιℚ 1 →
    value <ℝ Real.ιℚ 1
  absContraction→value<1 value abs-value<1 =
    ≤<ℝ-trans value (Abs.absℝ value) (Real.ιℚ 1)
      (x≤abs value) abs-value<1

  absContractionPowersTendToZero : ∀ value →
    Abs.absℝ value <ℝ Real.ιℚ 1 →
    GeometricPowersTendToZero value
  absContractionPowersTendToZero value abs-value<1 =
    summableTermsTendToZero
      (geometricTerms value)
      (geometricSeriesIsSummableOfAbs<1 value abs-value<1)


-- Repeated Cauchy products of the unit coefficient sequence.  Order zero
-- represents one geometric factor; each successor adds one more factor.

iteratedGeometricCoefficients : ℕ → RealSequence
iteratedGeometricCoefficients zero =
  unitCoefficients
iteratedGeometricCoefficients (suc order) =
  cauchyProduct
    unitCoefficients
    (iteratedGeometricCoefficients order)


iteratedGeometricCoefficients-one :
  iteratedGeometricCoefficients (suc zero) ≡
  linearGrowthCoefficients
iteratedGeometricCoefficients-one =
  funExt cauchyProduct-unitCoefficients


-- The native Cauchy-sequence implementation can iterate Mertens directly
-- from absolute convergence.  In contrast with the bound-indexed version,
-- no sequence of selected rational bounds is carried through the recursion.

unitPowerSeriesIsAbsolutelyCauchyOfAbs<1 : ∀ x →
  Abs.absℝ x <ℝ Real.ιℚ 1 →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms unitCoefficients x)
unitPowerSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1 =
  subst
    IsAbsolutelyCauchySeries
    (sym (powerSeriesTerms-unitCoefficients-sequence x))
    (geometricSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1)


iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1 :
  ∀ x →
  Abs.absℝ x <ℝ Real.ιℚ 1 →
  ∀ order →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1
  x absx<1 zero =
    unitPowerSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1
iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1
  x absx<1 (suc order) =
    subst
      IsAbsolutelyCauchySeries
      (sym
        (powerSeriesTerms-cauchyProduct-sequence
          unitCoefficients
          (iteratedGeometricCoefficients order)
          x))
      (absoluteMertensCauchyProductIsAbsolutelyCauchy-sealed
        (powerSeriesTerms unitCoefficients x)
        (powerSeriesTerms
          (iteratedGeometricCoefficients order) x)
        (unitPowerSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1)
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1
          x absx<1 order))


iteratedGeometricPowerSeriesIsAbsolutelyCauchy :
  ∀ x →
  RationalContractionBound x →
  ∀ order →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (iteratedGeometricCoefficients order) x)
iteratedGeometricPowerSeriesIsAbsolutelyCauchy
  x contraction order =
    iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1
      x (rationalContractionBound→abs<1 x contraction) order


iteratedGeometricPowerSeriesSummableOfAbs<1 :
  ∀ x →
  Abs.absℝ x <ℝ Real.ιℚ 1 →
  ∀ order →
  PowerSeriesSummableAt
    (iteratedGeometricCoefficients order) x
iteratedGeometricPowerSeriesSummableOfAbs<1
  x absx<1 order =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms
        (iteratedGeometricCoefficients order) x)
      (iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1
        x absx<1 order)


iteratedGeometricPowerSeriesSummable :
  ∀ x →
  RationalContractionBound x →
  ∀ order →
  PowerSeriesSummableAt
    (iteratedGeometricCoefficients order) x
iteratedGeometricPowerSeriesSummable
  x contraction order =
    iteratedGeometricPowerSeriesSummableOfAbs<1
      x (rationalContractionBound→abs<1 x contraction) order


iteratedProduct : ℕ → Real.ℝ → Real.ℝ
iteratedProduct zero value =
  value
iteratedProduct (suc order) value =
  value Mul.· iteratedProduct order value


iteratedGeometricPowerSeriesValueOfAbs<1 :
  ∀ x →
  (absx<1 : Abs.absℝ x <ℝ Real.ιℚ 1) →
  ∀ order →
  (summable :
    PowerSeriesSummableAt
      (iteratedGeometricCoefficients order) x) →
  powerSeriesValue
      (iteratedGeometricCoefficients order) x summable
    ≡
  iteratedProduct order
    (geometricReciprocal x
      (absContraction→value<1 x absx<1))
iteratedGeometricPowerSeriesValueOfAbs<1
  x absx<1 zero summable =
    powerSeriesValue-unitCoefficients
      x
      (absContraction→value<1 x absx<1)
      (absContractionPowersTendToZero x absx<1)
      summable
iteratedGeometricPowerSeriesValueOfAbs<1
  x absx<1 (suc order) summable =
    powerSeriesValue-cauchyProductByApproximation
      unitCoefficients
      (iteratedGeometricCoefficients order)
      x unit-summable previous-summable summable approximation
  ∙ cong₂ Mul._·_
      (powerSeriesValue-unitCoefficients
        x
        (absContraction→value<1 x absx<1)
        (absContractionPowersTendToZero x absx<1)
        unit-summable)
      (iteratedGeometricPowerSeriesValueOfAbs<1
        x absx<1 order previous-summable)
  where
  unit-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms unitCoefficients x)
  unit-absolute =
    unitPowerSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1

  previous-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms
        (iteratedGeometricCoefficients order) x)
  previous-absolute =
    iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1
      x absx<1 order

  unit-summable :
    PowerSeriesSummableAt unitCoefficients x
  unit-summable =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms unitCoefficients x)
      unit-absolute

  previous-summable :
    PowerSeriesSummableAt
      (iteratedGeometricCoefficients order) x
  previous-summable =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms
        (iteratedGeometricCoefficients order) x)
      previous-absolute

  approximation :
    PowerSeriesProductRectangularApproximation
      unitCoefficients
      (iteratedGeometricCoefficients order)
      x
  approximation =
    absoluteMertensRectangularApproximation-sealed
      (powerSeriesTerms unitCoefficients x)
      (powerSeriesTerms
        (iteratedGeometricCoefficients order) x)
      unit-absolute previous-absolute


iteratedGeometricPowerSeriesValue :
  ∀ x →
  (contraction : RationalContractionBound x) →
  ∀ order →
  (summable :
    PowerSeriesSummableAt
      (iteratedGeometricCoefficients order) x) →
  powerSeriesValue
      (iteratedGeometricCoefficients order) x summable
    ≡
  iteratedProduct order
    (geometricReciprocal x
      (rationalContractionBound→x<1 x contraction))
iteratedGeometricPowerSeriesValue
  x contraction order summable =
    iteratedGeometricPowerSeriesValueOfAbs<1
      x (rationalContractionBound→abs<1 x contraction)
      order summable


-- Downstream uniform arguments only need these proofs extensionally.  Seal
-- the recursive Mertens constructions to prevent repeated normalization of
-- the entire induction during later derivative transports.

opaque
  iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed :
    ∀ x →
    Abs.absℝ x <ℝ Real.ιℚ 1 →
    ∀ order →
    IsAbsolutelyCauchySeries
      (powerSeriesTerms
        (iteratedGeometricCoefficients order) x)
  iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed =
    iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1

  iteratedGeometricPowerSeriesValueOfAbs<1-sealed :
    ∀ x →
    (absx<1 : Abs.absℝ x <ℝ Real.ιℚ 1) →
    ∀ order →
    (summable :
      PowerSeriesSummableAt
        (iteratedGeometricCoefficients order) x) →
    powerSeriesValue
        (iteratedGeometricCoefficients order) x summable
      ≡
    iteratedProduct order
      (geometricReciprocal x
        (absContraction→value<1 x absx<1))
  iteratedGeometricPowerSeriesValueOfAbs<1-sealed =
    iteratedGeometricPowerSeriesValueOfAbs<1
