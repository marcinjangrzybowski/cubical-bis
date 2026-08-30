module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Geometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LinearGrowth
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric.Coefficients


-- Differentiating the simplex coefficients raises their order once and
-- contributes the scalar `order + 1`.

formalDerivative-iteratedGeometric-pointwise : ∀ order n →
  formalDerivative (iteratedGeometricCoefficients order) n ≡
  realNatural (suc order) Mul.·
    iteratedGeometricCoefficients (suc order) n
formalDerivative-iteratedGeometric-pointwise order n =
  cong
      (realNatural (suc n) Mul.·_)
      (iteratedGeometricCoefficients-simplex order (suc n))
  ∙ sym
      (realNatural-mul
        (suc n) (simplexCoefficient order (suc n)))
  ∙ cong realNatural
      (simplexCoefficient-derivative-scale order n)
  ∙ realNatural-mul
      (suc order) (simplexCoefficient (suc order) n)
  ∙ cong
      (realNatural (suc order) Mul.·_)
      (sym
        (iteratedGeometricCoefficients-simplex
          (suc order) n))


formalDerivative-iteratedGeometric : ∀ order →
  formalDerivative (iteratedGeometricCoefficients order) ≡
  scaleSeries
    (realNatural (suc order))
    (iteratedGeometricCoefficients (suc order))
formalDerivative-iteratedGeometric order =
  funExt (formalDerivative-iteratedGeometric-pointwise order)


formalDerivative-unitCoefficients :
  formalDerivative unitCoefficients ≡ linearGrowthCoefficients
formalDerivative-unitCoefficients =
  funExt λ n → mul-one-right (realNatural (suc n))


iteratedGeometricFormalDerivativePowerSeriesSummableOfAbs<1 :
  ∀ x →
  Abs.absℝ x <ℝ Real.ιℚ 1 →
  ∀ order →
  PowerSeriesSummableAt
    (formalDerivative
      (iteratedGeometricCoefficients order)) x
iteratedGeometricFormalDerivativePowerSeriesSummableOfAbs<1
  x absx<1 order =
    subst
      (λ coefficients → PowerSeriesSummableAt coefficients x)
      (sym (formalDerivative-iteratedGeometric order))
      (powerSeriesScaleSummable
        (realNatural (suc order))
        (iteratedGeometricCoefficients (suc order))
        x
        (iteratedGeometricPowerSeriesSummableOfAbs<1
          x absx<1 (suc order)))


iteratedGeometricFormalDerivativePowerSeriesSummable :
  ∀ x →
  RationalContractionBound x →
  ∀ order →
  PowerSeriesSummableAt
    (formalDerivative
      (iteratedGeometricCoefficients order)) x
iteratedGeometricFormalDerivativePowerSeriesSummable
  x contraction order =
    iteratedGeometricFormalDerivativePowerSeriesSummableOfAbs<1
      x (rationalContractionBound→abs<1 x contraction) order


iteratedGeometricFormalDerivativePowerSeriesValueOfAbs<1 :
  ∀ x →
  (absx<1 : Abs.absℝ x <ℝ Real.ιℚ 1) →
  ∀ order →
  (summable :
    PowerSeriesSummableAt
      (formalDerivative
        (iteratedGeometricCoefficients order)) x) →
  powerSeriesValue
      (formalDerivative
        (iteratedGeometricCoefficients order)) x summable
    ≡
  realNatural (suc order) Mul.·
    iteratedProduct (suc order)
      (geometricReciprocal x
        (≤<ℝ-trans
          x (Abs.absℝ x) (Real.ιℚ 1)
          (x≤abs x)
          absx<1))
iteratedGeometricFormalDerivativePowerSeriesValueOfAbs<1
  x absx<1 order summable =
    seriesSumIndependent derivative-terms summable target-summable
  where
  coefficient : Real.ℝ
  coefficient = realNatural (suc order)

  next-coefficients : RealSequence
  next-coefficients = iteratedGeometricCoefficients (suc order)

  next-summable : PowerSeriesSummableAt next-coefficients x
  next-summable =
    iteratedGeometricPowerSeriesSummableOfAbs<1
      x absx<1 (suc order)

  scaled-summable :
    PowerSeriesSummableAt
      (scaleSeries coefficient next-coefficients) x
  scaled-summable =
    powerSeriesScaleSummable
      coefficient next-coefficients x next-summable

  derivative-terms : RealSequence
  derivative-terms =
    powerSeriesTerms
      (formalDerivative (iteratedGeometricCoefficients order)) x

  scaled-terms : RealSequence
  scaled-terms =
    powerSeriesTerms
      (scaleSeries coefficient next-coefficients) x

  x<1 : x <ℝ Real.ιℚ 1
  x<1 =
    ≤<ℝ-trans
      x (Abs.absℝ x) (Real.ιℚ 1)
      (x≤abs x)
      absx<1

  target : Real.ℝ
  target =
    coefficient Mul.·
      iteratedProduct (suc order) (geometricReciprocal x x<1)

  scaled-value-path :
    powerSeriesValue
        (scaleSeries coefficient next-coefficients)
        x scaled-summable
      ≡
    target
  scaled-value-path =
    powerSeriesValue-scale
      coefficient next-coefficients x
      next-summable scaled-summable
    ∙ cong
        (coefficient Mul.·_)
        (iteratedGeometricPowerSeriesValueOfAbs<1
          x absx<1 (suc order) next-summable)

  scaled-has-target : HasSum scaled-terms target
  scaled-has-target =
    subst
      (HasSum scaled-terms)
      scaled-value-path
      (seriesSumHasSum scaled-terms scaled-summable)

  derivative-terms-path : derivative-terms ≡ scaled-terms
  derivative-terms-path =
    cong
      (λ coefficients → powerSeriesTerms coefficients x)
      (formalDerivative-iteratedGeometric order)

  derivative-has-target : HasSum derivative-terms target
  derivative-has-target =
    subst
      (λ terms → HasSum terms target)
      (sym derivative-terms-path)
      scaled-has-target

  target-summable : Summable derivative-terms
  target-summable = target , derivative-has-target


iteratedGeometricFormalDerivativePowerSeriesValue :
  ∀ x →
  (contraction : RationalContractionBound x) →
  ∀ order →
  (summable :
    PowerSeriesSummableAt
      (formalDerivative
        (iteratedGeometricCoefficients order)) x) →
  powerSeriesValue
      (formalDerivative
        (iteratedGeometricCoefficients order)) x summable
    ≡
  realNatural (suc order) Mul.·
    iteratedProduct (suc order)
      (geometricReciprocal x
        (rationalContractionBound→x<1 x contraction))
iteratedGeometricFormalDerivativePowerSeriesValue
  x contraction order summable =
    iteratedGeometricFormalDerivativePowerSeriesValueOfAbs<1
      x (rationalContractionBound→abs<1 x contraction)
      order summable


opaque
  iteratedGeometricFormalDerivativePowerSeriesValueOfAbs<1-sealed :
    ∀ x →
    (absx<1 : Abs.absℝ x <ℝ Real.ιℚ 1) →
    ∀ order →
    (summable :
      PowerSeriesSummableAt
        (formalDerivative
          (iteratedGeometricCoefficients order)) x) →
    powerSeriesValue
        (formalDerivative
          (iteratedGeometricCoefficients order)) x summable
      ≡
    realNatural (suc order) Mul.·
      iteratedProduct (suc order)
        (geometricReciprocal x
          (≤<ℝ-trans
            x (Abs.absℝ x) (Real.ιℚ 1)
            (x≤abs x) absx<1))
  iteratedGeometricFormalDerivativePowerSeriesValueOfAbs<1-sealed =
    iteratedGeometricFormalDerivativePowerSeriesValueOfAbs<1
