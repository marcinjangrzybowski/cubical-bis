module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Rationals.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (mul-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric.Derivative


-- Absolute convergence at the boundary radius is a uniform majorant for
-- the whole closed ball.  The self-majorant is valid because all simplex
-- coefficients are nonnegative.

iteratedGeometricPowerSeriesUniformlyAbsolutelyCauchyOfAbs<1 :
  ∀ radius →
  Abs.absℝ radius <ℝ Real.ιℚ 1 →
  ∀ order →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    (iteratedGeometricCoefficients order) radius
iteratedGeometricPowerSeriesUniformlyAbsolutelyCauchyOfAbs<1
  radius abs-radius<1 order =
    powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms coefficients radius)
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed
          radius abs-radius<1 order))
  where
  coefficients : RealSequence
  coefficients = iteratedGeometricCoefficients order

  nonnegative : NonnegativeCoefficients coefficients
  nonnegative = iteratedGeometricCoefficients-nonnegative-sealed order


iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1 :
  ∀ radius →
  Abs.absℝ radius <ℝ Real.ιℚ 1 →
  ∀ order →
  PowerSeriesUniformlyCauchyOnRadius
    (iteratedGeometricCoefficients order) radius
iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1
  radius abs-radius<1 order =
    powerSeriesUniformlyCauchyByCoefficientMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms coefficients radius)
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed
          radius abs-radius<1 order))
  where
  coefficients : RealSequence
  coefficients = iteratedGeometricCoefficients order

  nonnegative : NonnegativeCoefficients coefficients
  nonnegative = iteratedGeometricCoefficients-nonnegative-sealed order


opaque
  iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1-sealed :
    ∀ radius →
    Abs.absℝ radius <ℝ Real.ιℚ 1 →
    ∀ order →
    PowerSeriesUniformlyCauchyOnRadius
      (iteratedGeometricCoefficients order) radius
  iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1-sealed =
    iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1


iteratedGeometricPowerSeriesUniformlyCauchy :
  ∀ radius →
  RationalContractionBound radius →
  ∀ order →
  PowerSeriesUniformlyCauchyOnRadius
    (iteratedGeometricCoefficients order) radius
iteratedGeometricPowerSeriesUniformlyCauchy
  radius contraction order =
    iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1-sealed
      radius (rationalContractionBound→abs<1 radius contraction)
      order


iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchyOfAbs<1 :
  ∀ radius →
  Abs.absℝ radius <ℝ Real.ιℚ 1 →
  ∀ order →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (formalDerivative
        (iteratedGeometricCoefficients order)) radius)
iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchyOfAbs<1
  radius abs-radius<1 order =
    subst
      IsAbsolutelyCauchySeries
      (sym derivative-terms-path)
      (scaleSeriesIsAbsolutelyCauchy
        (realNatural (suc order))
        next-terms
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed
          radius abs-radius<1 (suc order)))
  where
  next-coefficients : RealSequence
  next-coefficients = iteratedGeometricCoefficients (suc order)

  next-terms : RealSequence
  next-terms = powerSeriesTerms next-coefficients radius

  derivative-terms-path :
    powerSeriesTerms
        (formalDerivative
          (iteratedGeometricCoefficients order)) radius
      ≡
    scaleSeries (realNatural (suc order)) next-terms
  derivative-terms-path =
    cong
      (λ coefficients → powerSeriesTerms coefficients radius)
      (formalDerivative-iteratedGeometric order)
    ∙ powerSeriesTerms-scale-sequence
        (realNatural (suc order)) next-coefficients radius


opaque
  iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed :
    ∀ radius →
    Abs.absℝ radius <ℝ Real.ιℚ 1 →
    ∀ order →
    IsAbsolutelyCauchySeries
      (powerSeriesTerms
        (formalDerivative
          (iteratedGeometricCoefficients order)) radius)
  iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed =
    iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchyOfAbs<1


iteratedGeometricFormalDerivativeCoefficients-nonnegative :
  ∀ order →
  NonnegativeCoefficients
    (formalDerivative (iteratedGeometricCoefficients order))
iteratedGeometricFormalDerivativeCoefficients-nonnegative order n =
  subst
    (λ value → zeroℝ ≤ℝ value)
    (sym (formalDerivative-iteratedGeometric-pointwise order n))
    (mul-nonnegative
      (realNatural (suc order))
      (iteratedGeometricCoefficients (suc order) n)
      (realNatural-nonnegative (suc order))
      (iteratedGeometricCoefficients-nonnegative-sealed
        (suc order) n))


opaque
  iteratedGeometricFormalDerivativeCoefficients-nonnegative-sealed :
    ∀ order →
    NonnegativeCoefficients
      (formalDerivative (iteratedGeometricCoefficients order))
  iteratedGeometricFormalDerivativeCoefficients-nonnegative-sealed =
    iteratedGeometricFormalDerivativeCoefficients-nonnegative


iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchyOfAbs<1 :
  ∀ radius →
  Abs.absℝ radius <ℝ Real.ιℚ 1 →
  ∀ order →
  PowerSeriesUniformlyCauchyOnRadius
    (formalDerivative (iteratedGeometricCoefficients order))
    radius
iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchyOfAbs<1
  radius abs-radius<1 order =
    powerSeriesUniformlyCauchyByCoefficientMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms coefficients radius)
        (iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchyOfAbs<1-sealed
          radius abs-radius<1 order))
  where
  coefficients : RealSequence
  coefficients =
    formalDerivative (iteratedGeometricCoefficients order)

  nonnegative : NonnegativeCoefficients coefficients
  nonnegative =
    iteratedGeometricFormalDerivativeCoefficients-nonnegative-sealed order


opaque
  iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchyOfAbs<1-sealed :
    ∀ radius →
    Abs.absℝ radius <ℝ Real.ιℚ 1 →
    ∀ order →
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative (iteratedGeometricCoefficients order))
      radius
  iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchyOfAbs<1-sealed =
    iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchyOfAbs<1


iteratedGeometricPowerSeriesFunctionOnClosedRadiusOfAbs<1 :
  ∀ radius →
  Abs.absℝ radius <ℝ Real.ιℚ 1 →
  ℕ → ClosedAbsRadius radius → Real.ℝ
iteratedGeometricPowerSeriesFunctionOnClosedRadiusOfAbs<1
  radius abs-radius<1 order =
    powerSeriesUniformValueOnClosedRadius
      (iteratedGeometricCoefficients order)
      radius
      (iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1-sealed
        radius abs-radius<1 order)


iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadiusOfAbs<1 :
  ∀ radius →
  Abs.absℝ radius <ℝ Real.ιℚ 1 →
  ℕ → ClosedAbsRadius radius → Real.ℝ
iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadiusOfAbs<1
  radius abs-radius<1 order =
    powerSeriesUniformValueOnClosedRadius
      (formalDerivative (iteratedGeometricCoefficients order))
      radius
      (iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchyOfAbs<1-sealed
        radius abs-radius<1 order)


iteratedGeometricPowerSeriesFunctionOnClosedRadiusIsContinuousOfAbs<1 :
  ∀ radius →
  (abs-radius<1 : Abs.absℝ radius <ℝ Real.ιℚ 1) →
  ∀ order →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    (iteratedGeometricPowerSeriesFunctionOnClosedRadiusOfAbs<1
      radius abs-radius<1 order)
    (snd Real.ℝPremetricSpace)
iteratedGeometricPowerSeriesFunctionOnClosedRadiusIsContinuousOfAbs<1
  radius abs-radius<1 order =
    powerSeriesUniformValueOnClosedRadiusIsContinuous
      (iteratedGeometricCoefficients order)
      radius
      (iteratedGeometricPowerSeriesUniformlyCauchyOfAbs<1-sealed
        radius abs-radius<1 order)


-- The generic divided-difference theorem can consume the two checked
-- uniform families above.  Its direct specialization is intentionally left
-- out here: elaborating that proposition currently expands for minutes in
-- Agda even behind opaque recursive witnesses, while adding no new analytic
-- premise or computational content.
