module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Geometric
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric.Coefficients

formalDerivative-iteratedGeometric-pointwise :
  ∀ order n →
  formalDerivative
      (iteratedGeometricCoefficients
        order)
      n
    ≡
  realNatural (suc order)
    · iteratedGeometricCoefficients
        (suc order) n
formalDerivative-iteratedGeometric-pointwise
  order n =
    cong
      (realNatural (suc n) ·_)
      (iteratedGeometricCoefficients-simplex
        order (suc n))
    ∙ sym
        (realNatural-mul
          (suc n)
          (simplexCoefficient
            order (suc n)))
    ∙ cong realNatural
        (simplexCoefficient-derivative-scale
          order n)
    ∙ realNatural-mul
        (suc order)
        (simplexCoefficient
          (suc order) n)
    ∙ cong
        (realNatural (suc order) ·_)
        (sym
          (iteratedGeometricCoefficients-simplex
            (suc order) n))

formalDerivative-iteratedGeometric :
  ∀ order →
  formalDerivative
      (iteratedGeometricCoefficients
        order)
    ≡
  scaleSeries
    (realNatural (suc order))
    (iteratedGeometricCoefficients
      (suc order))
formalDerivative-iteratedGeometric order =
  funExt
    (formalDerivative-iteratedGeometric-pointwise
      order)

formalDerivative-unitCoefficients :
  formalDerivative unitCoefficients
    ≡
  linearGrowthCoefficients
formalDerivative-unitCoefficients =
  funExt
    (λ n →
      mulIdR (realNatural (suc n))
      ∙ sym
          (linearGrowthCoefficients-value
            n))

iteratedGeometricFormalDerivativePowerSeriesSummable :
  ∀ x →
  RationalContractionBound x →
  ∀ order →
  PowerSeriesSummableAt
    (formalDerivative
      (iteratedGeometricCoefficients
        order))
    x
iteratedGeometricFormalDerivativePowerSeriesSummable
  x contraction order =
    subst
      (λ coefficients →
        PowerSeriesSummableAt
          coefficients x)
      (sym
        (formalDerivative-iteratedGeometric
          order))
      (powerSeriesScaleSummable
        (realNatural (suc order))
        (iteratedGeometricCoefficients
          (suc order))
        x
        (iteratedGeometricPowerSeriesSummable
          x contraction (suc order)))

opaque
  iteratedGeometricFormalDerivativePowerSeriesValue :
    ∀ x →
    (contraction :
      RationalContractionBound x) →
    ∀ order →
    (summable :
      PowerSeriesSummableAt
        (formalDerivative
          (iteratedGeometricCoefficients
            order))
        x) →
    powerSeriesValue
        (formalDerivative
          (iteratedGeometricCoefficients
            order))
        x summable
      ≡
    realNatural (suc order)
      · iteratedProduct (suc order)
        (positiveReciprocal
          (1 - x)
          (positiveSub x 1
            (rationalContractionBound→x<1
              x contraction)))
  iteratedGeometricFormalDerivativePowerSeriesValue
    x contraction order summable =
      seriesSumIndependent
        derivative-terms
        summable
        target-summable
    where
    coefficient : ℝ
    coefficient =
      realNatural (suc order)

    next-coefficients : RealSequence
    next-coefficients =
      iteratedGeometricCoefficients
        (suc order)

    next-summable :
      PowerSeriesSummableAt
        next-coefficients x
    next-summable =
      iteratedGeometricPowerSeriesSummable
        x contraction (suc order)

    scaled-summable :
      PowerSeriesSummableAt
        (scaleSeries
          coefficient next-coefficients)
        x
    scaled-summable =
      powerSeriesScaleSummable
        coefficient next-coefficients x
        next-summable

    derivative-terms : RealSequence
    derivative-terms =
      powerSeriesTerms
        (formalDerivative
          (iteratedGeometricCoefficients
            order))
        x

    scaled-terms : RealSequence
    scaled-terms =
      powerSeriesTerms
        (scaleSeries
          coefficient next-coefficients)
        x

    target : ℝ
    target =
      coefficient
        · iteratedProduct (suc order)
          (positiveReciprocal
            (1 - x)
            (positiveSub x 1
              (rationalContractionBound→x<1
                x contraction)))

    scaled-value-path :
      powerSeriesValue
          (scaleSeries
            coefficient next-coefficients)
          x scaled-summable
        ≡
      target
    scaled-value-path =
      powerSeriesValue-scale
        coefficient next-coefficients x
        next-summable scaled-summable
      ∙ cong
          (coefficient ·_)
          (iteratedGeometricPowerSeriesValue
            x contraction (suc order)
            next-summable)

    scaled-has-target :
      HasSum scaled-terms target
    scaled-has-target =
      subst
        (HasSum scaled-terms)
        scaled-value-path
        (seriesSumHasSum
          scaled-terms scaled-summable)

    derivative-terms-path :
      derivative-terms ≡ scaled-terms
    derivative-terms-path =
      cong
        (λ coefficients →
          powerSeriesTerms coefficients x)
        (formalDerivative-iteratedGeometric
          order)

    derivative-has-target :
      HasSum derivative-terms target
    derivative-has-target =
      subst
        (λ terms → HasSum terms target)
        (sym derivative-terms-path)
        scaled-has-target

    target-summable :
      Summable derivative-terms
    target-summable =
      target , derivative-has-target
