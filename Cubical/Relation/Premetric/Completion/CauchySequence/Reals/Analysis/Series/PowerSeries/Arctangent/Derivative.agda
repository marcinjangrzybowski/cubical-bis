module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Derivative where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Uniform
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
open import Cubical.Data.Rationals.Order as ℚ

opaque
  arctangentHasFormalDerivativeOnClosedRadius :
    (q : ℚ₊) (q<1 : fst q ℚ.< 1) →
    IsDerivativeAlong
      (snd (ClosedAbsRadiusPremetricSpace (Real.ιℚ (fst q))))
      fst
      (arctangentOnClosedRadius q q<1)
      (arctangentFormalDerivativeOnClosedRadius q q<1)
  arctangentHasFormalDerivativeOnClosedRadius q q<1 =
    subst2
      (IsDerivativeAlong
        (snd (ClosedAbsRadiusPremetricSpace (Real.ιℚ (fst q)))) fst)
      original-value-path
      derivative-value-path
      (boundedPowerSeriesUniformValueHasFormalDerivative
        onePositiveRational q arctangentCoefficients
        arctangentCoefficientsBounded q<1)
    where
    original-value-path :
      powerSeriesUniformValueOnClosedRadius
          arctangentCoefficients (Real.ιℚ (fst q))
          (boundedPowerSeriesUniformlyCauchy
            onePositiveRational q arctangentCoefficients
            arctangentCoefficientsBounded q<1)
        ≡ arctangentOnClosedRadius q q<1
    original-value-path =
      powerSeriesUniformValueOnClosedRadiusProofIndependent
        arctangentCoefficients (Real.ιℚ (fst q))
        (boundedPowerSeriesUniformlyCauchy
          onePositiveRational q arctangentCoefficients
          arctangentCoefficientsBounded q<1)
        (arctangentUniformlyCauchy q q<1)

    derivative-value-path :
      powerSeriesUniformValueOnClosedRadius
          (formalDerivative arctangentCoefficients)
          (Real.ιℚ (fst q))
          (boundedPowerSeriesFormalDerivativeUniformlyCauchy
            onePositiveRational q arctangentCoefficients
            arctangentCoefficientsBounded q<1)
        ≡ arctangentFormalDerivativeOnClosedRadius q q<1
    derivative-value-path =
      powerSeriesUniformValueOnClosedRadiusProofIndependent
        (formalDerivative arctangentCoefficients)
        (Real.ιℚ (fst q))
        (boundedPowerSeriesFormalDerivativeUniformlyCauchy
          onePositiveRational q arctangentCoefficients
          arctangentCoefficientsBounded q<1)
        (arctangentFormalDerivativeUniformlyCauchy q q<1)
