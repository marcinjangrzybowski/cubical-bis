module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Reciprocal.Value where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Reciprocal.Ratio
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Reciprocal.Definition
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
open import Cubical.Data.Rationals.Order as ℚ

opaque
  arctangentFormalDerivativeValue≡Reciprocal :
    (q : ℚ₊) (q<1 : fst q ℚ.< 1) →
    (point : ClosedAbsRadius (Real.ιℚ (fst q))) →
    arctangentFormalDerivativeOnClosedRadius q q<1 point
      ≡ arctangentReciprocalOnClosedRadius q q<1 point
  arctangentFormalDerivativeValue≡Reciprocal q q<1 point =
    seriesSumIndependent derivative-terms value-summable reciprocal-summable
    where
    x : Real.ℝ
    x = fst point

    ratio : Real.ℝ
    ratio = arctangentRatio x

    derivative-terms : RealSequence
    derivative-terms =
      powerSeriesTerms (formalDerivative arctangentCoefficients) x

    derivative-terms≡interleaved-geometric :
      derivative-terms ≡ zeroInterleave (geometricTerms ratio)
    derivative-terms≡interleaved-geometric =
        cong (λ coefficients → powerSeriesTerms coefficients x)
          formalDerivative-arctangentCoefficients
      ∙ arctangentDerivativeTermsAsInterleavedGeometric x

    value-summable : Summable derivative-terms
    value-summable =
      arctangentFormalDerivativeOnClosedRadius q q<1 point
      , powerSeriesUniformValueOnClosedRadiusHasSum
          (formalDerivative arctangentCoefficients)
          (Real.ιℚ (fst q))
          (arctangentFormalDerivativeUniformlyCauchy q q<1)
          point

    reciprocal-summable : Summable derivative-terms
    reciprocal-summable =
      arctangentReciprocalOnClosedRadius q q<1 point
      , subst
          (λ terms → HasSum terms
            (arctangentReciprocalOnClosedRadius q q<1 point))
          (sym derivative-terms≡interleaved-geometric)
          (zeroInterleaveHasSum
            (geometricTerms ratio)
            (arctangentReciprocalOnClosedRadius q q<1 point)
            (geometricSeriesHasSumOfAbs<1 ratio
              (arctangentRatioAbs<one q q<1 point)))
