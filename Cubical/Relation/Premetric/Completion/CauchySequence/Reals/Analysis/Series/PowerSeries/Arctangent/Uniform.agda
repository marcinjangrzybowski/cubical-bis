module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Uniform where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Coefficients
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
open import Cubical.Data.Rationals.Order as ℚ


opaque
  arctangentUniformlyAbsolutelyCauchy : ∀ (q : ℚ₊) →
    fst q ℚ.< 1 →
    PowerSeriesUniformlyAbsolutelyCauchyOnRadius
      arctangentCoefficients (Real.ιℚ (fst q))
  arctangentUniformlyAbsolutelyCauchy q q<1 =
    boundedPowerSeriesUniformlyAbsolutelyCauchy
      onePositiveRational q arctangentCoefficients
      arctangentCoefficientsBounded q<1

  arctangentUniformlyCauchy : ∀ (q : ℚ₊) →
    fst q ℚ.< 1 →
    PowerSeriesUniformlyCauchyOnRadius
      arctangentCoefficients (Real.ιℚ (fst q))
  arctangentUniformlyCauchy q q<1 =
    boundedPowerSeriesUniformlyCauchy
      onePositiveRational q arctangentCoefficients
      arctangentCoefficientsBounded q<1


arctangentOnClosedRadius :
  (q : ℚ₊) → fst q ℚ.< 1 →
  ClosedAbsRadius (Real.ιℚ (fst q)) → Real.ℝ
arctangentOnClosedRadius q q<1 =
  powerSeriesUniformValueOnClosedRadius
    arctangentCoefficients (Real.ιℚ (fst q))
    (arctangentUniformlyCauchy q q<1)


opaque
  arctangentFormalDerivativeUniformlyCauchy : ∀ (q : ℚ₊) →
    fst q ℚ.< 1 →
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative arctangentCoefficients) (Real.ιℚ (fst q))
  arctangentFormalDerivativeUniformlyCauchy q q<1 =
    boundedPowerSeriesFormalDerivativeUniformlyCauchy
      onePositiveRational q arctangentCoefficients
      arctangentCoefficientsBounded q<1


arctangentDerivativeCoefficientsUniformlyCauchy : ∀ (q : ℚ₊) →
  fst q ℚ.< 1 →
  PowerSeriesUniformlyCauchyOnRadius
    arctangentDerivativeCoefficients (Real.ιℚ (fst q))
arctangentDerivativeCoefficientsUniformlyCauchy q q<1 =
  subst
    (λ c → PowerSeriesUniformlyCauchyOnRadius c (Real.ιℚ (fst q)))
    formalDerivative-arctangentCoefficients
    (arctangentFormalDerivativeUniformlyCauchy q q<1)


arctangentFormalDerivativeOnClosedRadius :
  (q : ℚ₊) → fst q ℚ.< 1 →
  ClosedAbsRadius (Real.ιℚ (fst q)) → Real.ℝ
arctangentFormalDerivativeOnClosedRadius q q<1 =
  powerSeriesUniformValueOnClosedRadius
    (formalDerivative arctangentCoefficients)
    (Real.ιℚ (fst q))
    (arctangentFormalDerivativeUniformlyCauchy q q<1)
