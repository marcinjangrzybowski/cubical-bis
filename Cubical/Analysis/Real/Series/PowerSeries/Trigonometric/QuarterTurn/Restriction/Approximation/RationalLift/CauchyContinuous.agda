module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.CauchyContinuous where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.CauchyGraph


opaque
  rationalSineInverse-isCauchyContinuous :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate) →
    RationalSineInverseLaw inverseℚ →
    RationalSineInverseRange quarter inverseℚ →
    ChosenQuarterTurnSineClosenessReflectionModulus quarter →
    C.IsCauchyContinuous inverseℚ
  rationalSineInverse-isCauchyContinuous
      quarter inverseℚ inverse-law inverse-range modulus =
    C.cauchyContinuous
      (rationalSineInverse-presCauchyGraph
        quarter inverseℚ inverse-law inverse-range modulus)


  rationalSineInverseConstruction→data :
    ∀ quarter →
    ChosenQuarterTurnSineClosenessReflectionModulus quarter →
    RationalSineInverseConstruction quarter →
    RationalSineInverseData quarter
  rationalSineInverseConstruction→data
      quarter modulus (inverseℚ , inverse-law , inverse-range) =
    inverseℚ
    , rationalSineInverse-isCauchyContinuous
        quarter inverseℚ inverse-law inverse-range modulus
    , inverse-law
    , inverse-range
