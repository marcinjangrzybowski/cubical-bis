module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.IntermediateValue where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Surjectivity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Equation
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Range
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.CauchyContinuous


opaque
  rationalSineInverse→intermediateValue :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate)
      (inverseℚ-cc : C.IsCauchyContinuous inverseℚ) →
      RationalSineInverseLaw inverseℚ →
      RationalSineInverseRange quarter inverseℚ →
      SineQuarterIntermediateValue quarter
  rationalSineInverse→intermediateValue
      quarter inverseℚ inverseℚ-cc inverse-law inverse-range
      target lower upper =
    ∣ liftRationalSineInverse-inQuarter
        quarter inverseℚ inverseℚ-cc inverse-range target
    , cong sinℝ
        (liftRationalSineInverse-inQuarter-value
          quarter inverseℚ inverseℚ-cc inverse-range target)
      ∙ liftRationalSineInverse-sineClamp
        inverseℚ inverseℚ-cc inverse-law target
      ∙ unitClampFix target lower upper
    ∣₁


  rationalSineInverseData→intermediateValue :
    ∀ quarter →
    RationalSineInverseData quarter →
    SineQuarterIntermediateValue quarter
  rationalSineInverseData→intermediateValue
      quarter (inverseℚ , inverseℚ-cc , inverse-law , inverse-range) =
    rationalSineInverse→intermediateValue
      quarter inverseℚ inverseℚ-cc inverse-law inverse-range


  rationalSineInverseConstruction→intermediateValue :
    ∀ quarter →
    ChosenQuarterTurnSineClosenessReflectionModulus quarter →
    RationalSineInverseConstruction quarter →
    SineQuarterIntermediateValue quarter
  rationalSineInverseConstruction→intermediateValue
      quarter modulus construction =
    rationalSineInverseData→intermediateValue quarter
      (rationalSineInverseConstruction→data
        quarter modulus construction)


  mereRationalSineInverseConstruction→intermediateValue :
    ∀ quarter →
    MereChosenQuarterTurnSineClosenessReflectionModulus quarter →
    RationalSineInverseConstruction quarter →
    SineQuarterIntermediateValue quarter
  mereRationalSineInverseConstruction→intermediateValue
      quarter mere-modulus construction =
    PT.rec
      (isPropSineQuarterIntermediateValue quarter)
      (λ modulus →
        rationalSineInverseConstruction→intermediateValue
          quarter modulus construction)
      mere-modulus
