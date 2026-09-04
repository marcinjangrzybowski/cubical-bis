module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Equation where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Closeness



opaque
  rationalSineInverseGraph-sineClamp :
    ∀ (inverseℚ : RationalSineInverseCandidate) →
    RationalSineInverseLaw inverseℚ →
    ∀ target output →
    C.JointlyApproximableFor inverseℚ target output →
    sinℝ output ≡ unitClamp target
  rationalSineInverseGraph-sineClamp
      inverseℚ inverse-law target output joint =
    eqℝ (sinℝ output) (unitClamp target)
      (rationalSineInverseGraph-sineClamp-close
        inverseℚ inverse-law target output joint)


  liftRationalSineInverse-sineClamp :
    ∀ (inverseℚ : RationalSineInverseCandidate)
      (inverseℚ-cc : C.IsCauchyContinuous inverseℚ) →
      RationalSineInverseLaw inverseℚ →
      ∀ target →
      sinℝ (liftRationalSineInverse inverseℚ inverseℚ-cc target)
        ≡ unitClamp target
  liftRationalSineInverse-sineClamp
      inverseℚ inverseℚ-cc inverse-law target =
    rationalSineInverseGraph-sineClamp
      inverseℚ inverse-law target
        (liftRationalSineInverse inverseℚ inverseℚ-cc target)
        (C.liftCauchyContinuous-joint
          inverseℚ inverseℚ-cc target)
