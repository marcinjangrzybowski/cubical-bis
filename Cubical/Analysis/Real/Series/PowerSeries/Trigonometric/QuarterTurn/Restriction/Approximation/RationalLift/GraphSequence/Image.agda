module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.GraphSequence.Image where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Equation
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.GraphSequence.Points


opaque
  rationalSineInverseGraphPoints-sine-values :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate)
      (inverse-law : RationalSineInverseLaw inverseℚ)
      (inverse-range : RationalSineInverseRange quarter inverseℚ)
      (source target : ℕ → ℝ)
      (joint : ∀ n → C.JointlyApproximableFor
        inverseℚ (source n) (target n)) →
    (λ n → sinℝ (fst (rationalSineInverseGraphPoints
      quarter inverseℚ inverse-range source target joint n)))
      ≡ unitClamp ∘ source
  rationalSineInverseGraphPoints-sine-values
      quarter inverseℚ inverse-law inverse-range source target joint =
    cong (sinℝ ∘_)
      (rationalSineInverseGraphPoints-values
        quarter inverseℚ inverse-range source target joint)
    ∙ funExt (λ n →
        rationalSineInverseGraph-sineClamp
          inverseℚ inverse-law
          (source n) (target n) (joint n))
