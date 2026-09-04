module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.GraphSequence.Points where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Range


rationalSineInverseGraphPoints :
  ∀ quarter (inverseℚ : RationalSineInverseCandidate) →
  RationalSineInverseRange quarter inverseℚ →
  (source target : ℕ → ℝ) →
  (∀ n → C.JointlyApproximableFor
    inverseℚ (source n) (target n)) →
  ℕ → SineQuarterInterval quarter
rationalSineInverseGraphPoints
    quarter inverseℚ inverse-range source target joint n =
  rationalSineInverseGraph-inQuarter
    quarter inverseℚ inverse-range
    (source n) (target n) (joint n)


opaque
  rationalSineInverseGraphPoints-values :
    ∀ quarter (inverseℚ : RationalSineInverseCandidate)
      (inverse-range : RationalSineInverseRange quarter inverseℚ)
      (source target : ℕ → ℝ)
      (joint : ∀ n → C.JointlyApproximableFor
        inverseℚ (source n) (target n)) →
    (λ n → fst (rationalSineInverseGraphPoints
      quarter inverseℚ inverse-range source target joint n))
      ≡ target
  rationalSineInverseGraphPoints-values
      quarter inverseℚ inverse-range source target joint =
    funExt λ n →
      rationalSineInverseGraph-inQuarter-value
        quarter inverseℚ inverse-range
        (source n) (target n) (joint n)
