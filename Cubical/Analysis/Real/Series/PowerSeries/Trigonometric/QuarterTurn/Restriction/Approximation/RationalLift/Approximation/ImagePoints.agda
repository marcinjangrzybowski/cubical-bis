module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.ImagePoints where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base


-- Image convergence is weaker than a native source Cauchy witness. These
-- data types do not claim that one can recover the latter from the former.

RationalPointSineInverseImageApproximation : ℝ → ℚ → Type₀
RationalPointSineInverseImageApproximation quarter q =
  Σ[ points ∈ (ℕ → ℚ) ]
    (∀ n →
      ((- quarter) ≤ℝ rat (points n)) ×
      (rat (points n) ≤ℝ quarter))
    × isLimitSequence
        (λ n → sinℝ (rat (points n)))
        (unitClamp (rat q))


RationalPointSineInverseImageApproximationFamily : ℝ → Type₀
RationalPointSineInverseImageApproximationFamily quarter =
  (q : ℚ) → RationalPointSineInverseImageApproximation quarter q
