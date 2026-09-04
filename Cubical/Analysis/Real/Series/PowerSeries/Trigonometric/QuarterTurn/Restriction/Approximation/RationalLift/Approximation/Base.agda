module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.IntervalLimit
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base


-- This is the exact output expected from a rational-target bisection.  Its
-- source sequence may use arbitrary real interval points; a rational
-- bisection can of course supply points embedded by `rat`.

RationalSineInverseApproximation : ℝ → ℚ → Type₀
RationalSineInverseApproximation quarter q =
  SineQuarterApproximation quarter (unitClamp (rat q))


RationalSineInverseApproximationFamily : ℝ → Type₀
RationalSineInverseApproximationFamily quarter =
  (q : ℚ) → RationalSineInverseApproximation quarter q


MereRationalSineInverseApproximationFamily : ℝ → Type₀
MereRationalSineInverseApproximationFamily quarter =
  ∥ RationalSineInverseApproximationFamily quarter ∥₁


rationalSineInverseApproximationCandidate :
  ∀ quarter →
  RationalSineInverseApproximationFamily quarter →
  RationalSineInverseCandidate
rationalSineInverseApproximationCandidate quarter approximations q =
  sineQuarterSequenceLimit quarter
    (fst (approximations q))
    (fst (snd (approximations q)))
