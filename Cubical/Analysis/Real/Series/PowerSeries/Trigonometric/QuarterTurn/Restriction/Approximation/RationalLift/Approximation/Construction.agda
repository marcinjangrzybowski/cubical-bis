module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Construction where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Equation
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.Range
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Approximation.RationalPoints


rationalSineInverseApproximationFamily→construction :
  ∀ quarter →
  RationalSineInverseApproximationFamily quarter →
  RationalSineInverseConstruction quarter
rationalSineInverseApproximationFamily→construction
    quarter approximations =
  (λ q →
    lim
      (λ n → fst (fst (approximations q) n))
      (fst (snd (approximations q))))
  , rationalSineInverseApproximationCandidate-law quarter approximations
  , rationalSineInverseApproximationCandidate-range quarter approximations


mereRationalSineInverseApproximationFamily→mereConstruction :
  ∀ quarter →
  MereRationalSineInverseApproximationFamily quarter →
  ∥ RationalSineInverseConstruction quarter ∥₁
mereRationalSineInverseApproximationFamily→mereConstruction quarter =
  PT.map (rationalSineInverseApproximationFamily→construction quarter)


rationalPointSineInverseApproximationFamily→construction :
  ∀ quarter →
  RationalPointSineInverseApproximationFamily quarter →
  RationalSineInverseConstruction quarter
rationalPointSineInverseApproximationFamily→construction
    quarter approximations =
  rationalSineInverseApproximationFamily→construction quarter
    (rationalPointSineInverseApproximationFamily→approximationFamily
      quarter approximations)
