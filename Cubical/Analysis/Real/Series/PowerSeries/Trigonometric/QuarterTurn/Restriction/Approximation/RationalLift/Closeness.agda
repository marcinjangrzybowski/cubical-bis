module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Closeness where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.RationalLift.Error


open PositiveRationals
open PositiveHalvesℚ


opaque
  rationalSineInverseGraph-sineClamp-close :
    ∀ (inverseℚ : RationalSineInverseCandidate) →
    RationalSineInverseLaw inverseℚ →
    ∀ target lifted →
    C.JointlyApproximableFor inverseℚ target lifted →
    ∀ ε → sinℝ lifted ∼[ ε ] unitClamp target
  rationalSineInverseGraph-sineClamp-close
      inverseℚ inverse-law target lifted joint ε =
    PT.rec
      (S.isProp∼ (sinℝ lifted) ε (unitClamp target))
      with-continuity
      (sinℝIsContinuous lifted
        .IsContinuousAt.pres≈ (ε /4₊))
    where
    with-continuity :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ point → lifted ∼[ δ ] point →
          sinℝ lifted ∼[ ε /4₊ ] sinℝ point)) →
      sinℝ lifted ∼[ ε ] unitClamp target
    with-continuity (δ , preserves) =
      PT.rec
        (S.isProp∼ (sinℝ lifted) ε (unitClamp target))
        (rationalSineInverseApproximation-close
          inverseℚ inverse-law target lifted ε δ preserves)
        (joint (ε /4₊) δ)
