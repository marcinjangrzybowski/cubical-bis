module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Endpoints where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negZero)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (negPres≤)
open import Cubical.Analysis.Real.Domain.Interval
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


sineQuarterEndpointsOrdered : ∀ quarter →
  0ℝ ≤ℝ quarter → (- quarter) ≤ℝ quarter
sineQuarterEndpointsOrdered quarter zero≤quarter =
  ≤ℝ-trans (- quarter) 0ℝ quarter
    (subst ((- quarter) ≤ℝ_) negZero
      (negPres≤ 0ℝ quarter zero≤quarter))
    zero≤quarter


sineQuarterLeft : ∀ quarter →
  0ℝ ≤ℝ quarter → SineQuarterInterval quarter
sineQuarterLeft quarter zero≤quarter =
  (- quarter)
  , ≤ℝ-refl (- quarter)
  , sineQuarterEndpointsOrdered quarter zero≤quarter


sineQuarterRight : ∀ quarter →
  0ℝ ≤ℝ quarter → SineQuarterInterval quarter
sineQuarterRight quarter zero≤quarter =
  quarter
  , sineQuarterEndpointsOrdered quarter zero≤quarter
  , ≤ℝ-refl quarter


opaque
  sinℝ-negativeQuarter : ∀ quarter →
    (positive-quarter : IsPositiveQuarterTurn quarter) →
    sinℝ (- quarter) ≡ - 1ℝ
  sinℝ-negativeQuarter quarter positive-quarter =
    sinℝ-neg quarter
    ∙ cong -_ (quarterTurnSineOne positive-quarter)


  sinℝ-positiveQuarter : ∀ quarter →
    (positive-quarter : IsPositiveQuarterTurn quarter) →
    sinℝ quarter ≡ 1ℝ
  sinℝ-positiveQuarter quarter positive-quarter =
    quarterTurnSineOne positive-quarter
