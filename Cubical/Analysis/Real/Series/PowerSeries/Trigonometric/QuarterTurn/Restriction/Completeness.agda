module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Completeness where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Endpoints


sineQuarterIntervalIsComplete : ∀ quarter →
  0ℝ ≤ℝ quarter →
  PremetricTheory.isComplete
    (ClosedIntervalPremetricSpace (- quarter) quarter)
sineQuarterIntervalIsComplete quarter zero≤quarter =
  closedIntervalIsComplete (- quarter) quarter
    (sineQuarterEndpointsOrdered quarter zero≤quarter)


sineUnitIntervalIsComplete :
  PremetricTheory.isComplete
    (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ)
sineUnitIntervalIsComplete =
  closedIntervalIsComplete (- 1ℝ) 1ℝ
    sineUnitEndpointsOrdered
