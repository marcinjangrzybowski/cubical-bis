module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Completeness where

open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Interval
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius


-- These completeness results are inherited by explicit nonexpanding
-- retractions.  Consequently they need neither a fresh choice of Cauchy
-- moduli nor a representation comparison.

lowerClosedHalfLineIsComplete : ∀ a →
  PremetricTheory.isComplete (LowerClosedHalfLinePremetricSpace a)
lowerClosedHalfLineIsComplete a =
  retractPresIsComplete
    Real.isCompleteℝ
    (lowerClosedHalfLineInclusionNE a)
    (maxToLowerClosedHalfLineNE a)
    (maxToLowerClosedHalfLineSection a)


upperClosedHalfLineIsComplete : ∀ b →
  PremetricTheory.isComplete (UpperClosedHalfLinePremetricSpace b)
upperClosedHalfLineIsComplete b =
  retractPresIsComplete
    Real.isCompleteℝ
    (upperClosedHalfLineInclusionNE b)
    (minToUpperClosedHalfLineNE b)
    (minToUpperClosedHalfLineSection b)


closedIntervalIsComplete : ∀ a b →
  a ≤ℝ b →
  PremetricTheory.isComplete (ClosedIntervalPremetricSpace a b)
closedIntervalIsComplete a b a≤b =
  retractPresIsComplete
    Real.isCompleteℝ
    (closedIntervalInclusionNE a b)
    (clampIntervalRetractionNE a b a≤b)
    (clampIntervalRetractionSection a b a≤b)


closedAbsRadiusIsComplete : ∀ radius →
  Real.ιℚ 0 ≤ℝ radius →
  PremetricTheory.isComplete (ClosedAbsRadiusPremetricSpace radius)
closedAbsRadiusIsComplete radius 0≤radius =
  retractPresIsComplete
    Real.isCompleteℝ
    (closedAbsRadiusInclusionNE radius)
    (closedAbsRadiusRetractionNE radius 0≤radius)
    (closedAbsRadiusRetractionSection radius 0≤radius)
