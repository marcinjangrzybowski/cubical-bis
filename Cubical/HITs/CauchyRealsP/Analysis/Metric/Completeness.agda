module Cubical.HITs.CauchyRealsP.Analysis.Metric.Completeness where

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval
open import Cubical.HITs.CauchyRealsP.Analysis.Metric.Radius

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties

lowerClosedHalfLineIsComplete : ∀ a →
  PremetricTheory.isComplete (LowerClosedHalfLinePremetricSpace a)
lowerClosedHalfLineIsComplete a =
  retractPresIsComplete
    isCompleteℝ
    (lowerClosedHalfLineInclusionNE a)
    (maxToLowerClosedHalfLineNE a)
    (maxToLowerClosedHalfLineSection a)

upperClosedHalfLineIsComplete : ∀ b →
  PremetricTheory.isComplete (UpperClosedHalfLinePremetricSpace b)
upperClosedHalfLineIsComplete b =
  retractPresIsComplete
    isCompleteℝ
    (upperClosedHalfLineInclusionNE b)
    (minToUpperClosedHalfLineNE b)
    (minToUpperClosedHalfLineSection b)

closedIntervalIsComplete : ∀ a b →
  a ≤ℝ b →
  PremetricTheory.isComplete (ClosedIntervalPremetricSpace a b)
closedIntervalIsComplete a b a≤b =
  retractPresIsComplete
    isCompleteℝ
    (closedIntervalInclusionNE a b)
    (clampIntervalRetractionNE a b a≤b)
    (clampIntervalRetractionSection a b a≤b)

closedAbsRadiusIsComplete : ∀ radius →
  0 ≤ℝ radius →
  PremetricTheory.isComplete (ClosedAbsRadiusPremetricSpace radius)
closedAbsRadiusIsComplete radius 0≤radius =
  retractPresIsComplete
    isCompleteℝ
    (closedAbsRadiusInclusionNE radius)
    (closedAbsRadiusRetractionNE radius 0≤radius)
    (closedAbsRadiusRetractionSection radius 0≤radius)
