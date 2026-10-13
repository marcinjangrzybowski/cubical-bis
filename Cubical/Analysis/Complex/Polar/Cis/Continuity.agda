module Cubical.Analysis.Complex.Polar.Cis.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polar.Cis

opaque
  unfolding cisℝ

  cisℝ-isContinuous : isContinuous (ℝPremetricSpace .snd) cisℝ (ℂPremetricSpace .snd)
  cisℝ-isContinuous = pairℂ-isContinuous (ℝPremetricSpace .snd) cosℝ sinℝ
    cosℝIsContinuous sinℝIsContinuous
