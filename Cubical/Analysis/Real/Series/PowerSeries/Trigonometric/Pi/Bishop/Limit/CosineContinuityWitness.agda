module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.CosineContinuityWitness where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Mappings using (isContinuous)

open import Cubical.Analysis.Real.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


opaque
  cosℝIsContinuousOpaque :
    isContinuous
      (ℝPremetricSpace .snd) cosℝ
      (ℝPremetricSpace .snd)
  cosℝIsContinuousOpaque = cosℝIsContinuous
