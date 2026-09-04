module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.ContinuityWitness where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Mappings using (isContinuous)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration


opaque
  dampedCosineIsContinuousOpaque :
    isContinuous
      (ℝPremetricSpace .snd) cosℝ
      (ℝPremetricSpace .snd)
  dampedCosineIsContinuousOpaque = cosℝIsContinuous


  dampedHalfScalarIsContinuousOpaque :
    isContinuous
      (ℝPremetricSpace .snd)
      (dampedBishopCoefficient ⋆_)
      (ℝPremetricSpace .snd)
  dampedHalfScalarIsContinuousOpaque =
    scalar-isContinuous dampedBishopCoefficient
