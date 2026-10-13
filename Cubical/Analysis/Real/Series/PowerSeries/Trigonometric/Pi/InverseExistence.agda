module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.InverseExistence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.QuarterTurn
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.RestrictedSine
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Iteration

-- Supplies the missing input to every existing characterized inverse API.
opaque
  characterizedHalfPi-sineIntermediateValue : (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSineIntermediateValue construction
  characterizedHalfPi-sineIntermediateValue construction =
    sineQuarterIntermediateValueByIteration (fst construction)
      (characterizedHalfPi-quarterTurn construction) (snd construction)
