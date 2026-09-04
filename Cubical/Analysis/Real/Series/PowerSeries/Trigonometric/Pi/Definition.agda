module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization


-- A characterized value is kept as explicit data until the Bishop
-- convergence/positivity proof supplies an inhabitant.  The underlying real
-- selected by any two such constructions is unique.

CharacterizedHalfPi : Type₀
CharacterizedHalfPi =
  Σ[ half ∈ ℝ ] IsFirstPositiveCosineZero half


opaque
  isPropCharacterizedHalfPi :
    isProp CharacterizedHalfPi
  isPropCharacterizedHalfPi left right =
    Σ≡Prop
      isPropIsFirstPositiveCosineZero
      (firstPositiveCosineZero-unique
        (snd left) (snd right))


characterizedHalfPi :
  CharacterizedHalfPi → ℝ
characterizedHalfPi = fst


characterizedPi :
  CharacterizedHalfPi → ℝ
characterizedPi construction =
  characterizedHalfPi construction +
    characterizedHalfPi construction
