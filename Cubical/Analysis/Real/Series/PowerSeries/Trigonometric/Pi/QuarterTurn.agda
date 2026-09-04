module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.QuarterTurn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Consequences
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Orientation


-- Kept for compatibility with callers that supply an orientation witness.
-- `characterizedHalfPi-sineOne` now derives it from the characterization.

CharacterizedHalfPiSineOne :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiSineOne construction =
  sinℝ (fst construction) ≡ 1ℝ


isPropCharacterizedHalfPiSineOne :
  (construction : CharacterizedHalfPi) →
  isProp (CharacterizedHalfPiSineOne construction)
isPropCharacterizedHalfPiSineOne construction =
  isSetℝ (sinℝ (fst construction)) 1ℝ


characterizedHalfPi-positiveQuarterTurn :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSineOne construction →
  IsPositiveQuarterTurn (fst construction)
characterizedHalfPi-positiveQuarterTurn construction sine-one =
  firstPositiveCosineZero-zero (snd construction)
  , sine-one


characterizedHalfPi-quarterTurn :
  (construction : CharacterizedHalfPi) →
  IsPositiveQuarterTurn (fst construction)
characterizedHalfPi-quarterTurn construction =
  characterizedHalfPi-positiveQuarterTurn construction
    (characterizedHalfPi-sineOne construction)


characterizedHalfPi-positiveSine→positiveQuarterTurn :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSinePositive construction →
  IsPositiveQuarterTurn (fst construction)
characterizedHalfPi-positiveSine→positiveQuarterTurn
    construction sine-positive =
  characterizedHalfPi-positiveQuarterTurn construction
    (characterizedHalfPi-positiveSine→sineOne
      construction sine-positive)


characterizedPi-asHalfTurn :
  (construction : CharacterizedHalfPi) →
  characterizedPi construction ≡ halfTurn (fst construction)
characterizedPi-asHalfTurn construction = refl


characterizedTwoPi :
  CharacterizedHalfPi → ℝ
characterizedTwoPi construction =
  characterizedPi construction + characterizedPi construction


characterizedTwoPi-asFullTurn :
  (construction : CharacterizedHalfPi) →
  characterizedTwoPi construction ≡ fullTurn (fst construction)
characterizedTwoPi-asFullTurn construction = refl


opaque
  sinℝ-characterizedPi :
    (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSineOne construction →
    sinℝ (characterizedPi construction) ≡ 0ℝ
  sinℝ-characterizedPi construction sine-one =
      cong sinℝ (characterizedPi-asHalfTurn construction)
    ∙ sinℝ-halfTurn
        (fst construction)
        (characterizedHalfPi-positiveQuarterTurn
          construction sine-one)


  cosℝ-characterizedPi :
    (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSineOne construction →
    cosℝ (characterizedPi construction) ≡ - 1ℝ
  cosℝ-characterizedPi construction sine-one =
      cong cosℝ (characterizedPi-asHalfTurn construction)
    ∙ cosℝ-halfTurn
        (fst construction)
        (characterizedHalfPi-positiveQuarterTurn
          construction sine-one)


opaque
  sinℝ-add-characterizedPi :
    (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSineOne construction →
    ∀ x →
    sinℝ (x + characterizedPi construction) ≡ - sinℝ x
  sinℝ-add-characterizedPi construction sine-one x =
      cong sinℝ
        (cong (x +_) (characterizedPi-asHalfTurn construction))
    ∙ sinℝ-add-halfTurn
        (fst construction)
        (characterizedHalfPi-positiveQuarterTurn
          construction sine-one)
        x


  cosℝ-add-characterizedPi :
    (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSineOne construction →
    ∀ x →
    cosℝ (x + characterizedPi construction) ≡ - cosℝ x
  cosℝ-add-characterizedPi construction sine-one x =
      cong cosℝ
        (cong (x +_) (characterizedPi-asHalfTurn construction))
    ∙ cosℝ-add-halfTurn
        (fst construction)
        (characterizedHalfPi-positiveQuarterTurn
          construction sine-one)
        x


opaque
  sinℝ-add-characterizedTwoPi :
    (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSineOne construction →
    ∀ x →
    sinℝ (x + characterizedTwoPi construction) ≡ sinℝ x
  sinℝ-add-characterizedTwoPi construction sine-one x =
      cong sinℝ
        (cong (x +_)
          (characterizedTwoPi-asFullTurn construction))
    ∙ sinℝ-add-fullTurn
        (fst construction)
        (characterizedHalfPi-positiveQuarterTurn
          construction sine-one)
        x


  cosℝ-add-characterizedTwoPi :
    (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSineOne construction →
    ∀ x →
    cosℝ (x + characterizedTwoPi construction) ≡ cosℝ x
  cosℝ-add-characterizedTwoPi construction sine-one x =
      cong cosℝ
        (cong (x +_)
          (characterizedTwoPi-asFullTurn construction))
    ∙ cosℝ-add-fullTurn
        (fst construction)
        (characterizedHalfPi-positiveQuarterTurn
          construction sine-one)
        x
