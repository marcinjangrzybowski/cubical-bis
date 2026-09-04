module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Consequences where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import
  Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ; mulIdL)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


CharacterizedHalfPiSinePositive :
  CharacterizedHalfPi → Type₀
CharacterizedHalfPiSinePositive construction =
  0ℝ <ℝ sinℝ (fst construction)


isPropCharacterizedHalfPiSinePositive :
  (construction : CharacterizedHalfPi) →
  isProp (CharacterizedHalfPiSinePositive construction)
isPropCharacterizedHalfPiSinePositive construction =
  isProp<ℝ 0ℝ (sinℝ (fst construction))


opaque
  positiveSquareOne→one : ∀ x →
    0ℝ <ℝ x →
    x · x ≡ 1ℝ →
    x ≡ 1ℝ
  positiveSquareOne→one x zero<x square-one =
    ≤ℝ-antisym x 1ℝ
      (notGreater→≤ℝ x 1ℝ λ one<x →
        <ℝ-irrefl 1ℝ
          (subst2 _<ℝ_
            (mulIdL 1ℝ)
            square-one
            (mulPres<
              1ℝ x 1ℝ x
              zero<x
              (isOrderedCommRingℝ .IsOrderedCommRing.0<1)
              one<x one<x)))
      (notGreater→≤ℝ 1ℝ x λ x<one →
        <ℝ-irrefl 1ℝ
          (subst2 _<ℝ_
            square-one
            (mulIdL 1ℝ)
            (mulPres<
              x 1ℝ x 1ℝ
              (isOrderedCommRingℝ .IsOrderedCommRing.0<1)
              zero<x
              x<one x<one)))


  cosineZero→sineSquareOne : ∀ x →
    cosℝ x ≡ 0ℝ →
    sinℝ x · sinℝ x ≡ 1ℝ
  cosineZero→sineSquareOne x cosine-zero =
      sym (addIdR sine-square)
    ∙ cong (sine-square +_)
        (sym cosine-square-zero)
    ∙ sin²+cos²≡1 x
    where
    sine-square : ℝ
    sine-square = sinℝ x · sinℝ x

    cosine-square-zero :
      cosℝ x · cosℝ x ≡ 0ℝ
    cosine-square-zero =
      cong₂ _·_ cosine-zero cosine-zero
      ∙ ℝRing.0LeftAnnihilates 0ℝ


  characterizedHalfPi-sineSquareOne :
    (construction : CharacterizedHalfPi) →
    sinℝ (fst construction) · sinℝ (fst construction) ≡ 1ℝ
  characterizedHalfPi-sineSquareOne construction =
    cosineZero→sineSquareOne
      (fst construction)
      (firstPositiveCosineZero-zero (snd construction))


opaque
  characterizedHalfPi-positiveSine→sineOne :
    (construction : CharacterizedHalfPi) →
    CharacterizedHalfPiSinePositive construction →
    sinℝ (fst construction) ≡ 1ℝ
  characterizedHalfPi-positiveSine→sineOne construction sine-positive =
    positiveSquareOne→one
      (sinℝ (fst construction))
      sine-positive
      (characterizedHalfPi-sineSquareOne construction)
