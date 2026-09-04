module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Orientation where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order using (positiveReciprocalPositive)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.AdditionDerived
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.PositiveNearZero
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Consequences

open PositiveRationals
open PositiveHalvesℚ


private
  module ℝRing = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  opaque
    cosineZeroReflection : ∀ quarter h → cosℝ quarter ≡ 0ℝ →
      cosℝ (quarter + (- h)) ≡ sinℝ quarter · sinℝ h
    cosineZeroReflection quarter h cosine-zero =
      cosℝ-sub quarter h
      ∙ cong (λ z → z · cosℝ h + sinℝ quarter · sinℝ h) cosine-zero
      ∙ cong (_+ (sinℝ quarter · sinℝ h)) (ℝRing.0LeftAnnihilates (cosℝ h))
      ∙ addIdL (sinℝ quarter · sinℝ h)

    positiveProduct→positiveLeft : ∀ x y →
      0ℝ <ℝ y → 0ℝ <ℝ x · y → 0ℝ <ℝ x
    positiveProduct→positiveLeft x y positive-y positive-product =
      subst (0ℝ <ℝ_)
        (sym (mulAssoc x y reciprocal)
          ∙ cong (x ·_) (positiveReciprocalLaw y positive-y)
          ∙ mulIdR x)
        (mulPositive (x · y) reciprocal positive-product
          (positiveReciprocalPositive y positive-y))
      where
      reciprocal : ℝ
      reciprocal = positiveReciprocal y positive-y

    positiveFromSmallStep : ∀ quarter →
      IsFirstPositiveCosineZero quarter → ∀ h →
      0ℝ <ℝ h → h <ℝ quarter → 0ℝ <ℝ sinℝ h →
      0ℝ <ℝ sinℝ quarter
    positiveFromSmallStep quarter characterization h positive-h h<quarter positive-sine =
      positiveProduct→positiveLeft (sinℝ quarter) (sinℝ h) positive-sine
        (subst (0ℝ <ℝ_)
          (cosineZeroReflection quarter h
            (firstPositiveCosineZero-zero characterization))
          (firstPositiveCosineZero-positive-before characterization
            (quarter + (- h))
            (<ℝ-weaken 0ℝ (quarter - h) (positiveSub h quarter h<quarter))
            (subst (quarter - h <ℝ_) (addIdR quarter)
              (<ℝ-addL (- h) 0ℝ quarter
                (subst ((- h) <ℝ_) negZero (<ℝ-neg 0ℝ h positive-h))))))


-- The sign at the first positive cosine zero is not an extra axiom:
-- choose small 0 < h < quarter with sin(h)>0 and use
-- 0 < cos(quarter-h) = sin(quarter)*sin(h).
opaque
  firstPositiveCosineZero-sinePositive : ∀ quarter →
    IsFirstPositiveCosineZero quarter → 0ℝ <ℝ sinℝ quarter
  firstPositiveCosineZero-sinePositive quarter characterization =
    PT.rec2 (isProp<ℝ 0ℝ (sinℝ quarter)) prove
      (firstPositiveCosineZero-positive characterization)
      sinℝ-positive-near-zero
    where
    prove : PositiveGap 0ℝ quarter →
      (Σ[ δ ∈ ℚ₊ ]
        (∀ (h : ℚ₊) → h <₊ δ → 0ℝ <ℝ sinℝ (rat (fst h)))) →
      0ℝ <ℝ sinℝ quarter
    prove (width , width≤quarter) (δ , sine-positive-near) =
      positiveFromSmallStep quarter characterization (rat (fst step))
        positive-h h<quarter
        (sine-positive-near step (min/2₊<R width δ))
      where
      step : ℚ₊
      step = min₊ width δ /2₊

      h : ℝ
      h = rat (fst step)

      positive-h : 0ℝ <ℝ h
      positive-h = <ℚ→<ℝ 0 (fst step) (snd step)

      h<quarter : h <ℝ quarter
      h<quarter =
        <≤ℝ-trans h (rat (fst width)) quarter
          (<ℚ→<ℝ (fst step) (fst width) (min/2₊<L width δ))
          (subst (_≤ℝ quarter) (addIdL (rat (fst width))) width≤quarter)

  firstPositiveCosineZero-sineOne : ∀ quarter →
    IsFirstPositiveCosineZero quarter → sinℝ quarter ≡ 1ℝ
  firstPositiveCosineZero-sineOne quarter characterization =
    positiveSquareOne→one (sinℝ quarter)
      (firstPositiveCosineZero-sinePositive quarter characterization)
      (cosineZero→sineSquareOne quarter
        (firstPositiveCosineZero-zero characterization))


characterizedHalfPi-sinePositive :
  (construction : CharacterizedHalfPi) →
  CharacterizedHalfPiSinePositive construction
characterizedHalfPi-sinePositive construction =
  firstPositiveCosineZero-sinePositive (fst construction) (snd construction)


characterizedHalfPi-sineOne :
  (construction : CharacterizedHalfPi) → sinℝ (fst construction) ≡ 1ℝ
characterizedHalfPi-sineOne construction =
  firstPositiveCosineZero-sineOne (fst construction) (snd construction)
