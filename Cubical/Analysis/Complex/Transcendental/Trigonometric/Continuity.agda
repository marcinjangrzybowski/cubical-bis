module Cubical.Analysis.Complex.Transcendental.Trigonometric.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Continuity
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base

private
  positivePhase negativePhase : ℂ → ℂ
  positivePhase z = expℂ (iℂ ·ℂ z)
  negativePhase z = expℂ (-ℂ (iℂ ·ℂ z))

  positivePhase-continuous : isContinuous (ℂPremetricSpace .snd) positivePhase (ℂPremetricSpace .snd)
  positivePhase-continuous = snd ((expℂ , expℂ-isContinuous) ∘C (iℂ ·ℂ_ , leftMultiplyℂ-isContinuous iℂ))

  negativePhase-continuous : isContinuous (ℂPremetricSpace .snd) negativePhase (ℂPremetricSpace .snd)
  negativePhase-continuous = snd ((expℂ , expℂ-isContinuous) ∘C
    ((λ z → -ℂ (iℂ ·ℂ z)) , negOfComplexContinuous (ℂPremetricSpace .snd)
      (iℂ ·ℂ_) (leftMultiplyℂ-isContinuous iℂ)))

opaque
  unfolding cosℂ sinℂ

  cosℂ-isContinuous : isContinuous (ℂPremetricSpace .snd) cosℂ (ℂPremetricSpace .snd)
  cosℂ-isContinuous = mulOfComplexContinuous (ℂPremetricSpace .snd) (λ _ → halfℂ) _
    (constantℂ-isContinuous (ℂPremetricSpace .snd) halfℂ)
    (addOfComplexContinuous (ℂPremetricSpace .snd) positivePhase negativePhase
      positivePhase-continuous negativePhase-continuous)

  sinℂ-isContinuous : isContinuous (ℂPremetricSpace .snd) sinℂ (ℂPremetricSpace .snd)
  sinℂ-isContinuous = mulOfComplexContinuous (ℂPremetricSpace .snd) (λ _ → (-ℂ iℂ) ·ℂ halfℂ) _
    (constantℂ-isContinuous (ℂPremetricSpace .snd) ((-ℂ iℂ) ·ℂ halfℂ))
    (subOfComplexContinuous (ℂPremetricSpace .snd) positivePhase negativePhase
      positivePhase-continuous negativePhase-continuous)
