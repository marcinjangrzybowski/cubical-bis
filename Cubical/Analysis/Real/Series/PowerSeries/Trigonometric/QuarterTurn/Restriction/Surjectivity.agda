module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Surjectivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


-- This is the exact intermediate-value statement still required for
-- surjectivity.  Keeping it separate from `isSurjection` makes the analytic
-- obligation independent of subtype equality bookkeeping.

SineQuarterIntermediateValue : ℝ → Type₀
SineQuarterIntermediateValue quarter =
  ∀ y → (- 1ℝ) ≤ℝ y → y ≤ℝ 1ℝ →
    ∥ Σ[ point ∈ SineQuarterInterval quarter ]
        sinℝ (fst point) ≡ y ∥₁


isPropSineQuarterIntermediateValue : ∀ quarter →
  isProp (SineQuarterIntermediateValue quarter)
isPropSineQuarterIntermediateValue quarter =
  isPropΠ3 λ _ _ _ → squash₁


opaque
  sineQuarterIntermediateValue→restrictedSineSurjective :
    ∀ quarter →
    SineQuarterIntermediateValue quarter →
    isSurjection (restrictedSine quarter)
  sineQuarterIntermediateValue→restrictedSineSurjective
      quarter intermediate target =
    PT.map
      (λ (point , sine-value) →
        point
        , sineUnitInterval≡ _ target
            (restrictedSine-value quarter point ∙ sine-value))
      (intermediate
        (fst target)
        (fst (snd target))
        (snd (snd target)))


  restrictedSineSurjective→sineQuarterIntermediateValue :
    ∀ quarter →
    isSurjection (restrictedSine quarter) →
    SineQuarterIntermediateValue quarter
  restrictedSineSurjective→sineQuarterIntermediateValue
      quarter surjective y lower upper =
    PT.map
      (λ (point , image-path) →
        point
        , sym (restrictedSine-value quarter point)
          ∙ cong fst image-path)
      (surjective (y , lower , upper))


restrictedSineSurjective≃SineQuarterIntermediateValue : ∀ quarter →
  isSurjection (restrictedSine quarter)
    ≃ SineQuarterIntermediateValue quarter
restrictedSineSurjective≃SineQuarterIntermediateValue quarter =
  propBiimpl→Equiv
    isPropIsSurjection
    (isPropSineQuarterIntermediateValue quarter)
    (restrictedSineSurjective→sineQuarterIntermediateValue quarter)
    (sineQuarterIntermediateValue→restrictedSineSurjective quarter)
