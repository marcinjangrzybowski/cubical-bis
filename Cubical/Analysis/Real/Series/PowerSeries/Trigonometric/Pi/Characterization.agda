module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


-- This is the constructive characterization targeted by Bishop's
-- approximation: the first positive zero of cosine, with positivity on the
-- whole preceding nonnegative interval recorded as data.

IsFirstPositiveCosineZero : ℝ → Type₀
IsFirstPositiveCosineZero half =
  (0ℝ <ℝ half) ×
  (cosℝ half ≡ 0ℝ) ×
  (∀ x → 0ℝ ≤ℝ x → x <ℝ half → 0ℝ <ℝ cosℝ x)


isPropIsFirstPositiveCosineZero : ∀ half →
  isProp (IsFirstPositiveCosineZero half)
isPropIsFirstPositiveCosineZero half =
  isProp×
    (isProp<ℝ 0ℝ half)
    (isProp×
      (isSetℝ (cosℝ half) 0ℝ)
      (isPropΠ λ x →
        isPropΠ λ _ →
          isPropΠ λ _ → isProp<ℝ 0ℝ (cosℝ x)))


firstPositiveCosineZero-positive : ∀ {half} →
  IsFirstPositiveCosineZero half → 0ℝ <ℝ half
firstPositiveCosineZero-positive = fst


firstPositiveCosineZero-zero : ∀ {half} →
  IsFirstPositiveCosineZero half → cosℝ half ≡ 0ℝ
firstPositiveCosineZero-zero characterization =
  fst (snd characterization)


firstPositiveCosineZero-positive-before : ∀ {half} →
  IsFirstPositiveCosineZero half →
  ∀ x → 0ℝ ≤ℝ x → x <ℝ half → 0ℝ <ℝ cosℝ x
firstPositiveCosineZero-positive-before characterization =
  snd (snd characterization)


IsLeastNonnegativeCosineZero : ℝ → Type₀
IsLeastNonnegativeCosineZero half =
  (0ℝ ≤ℝ half) ×
  (cosℝ half ≡ 0ℝ) ×
  (∀ x → 0ℝ ≤ℝ x → cosℝ x ≡ 0ℝ → half ≤ℝ x)


isPropIsLeastNonnegativeCosineZero : ∀ half →
  isProp (IsLeastNonnegativeCosineZero half)
isPropIsLeastNonnegativeCosineZero half =
  isProp×
    (isProp≤ℝ 0ℝ half)
    (isProp×
      (isSetℝ (cosℝ half) 0ℝ)
      (isPropΠ λ x →
        isPropΠ λ _ →
          isPropΠ λ _ → isProp≤ℝ half x))


firstPositiveCosineZero→leastNonnegativeCosineZero : ∀ {half} →
  IsFirstPositiveCosineZero half →
  IsLeastNonnegativeCosineZero half
firstPositiveCosineZero→leastNonnegativeCosineZero
    characterization =
  <ℝ-weaken 0ℝ _
    (firstPositiveCosineZero-positive characterization)
  , firstPositiveCosineZero-zero characterization
  , λ x 0≤x cosx≡0 →
      notGreater→≤ℝ _ _ λ x<half →
        <ℝ-irrefl 0ℝ
          (subst
            (0ℝ <ℝ_)
            cosx≡0
            (firstPositiveCosineZero-positive-before
              characterization x 0≤x x<half))


opaque
  firstPositiveCosineZero-unique : ∀ {left right} →
    IsFirstPositiveCosineZero left →
    IsFirstPositiveCosineZero right →
    left ≡ right
  firstPositiveCosineZero-unique {left} {right}
      left-characterization right-characterization =
    ≤ℝ-antisym left right
      (snd (snd
        (firstPositiveCosineZero→leastNonnegativeCosineZero
          left-characterization))
        right
        (<ℝ-weaken 0ℝ right
          (firstPositiveCosineZero-positive right-characterization))
        (firstPositiveCosineZero-zero right-characterization))
      (snd (snd
        (firstPositiveCosineZero→leastNonnegativeCosineZero
          right-characterization))
        left
        (<ℝ-weaken 0ℝ left
          (firstPositiveCosineZero-positive left-characterization))
        (firstPositiveCosineZero-zero left-characterization))
