module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.PositiveNearZero where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire

open PositiveRationals
open PositiveHalvesℚ


private
  half : ℚ₊
  half = 1₊ /2₊

  opaque
    smallRelativeError→positive : ∀ value x error-bound →
      absℝ (value - x) ≤ℝ error-bound →
      error-bound <ℝ x → 0ℝ <ℝ value
    smallRelativeError→positive value x error-bound bounded below =
      <ℝ-addL-cancel 0ℝ value error-bound
        (subst (_<ℝ error-bound + value) (sym (addIdR error-bound))
          (<≤ℝ-trans error-bound x (error-bound + value) below
            (subst (_≤ℝ error-bound + value)
              (sym (addAssoc x (- value) value)
                ∙ cong (x +_) (addInvL value) ∙ addIdR x)
              (addPres≤R (x - value) error-bound value
                (≤ℝ-trans (x - value) (absℝ (x - value)) error-bound
                  (leAbs (x - value))
                  (subst (_≤ℝ error-bound) (absSubComm value x) bounded))))))

    sineErrorAtZero : ∀ x →
      ((sinℝ x - sinℝ 0ℝ) - cosℝ 0ℝ · (x - 0ℝ)) ≡ sinℝ x - x
    sineErrorAtZero x =
      cong₂ _-_
        (cong (λ z → sinℝ x - z) sinℝ-zero ∙ subZero (sinℝ x))
        (cong₂ _·_ cosℝ-zero (subZero x) ∙ mulIdL x)

    positiveRatNearZero : ∀ (h δ : ℚ₊) →
      h <₊ δ → 0ℝ ∼[ δ ] rat (fst h)
    positiveRatNearZero h δ h<δ =
      absDifference<→closeness 0ℝ (rat (fst h)) δ
        (subst (_<ℝ rat (fst δ))
          (sym (cong absℝ (zeroSub (rat (fst h)))
            ∙ absNeg (rat (fst h))
            ∙ absOfNonnegative (rat (fst h))
                (<ℝ-weaken 0ℝ (rat (fst h))
                  (<ℚ→<ℝ 0 (fst h) (snd h)))))
          (<ℚ→<ℝ (fst h) (fst δ) h<δ))


-- This local sign follows just from sin(0)=0 and sin'(0)=1.  It does not
-- depend on pi, a quarter turn, or an intermediate-value principle.
opaque
  sinℝ-positive-near-zero :
    ∥ Σ[ δ ∈ ℚ₊ ]
      (∀ (h : ℚ₊) → h <₊ δ → 0ℝ <ℝ sinℝ (rat (fst h))) ∥₁
  sinℝ-positive-near-zero =
    PT.map
      (λ (δ , error-near) → δ , λ h h<δ →
        positive-from-error (rat (fst h)) (<ℚ→<ℝ 0 (fst h) (snd h))
          (error-near (rat (fst h)) (positiveRatNearZero h δ h<δ)))
      (sinℝHasDerivative 0ℝ half)
    where
    positive-from-error : ∀ x → 0ℝ <ℝ x →
      absℝ ((sinℝ x - sinℝ 0ℝ) - cosℝ 0ℝ · (x - 0ℝ)) ≤ℝ
      rat (fst half) · absℝ (x - 0ℝ) → 0ℝ <ℝ sinℝ x
    positive-from-error x positive bounded =
      smallRelativeError→positive (sinℝ x) x (rat (fst half) · x)
        (subst2 _≤ℝ_
          (cong absℝ (sineErrorAtZero x))
          (cong (rat (fst half) ·_)
            (cong absℝ (subZero x)
              ∙ absOfNonnegative x (<ℝ-weaken 0ℝ x positive))) bounded)
        (subst (rat (fst half) · x <ℝ_) (mulIdL x)
          (mulPres<PosR (rat (fst half)) 1ℝ x positive
            (<ℚ→<ℝ (fst half) 1 (/2₊<id 1₊))))
