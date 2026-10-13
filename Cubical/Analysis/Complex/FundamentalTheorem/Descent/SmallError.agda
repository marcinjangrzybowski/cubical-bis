module Cubical.Analysis.Complex.FundamentalTheorem.Descent.SmallError where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; min₊; min₊≤L; min₊≤R)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication

-- Three positive gaps suffice to choose one rational error. This is
-- finite truncation elimination, not a selection indexed by accuracies.
smallPositiveRational3 : ∀ x y z → 0ℝ <ℝ x → 0ℝ <ℝ y → 0ℝ <ℝ z →
  ∥ Σ[ ε ∈ ℚ₊ ] (rat (fst ε) ≤ℝ x) × (rat (fst ε) ≤ℝ y) × (rat (fst ε) ≤ℝ z) ∥₁
smallPositiveRational3 x y z x-positive y-positive z-positive =
  PT.map2 combine (PT.map2 _,_ x-positive y-positive) z-positive
  where
  combine : (PositiveGap 0ℝ x × PositiveGap 0ℝ y) → PositiveGap 0ℝ z →
    Σ[ ε ∈ ℚ₊ ] (rat (fst ε) ≤ℝ x) × (rat (fst ε) ≤ℝ y) × (rat (fst ε) ≤ℝ z)
  combine ((ε , ε-bound) , (δ , δ-bound)) (η , η-bound) = μ ,
    ≤ℝ-trans (rat (fst μ)) (rat (fst ε)) x μ≤ε (subst (_≤ℝ x) (addIdL (rat (fst ε))) ε-bound) ,
    ≤ℝ-trans (rat (fst μ)) (rat (fst δ)) y
      (≤ℝ-trans (rat (fst μ)) (rat (fst ν)) (rat (fst δ)) μ≤ν
        (invEq (rat≤rat≃ (fst ν) (fst δ)) (min₊≤L δ η)))
      (subst (_≤ℝ y) (addIdL (rat (fst δ))) δ-bound) ,
    ≤ℝ-trans (rat (fst μ)) (rat (fst η)) z
      (≤ℝ-trans (rat (fst μ)) (rat (fst ν)) (rat (fst η)) μ≤ν
        (invEq (rat≤rat≃ (fst ν) (fst η)) (min₊≤R δ η)))
      (subst (_≤ℝ z) (addIdL (rat (fst η))) η-bound)
    where
    ν = min₊ δ η
    μ = min₊ ε ν
    μ≤ε = invEq (rat≤rat≃ (fst μ) (fst ε)) (min₊≤L ε ν)
    μ≤ν = invEq (rat≤rat≃ (fst μ) (fst ν)) (min₊≤R ε ν)

smallPositiveRationalWithMultiple : ∀ x y multiplier budget →
  0ℝ <ℝ x → 0ℝ <ℝ y → 0ℝ <ℝ multiplier → 0ℝ <ℝ budget →
  ∥ Σ[ ε ∈ ℚ₊ ] (rat (fst ε) ≤ℝ x) × (rat (fst ε) ≤ℝ y) ×
    (multiplier · rat (fst ε) ≤ℝ budget) ∥₁
smallPositiveRationalWithMultiple x y multiplier budget x-positive y-positive multiplier-positive budget-positive =
  PT.map fromBound (smallPositiveRational3 x y divided-budget x-positive y-positive
    (mulPositive reciprocal budget (positiveReciprocalPositive multiplier multiplier-positive) budget-positive))
  where
  reciprocal = positiveReciprocal multiplier multiplier-positive
  divided-budget = reciprocal · budget

  cancel : multiplier · divided-budget ≡ budget
  cancel = mulAssoc multiplier reciprocal budget
    ∙ cong (_· budget) (positiveReciprocalLaw multiplier multiplier-positive) ∙ mulIdL budget

  fromBound : (Σ[ ε ∈ ℚ₊ ] (rat (fst ε) ≤ℝ x) × (rat (fst ε) ≤ℝ y) ×
      (rat (fst ε) ≤ℝ divided-budget)) →
    Σ[ ε ∈ ℚ₊ ] (rat (fst ε) ≤ℝ x) × (rat (fst ε) ≤ℝ y) × (multiplier · rat (fst ε) ≤ℝ budget)
  fromBound (ε , first , second , third) = ε , first , second ,
    subst (multiplier · rat (fst ε) ≤ℝ_) cancel
      (mulPres≤L (rat (fst ε)) divided-budget multiplier
        (0≤→isNonnegative multiplier (<ℝ-weaken 0ℝ multiplier multiplier-positive)) third)
