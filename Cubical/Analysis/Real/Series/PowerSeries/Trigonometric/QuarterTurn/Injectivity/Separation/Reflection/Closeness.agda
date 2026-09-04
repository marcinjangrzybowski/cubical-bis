module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Closeness where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Metric using (close→upperBound)


open PositiveRationals using (ℚ₊)


private
  addSubCancelLeft : ∀ (x y : ℝ) → (x + y) + (- x) ≡ y
  addSubCancelLeft x y =
    sym (addAssoc x y (- x))
    ∙ cong (x +_) (addComm y (- x))
    ∙ addAssoc x (- x) y
    ∙ cong (_+ y) (addInvR x)
    ∙ addIdL y


opaque
  closeness→reverseDifference≤ : ∀ (x y : ℝ) (radius : ℚ₊) →
    x ∼[ radius ] y → y - x ≤ℝ rat (fst radius)
  closeness→reverseDifference≤ x y radius x-close-y =
    subst (y - x ≤ℝ_)
      (addSubCancelLeft x (rat (fst radius)))
      (addPres≤R
        y (x + rat (fst radius)) (- x)
        (close→upperBound y x radius
          (sym∼ x y radius x-close-y)))
