module Cubical.Analysis.Real.Integration.FundamentalTheorem.Stability.Estimates where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.Partition.Overlap
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Comparison
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Algebra
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.First

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

opaque
  -- The estimate retains the distance between the endpoints. This is
  -- stronger than uniform convergence of the primitive alone and allows
  -- passage to a derivative without a continuity assumption on its limit.
  integralIncrementsDifferenceBound : ∀ (F G f g : ℝ → ℝ) (a b bound : ℝ) →
    HasIntegralIncrementsOn F f a b → HasIntegralIncrementsOn G g a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z - g z) ≤ℝ bound) →
    ∀ (x y : ClosedInterval a b) →
    absℝ ((F (fst y) - F (fst x)) - (G (fst y) - G (fst x))) ≤ℝ
      bound · absℝ (fst y - fst x)
  integralIncrementsDifferenceBound F G f g a b bound first second bounded
      x@(x₀ , a≤x , x≤b) y@(y₀ , a≤y , y≤b) =
    orderCasesForBound x₀ y₀ (absℝ ((F y₀ - F x₀) - (G y₀ - G x₀)))
      (bound · absℝ (y₀ - x₀))
      (λ x≤y → ordered x₀ y₀ a≤x x≤y y≤b)
      (λ y≤x → subst2 _≤ℝ_
        (cong absℝ (differenceOfDifferences (F x₀) (F y₀) (G x₀) (G y₀))
          ∙ absSubComm (F x₀ - G x₀) (F y₀ - G y₀)
          ∙ cong absℝ (sym (differenceOfDifferences (F y₀) (F x₀) (G y₀) (G x₀))))
        (cong (bound ·_) (absSubComm x₀ y₀))
        (ordered y₀ x₀ a≤y y≤x x≤b))
    where
    ordered : ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b →
      absℝ ((F y - F x) - (G y - G x)) ≤ℝ bound · absℝ (y - x)
    ordered x y a≤x x≤y y≤b =
      subst (absℝ ((F y - F x) - (G y - G x)) ≤ℝ_)
        (mulComm (y - x) bound ∙ cong (bound ·_) (sym (absOfNonnegative (y - x) (nonnegativeSub x y x≤y))))
        (riemannIntegral-differenceBoundOn x y x≤y f g (F y - F x) (G y - G x) bound
          (first x y a≤x x≤y y≤b) (second x y a≤x x≤y y≤b)
          (λ z x≤z z≤y → bounded z (≤ℝ-trans a x z a≤x x≤z) (≤ℝ-trans z y b z≤y y≤b)))

