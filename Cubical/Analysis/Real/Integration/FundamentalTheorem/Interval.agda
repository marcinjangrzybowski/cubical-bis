module Cubical.Analysis.Real.Integration.FundamentalTheorem.Interval where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue


opaque
  maxEndpointDistanceBound : ∀ x y →
    maxℝ x y - x ≤ℝ absℝ (y - x)
  maxEndpointDistanceBound x y =
    subst (_≤ℝ absℝ (y - x))
      (sym (addMax x y (- x)
        ∙ cong (λ t → maxℝ t (y - x)) (subSelf x)))
      (maxLeastUpperBound 0ℝ (y - x) (absℝ (y - x))
        (absNonnegative (y - x)) (leAbs (y - x)))

  minEndpointDistanceBound : ∀ x y →
    x - minℝ x y ≤ℝ absℝ (y - x)
  minEndpointDistanceBound x y =
    subst2 _≤ℝ_
      (sym
        (cong (x +_) (negInvol (maxℝ (- x) (- y)))
          ∙ addComm x (maxℝ (- x) (- y))
          ∙ addMax (- x) (- y) x
          ∙ cong₂ maxℝ (addInvL x) (addComm (- y) x)))
      (absSubComm x y)
      (maxLeastUpperBound 0ℝ (x - y) (absℝ (x - y))
        (absNonnegative (x - y)) (leAbs (x - y)))

  -- This uses lattice bounds, so it never decides which endpoint is larger.
  betweenEndpointsDistanceBound : ∀ x y t →
    minℝ x y ≤ℝ t → t ≤ℝ maxℝ x y →
    absℝ (t - x) ≤ℝ absℝ (y - x)
  betweenEndpointsDistanceBound x y t min≤t t≤max =
    absLeastUpperBound (t - x) (absℝ (y - x))
      (≤ℝ-trans (t - x) (maxℝ x y - x) (absℝ (y - x))
        (addPres≤R t (maxℝ x y) (- x) t≤max)
        (maxEndpointDistanceBound x y))
      (subst (_≤ℝ absℝ (y - x)) (sym (negSub t x))
        (≤ℝ-trans (x - t) (x - minℝ x y) (absℝ (y - x))
          (addPres≤L (- t) (- minℝ x y) x
            (negPres≤ (minℝ x y) t min≤t))
          (minEndpointDistanceBound x y)))
