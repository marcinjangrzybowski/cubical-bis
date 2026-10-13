module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.NonExpanding where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.Partition.Overlap
  using (orderCasesForBound)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.UniformDerivative

private
  opaque
    unitDerivativeDifferenceBound : ∀ f f′ →
      IsRadiuswiseUniformDerivative f f′ →
      (∀ x → absℝ (f′ x) ≤ℝ 1ℝ) →
      ∀ x y → absℝ (f x - f y) ≤ℝ absℝ (x - y)
    unitDerivativeDifferenceBound f f′ derivative bound x y =
      orderCasesForBound x y (absℝ (f x - f y)) (absℝ (x - y))
        (λ x≤y → subst2 _≤ℝ_
          (absSubComm (f y) (f x))
          (mulIdL (y - x) ∙ sym (absOfNonnegative (y - x)
            (nonnegativeSub x y x≤y)) ∙ absSubComm y x)
          (radiuswiseUniformDerivativeBound f f′ derivative x y x≤y 1ℝ bound))
        (λ y≤x → subst (absℝ (f x - f y) ≤ℝ_)
          (mulIdL (x - y) ∙ sym (absOfNonnegative (x - y)
            (nonnegativeSub y x y≤x)))
          (radiuswiseUniformDerivativeBound f f′ derivative y x y≤x 1ℝ bound))

    differenceBound→nonExpanding : ∀ f →
      (∀ x y → absℝ (f x - f y) ≤ℝ absℝ (x - y)) →
      IsNonExpanding (snd ℝPremetricSpace) f (snd ℝPremetricSpace)
    differenceBound→nonExpanding f bound .IsNonExpanding.pres≈ x y ε close =
      absDifference<→closeness (f x) (f y) ε
        (≤<ℝ-trans (absℝ (f x - f y)) (absℝ (x - y)) (rat (fst ε))
          (bound x y) (closeness→absDifference< x y ε close))

opaque
  sinℝ-difference-bound : ∀ x y →
    absℝ (sinℝ x - sinℝ y) ≤ℝ absℝ (x - y)
  sinℝ-difference-bound = unitDerivativeDifferenceBound sinℝ cosℝ
    sinℝHasUniformDerivative cosℝ-abs≤one

  cosℝ-difference-bound : ∀ x y →
    absℝ (cosℝ x - cosℝ y) ≤ℝ absℝ (x - y)
  cosℝ-difference-bound = unitDerivativeDifferenceBound cosℝ (λ x → - sinℝ x)
    cosℝHasUniformDerivative
    (λ x → subst (_≤ℝ 1ℝ) (sym (absNeg (sinℝ x))) (sinℝ-abs≤one x))

  sinℝ-isNonExpanding :
    IsNonExpanding (snd ℝPremetricSpace) sinℝ (snd ℝPremetricSpace)
  sinℝ-isNonExpanding = differenceBound→nonExpanding sinℝ sinℝ-difference-bound

  cosℝ-isNonExpanding :
    IsNonExpanding (snd ℝPremetricSpace) cosℝ (snd ℝPremetricSpace)
  cosℝ-isNonExpanding = differenceBound→nonExpanding cosℝ cosℝ-difference-bound

  sinℝ-abs≤abs : ∀ x → absℝ (sinℝ x) ≤ℝ absℝ x
  sinℝ-abs≤abs x = subst2 _≤ℝ_
    (cong absℝ (cong (λ z → sinℝ x - z) sinℝ-zero ∙ subZero (sinℝ x)))
    (cong absℝ (subZero x)) (sinℝ-difference-bound x 0ℝ)
