module Cubical.Analysis.Complex.Integration.Path.Vertical where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdL)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absZero; absOne)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ; mulIdL)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Basic using (constantHasUniformDerivativeAlong)
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Affine
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Integration.Path

verticalComplexPath : ∀ a b → a ≤ℝ b → UniformComplexPath a b
verticalComplexPath a b ordered .UniformComplexPath.ordered = ordered
verticalComplexPath a b ordered .UniformComplexPath.curve t = 0ℝ , t
verticalComplexPath a b ordered .UniformComplexPath.velocity t = iℂ
verticalComplexPath a b ordered .UniformComplexPath.differentiable =
  uniformDerivativeAlongInterval→on (λ _ → 0ℝ) (λ _ → 0ℝ) a b
    (constantHasUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst 0ℝ) ,
  uniformDerivativeAlongInterval→on (λ t → t) (λ _ → 1ℝ) a b
    (exactDifferenceGivesUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst fst (λ _ → 1ℝ)
      (λ x y → sym (mulIdL (fst y - fst x))))
verticalComplexPath a b ordered .UniformComplexPath.speedBound = 1₊
verticalComplexPath a b ordered .UniformComplexPath.boundedSpeed t lo hi =
  subst (_≤ℝ 1ℝ) (sym (cong₂ _+_ absZero absOne ∙ addIdL 1ℝ)) (≤ℝ-refl 1ℝ)
