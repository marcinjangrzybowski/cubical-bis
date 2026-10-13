module Cubical.Analysis.Complex.Integration.Curve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (mulDistL)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference using (closeness→absDifference<)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
import Cubical.Analysis.Real.Calculus.MeanValue.Uniform as Real
import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval as Real
import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Estimates as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.RealParameter

IsUniformComplexCurveDerivativeOn : (ℝ → ℂ) → (ℝ → ℂ) → ℝ → ℝ → Type₀
IsUniformComplexCurveDerivativeOn curve velocity a b =
  Real.IsRadiuswiseUniformDerivativeOn (re ∘ curve) (re ∘ velocity) a b ×
  Real.IsRadiuswiseUniformDerivativeOn (im ∘ curve) (im ∘ velocity) a b

uniformCurveDerivativeOn→along : ∀ curve velocity a b → IsUniformComplexCurveDerivativeOn curve velocity a b →
  IsRadiuswiseUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
    (fromℝ ∘ fst) (curve ∘ fst) (velocity ∘ fst)
uniformCurveDerivativeOn→along curve velocity a b derivative =
  uniformRealCoordinates→complexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst
    (curve ∘ fst) (velocity ∘ fst)
    (Real.uniformDerivativeOn→alongInterval (re ∘ curve) (re ∘ velocity) a b (fst derivative))
    (Real.uniformDerivativeOn→alongInterval (im ∘ curve) (im ∘ velocity) a b (snd derivative))

uniformCurveDerivativeAlong→on : ∀ curve velocity a b →
  IsRadiuswiseUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
    (fromℝ ∘ fst) (curve ∘ fst) (velocity ∘ fst) → IsUniformComplexCurveDerivativeOn curve velocity a b
uniformCurveDerivativeAlong→on curve velocity a b derivative =
  Real.uniformDerivativeAlongInterval→on (re ∘ curve) (re ∘ velocity) a b (fst coordinates) ,
  Real.uniformDerivativeAlongInterval→on (im ∘ curve) (im ∘ velocity) a b (snd coordinates)
  where
  coordinates = uniformComplexDerivativeAlong→realCoordinates (ClosedIntervalPremetricSpace a b .snd)
    fst (curve ∘ fst) (velocity ∘ fst) derivative

opaque
  -- The two existing real mean-value bounds give a uniform complex bound.
  -- The factor two is harmless and avoids a new vector mean-value theorem.
  uniformComplexCurveLipschitzOn : ∀ curve velocity a b (B : ℚ₊) →
    IsUniformComplexCurveDerivativeOn curve velocity a b →
    (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (velocity t) ≤ℝ rat (fst B)) →
    ∀ (x y : ClosedInterval a b) → normℂ (curve (fst y) -ℂ curve (fst x)) ≤ℝ
      rat (fst (B +₊ B)) · absℝ (fst y - fst x)
  uniformComplexCurveLipschitzOn curve velocity a b B derivative bounded x y =
    subst (normℂ (curve (fst y) -ℂ curve (fst x)) ≤ℝ_)
      (sym (mulDistL (rat (fst B)) (rat (fst B)) (absℝ (fst y - fst x)))
        ∙ cong (_· absℝ (fst y - fst x)) (rat+rat (fst B) (fst B)))
      (addPres≤ (absℝ (re (curve (fst y)) - re (curve (fst x))))
        (rat (fst B) · absℝ (fst y - fst x))
        (absℝ (im (curve (fst y)) - im (curve (fst x))))
        (rat (fst B) · absℝ (fst y - fst x))
        (Real.uniformDerivativeLipschitzOn (re ∘ curve) (re ∘ velocity) a b (rat (fst B)) (fst derivative)
          (λ t lower upper → ≤ℝ-trans (absℝ (re (velocity t))) (normℂ (velocity t)) (rat (fst B))
            (reAbs≤normℂ (velocity t)) (bounded t lower upper)) x y)
        (Real.uniformDerivativeLipschitzOn (im ∘ curve) (im ∘ velocity) a b (rat (fst B)) (snd derivative)
          (λ t lower upper → ≤ℝ-trans (absℝ (im (velocity t))) (normℂ (velocity t)) (rat (fst B))
            (imAbs≤normℂ (velocity t)) (bounded t lower upper)) x y))

  uniformComplexCurveIsUniformlyContinuousOn : ∀ curve velocity a b (B : ℚ₊) →
    IsUniformComplexCurveDerivativeOn curve velocity a b →
    (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (velocity t) ≤ℝ rat (fst B)) →
    isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (curve ∘ fst) (ℂPremetricSpace .snd)
  uniformComplexCurveIsUniformlyContinuousOn curve velocity a b B derivative bounded =
    ∣ (λ ε → ε ₊／₊ (B +₊ B)) , isuniformlycontinuouswith (λ x y ε close →
      rationalLinearBoundGivesCloseness (curve (fst x)) (curve (fst y))
        (absℝ (fst y - fst x)) (B +₊ B) ε
        (uniformComplexCurveLipschitzOn curve velocity a b B derivative bounded x y)
        (closeness→absDifference< (fst y) (fst x) (ε ₊／₊ (B +₊ B))
          (sym∼ (fst x) (fst y) (ε ₊／₊ (B +₊ B)) close))) ∣₁
