module Cubical.Analysis.Real.Integration.FundamentalTheorem.First where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Relation.Premetric.Mappings using (isContinuous; IsContinuousAt)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Lattice
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Constant
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Sub
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Algebra
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Interval
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.IntegralBound
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Second


-- The semantic property of an accumulation function.  Only ordered
-- subintervals are used: the raw integral predicate is vacuous in reverse.
HasIntegralIncrementsOn : (F f : ℝ → ℝ) → ℝ → ℝ → Type₀
HasIntegralIncrementsOn F f a b =
  ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b →
    HasRiemannIntegralOn f x y (F y - F x)

isPropHasIntegralIncrementsOn : ∀ F f a b →
  isProp (HasIntegralIncrementsOn F f a b)
isPropHasIntegralIncrementsOn F f a b =
  isPropΠ λ x → isPropΠ λ y → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ →
    isPropHasRiemannIntegralOn f x y (F y - F x)


-- The quantitative first theorem only uses continuity at the base point.
integralIncrementsRemainderBound : ∀ F f a b (ε δ : ℚ₊) x y →
  HasIntegralIncrementsOn F f a b →
  a ≤ℝ x → x ≤ℝ b → a ≤ℝ y → y ≤ℝ b →
  (∀ t → a ≤ℝ t → t ≤ℝ b →
    x ∼[ δ ] t → f x ∼[ ε /2₊ ] f t) →
  x ∼[ δ ] y →
  absℝ ((F y - F x) - f x · (y - x))
    ≤ℝ rat (fst ε) · absℝ (y - x)
integralIncrementsRemainderBound F f a b ε δ x y increments
    a≤x x≤b a≤y y≤b continuous x∼y =
  subst2 _≤ℝ_
    (cong absℝ (remainderThrough (F x) (F y) (F m) (f x) x y m))
    (sym (mulDistL e e distance)
      ∙ cong (_· distance)
          (rat+rat (fst (ε /2₊)) (fst (ε /2₊))
            ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε))))
    (≤ℝ-trans (absℝ (error y - error x))
      (absℝ (error y) + absℝ (error x))
      (e · distance + e · distance)
      (absSubTriangle (error y) (error x))
      (addPres≤ (absℝ (error y)) (e · distance)
        (absℝ (error x)) (e · distance)
        (errorBound y m≤y y≤b (right≤max x y)
          (subst2 _≤ℝ_
            (cong (y -_) (minComm y x)) (absSubComm x y)
            (minEndpointDistanceBound y x)))
        (errorBound x m≤x x≤b (left≤max x y)
          (minEndpointDistanceBound x y))))
  where
  m = minℝ x y
  distance = absℝ (y - x)
  e = rat (fst (ε /2₊))
  error : ℝ → ℝ
  error z = (F z - F m) - f x · (z - m)

  m≤x = min≤left x y
  m≤y = min≤right x y
  a≤m = minGreatestLowerBound x y a a≤x a≤y

  pointwise : ∀ z → m ≤ℝ z → z ≤ℝ b → z ≤ℝ maxℝ x y →
    ∀ t → m ≤ℝ t → t ≤ℝ z → absℝ (f t - f x) ≤ℝ e
  pointwise z m≤z z≤b z≤max t m≤t t≤z =
    subst (_≤ℝ e) (absSubComm (f x) (f t))
      (<ℝ-weaken (absℝ (f x - f t)) e
        (closeness→absDifference< (f x) (f t) (ε /2₊)
          (continuous t
            (≤ℝ-trans a m t a≤m m≤t)
            (≤ℝ-trans t z b t≤z z≤b)
            (absDifference<→closeness x t δ
              (subst (_<ℝ rat (fst δ)) (absSubComm t x)
                (≤<ℝ-trans (absℝ (t - x)) distance (rat (fst δ))
                  (betweenEndpointsDistanceBound x y t m≤t
                    (≤ℝ-trans t z (maxℝ x y) t≤z z≤max))
                  (subst (_<ℝ rat (fst δ)) (absSubComm x y)
                    (closeness→absDifference< x y δ x∼y))))))))

  errorIntegral : ∀ z → m ≤ℝ z → z ≤ℝ b →
    HasRiemannIntegralOn (λ t → f t - f x) m z (error z)
  errorIntegral z m≤z z≤b =
    subHasRiemannIntegral f (λ _ → f x) (F z - F m) (f x · (z - m))
      (increments m z a≤m m≤z z≤b)
      (subst (HasRiemannIntegralOn (λ _ → f x) m z)
        (mulComm (z - m) (f x)) (constantHasRiemannIntegral m z (f x)))

  errorBound : ∀ z → m ≤ℝ z → z ≤ℝ b → z ≤ℝ maxℝ x y →
    z - m ≤ℝ distance → absℝ (error z) ≤ℝ e · distance
  errorBound z m≤z z≤b z≤max length≤distance =
    ≤ℝ-trans (absℝ (error z)) ((z - m) · e) (e · distance)
      (riemannIntegral-absBoundOn m z m≤z (λ t → f t - f x)
        (error z) e (errorIntegral z m≤z z≤b)
        (pointwise z m≤z z≤b z≤max))
      (subst (((z - m) · e) ≤ℝ_) (mulComm distance e)
        (mulPres≤R-0≤ (z - m) distance e
          (ratPositiveNonnegative (ε /2₊)) length≤distance))
    where
    ratPositiveNonnegative : ∀ (ρ : ℚ₊) → 0ℝ ≤ℝ rat (fst ρ)
    ratPositiveNonnegative ρ =
      <ℝ-weaken 0ℝ (rat (fst ρ)) (<ℚ→<ℝ 0 (fst ρ) (snd ρ))


opaque
  fundamentalTheoremOfCalculusFirstOn : ∀ F f a b →
    IsRadiuswiseUniformlyContinuous
      (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) →
    HasIntegralIncrementsOn F f a b →
    IsRadiuswiseUniformDerivativeOn F f a b
  fundamentalTheoremOfCalculusFirstOn F f a b continuous increments ε =
    PT.map (λ { (δ , close) → δ , λ x y a≤x x≤b a≤y y≤b x∼y →
      integralIncrementsRemainderBound F f a b ε δ x y increments
        a≤x x≤b a≤y y≤b
        (λ t a≤t t≤b → close (x , a≤x , x≤b) (t , a≤t , t≤b)) x∼y })
      (continuous (ε /2₊))

  fundamentalTheoremOfCalculusFirst : ∀ F f a b →
    IsRadiuswiseUniformlyContinuousℝ f →
    HasIntegralIncrementsOn F f a b →
    IsRadiuswiseUniformDerivativeOn F f a b
  fundamentalTheoremOfCalculusFirst F f a b continuous increments ε =
    PT.map (λ { (δ , close) → δ , λ x y a≤x x≤b a≤y y≤b x∼y →
      integralIncrementsRemainderBound F f a b ε δ x y increments
        a≤x x≤b a≤y y≤b (λ t _ _ → close x t) x∼y })
      (continuous (ε /2₊))

  -- Pointwise continuity suffices for the pointwise first theorem, including
  -- the relative (one-sided) derivatives at the interval endpoints.
  integralIncrementsHaveDerivativeAlong : ∀ F f a b →
    isContinuous (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd) →
    HasIntegralIncrementsOn F f a b →
    IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
      fst (F ∘ fst) (f ∘ fst)
  integralIncrementsHaveDerivativeAlong F f a b continuous increments
      (x , a≤x , x≤b) ε =
    PT.map (λ { (δ , close) → δ , λ (y , a≤y , y≤b) x∼y →
      integralIncrementsRemainderBound F f a b ε δ x y increments
        a≤x x≤b a≤y y≤b (λ t a≤t t≤b → close (t , a≤t , t≤b)) x∼y })
      (continuous (x , a≤x , x≤b) .IsContinuousAt.pres≈ (ε /2₊))

  uniformDerivativeHasIntegralIncrements : ∀ F f a b →
    IsRadiuswiseUniformDerivativeOn F f a b →
    HasIntegralIncrementsOn F f a b
  uniformDerivativeHasIntegralIncrements F f a b derivative x y a≤x x≤y y≤b =
    fundamentalTheoremOfCalculusSecond F f x y
      (radiuswiseUniformDerivativeOn→subinterval F f a b x y a≤x y≤b derivative)

  uniformDerivative≃integralIncrements : ∀ F f a b →
    IsRadiuswiseUniformlyContinuous
      (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) →
    IsRadiuswiseUniformDerivativeOn F f a b ≃ HasIntegralIncrementsOn F f a b
  uniformDerivative≃integralIncrements F f a b continuous =
    propBiimpl→Equiv
      (isPropIsRadiuswiseUniformDerivativeOn F f a b)
      (isPropHasIntegralIncrementsOn F f a b)
      (uniformDerivativeHasIntegralIncrements F f a b)
      (fundamentalTheoremOfCalculusFirstOn F f a b continuous)
