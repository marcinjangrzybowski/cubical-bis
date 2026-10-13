module Cubical.Analysis.Real.Integration.FundamentalTheorem.Accumulation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings using (isContinuous)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Concatenation
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.First
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Second


-- Existence is supplied, not inferred from radiuswise continuity.  Every
-- ordered integral is unique, so this is a proposition, not a choice schema.
IsIntegrableOnSubintervals : (ℝ → ℝ) → ℝ → ℝ → Type₀
IsIntegrableOnSubintervals f a b =
  ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b → IsRiemannIntegrableOn f x y

isPropIsIntegrableOnSubintervals : ∀ f a b →
  isProp (IsIntegrableOnSubintervals f a b)
isPropIsIntegrableOnSubintervals f a b =
  isPropΠ λ x → isPropΠ λ y → isPropΠ λ _ → isPropΠ λ x≤y → isPropΠ λ _ →
    isPropIsRiemannIntegrableOn x y x≤y f

uniformDerivativeIsIntegrableOnSubintervals : ∀ F f a b →
  IsRadiuswiseUniformDerivativeOn F f a b → IsIntegrableOnSubintervals f a b
uniformDerivativeIsIntegrableOnSubintervals F f a b derivative x y a≤x x≤y y≤b =
  (F y - F x) , uniformDerivativeHasIntegralIncrements F f a b derivative x y a≤x x≤y y≤b


module Accumulation (f : ℝ → ℝ) (a b : ℝ) (a≤b : a ≤ℝ b)
    (integrable : IsIntegrableOnSubintervals f a b) where

  -- The actual integral from the lower endpoint, on the closed interval.
  opaque
    value : ClosedInterval a b → ℝ
    value (x , a≤x , x≤b) = fst (integrable a x (≤ℝ-refl a) a≤x x≤b)

    hasValue : ∀ point → HasRiemannIntegralOn f a (fst point) (value point)
    hasValue (x , a≤x , x≤b) = snd (integrable a x (≤ℝ-refl a) a≤x x≤b)

  private
    -- An ambient extension lets the interval theorem avoid transporting
    -- proof-indexed values during its analytic estimates.
    opaque
      extendedValue : ℝ → ℝ
      extendedValue x = value
        (clampInterval a b x , clampIntervalLowerBound a b x
          , clampIntervalUpperBound a b a≤b x)

      agrees : ∀ point → extendedValue (fst point) ≡ value point
      agrees (x , a≤x , x≤b) = cong value
        (Σ≡Prop (isPropClosedIntervalMembership a b)
          (clampIntervalFix a b x a≤x x≤b))

  opaque
    private
      extendedHasValue : ∀ x → (a≤x : a ≤ℝ x) → (x≤b : x ≤ℝ b) →
        HasRiemannIntegralOn f a x (extendedValue x)
      extendedHasValue x a≤x x≤b =
        subst (HasRiemannIntegralOn f a x) (sym (agrees (x , a≤x , x≤b)))
          (hasValue (x , a≤x , x≤b))

      increments : HasIntegralIncrementsOn extendedValue f a b
      increments x y a≤x x≤y y≤b =
        subst (HasRiemannIntegralOn f x y)
          (sym (riemannIntegral-difference f a x y a≤x x≤y
            (extendedValue x , extendedHasValue x a≤x x≤b)
            (integrable x y a≤x x≤y y≤b)
            (extendedValue y , extendedHasValue y a≤y y≤b)))
          (snd (integrable x y a≤x x≤y y≤b))
        where
        x≤b : x ≤ℝ b
        x≤b = ≤ℝ-trans x y b x≤y y≤b
        a≤y : a ≤ℝ y
        a≤y = ≤ℝ-trans a x y a≤x x≤y

    -- FTC for F(x) = integral_a^x f.  Continuity is required only on [a,b].
    -- At the endpoints the derivative is relative to that closed interval.
    hasDerivative :
      isContinuous (ClosedIntervalPremetricSpace a b .snd)
        (f ∘ fst) (ℝPremetricSpace .snd) →
      IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst value (f ∘ fst)
    hasDerivative continuous =
      subst (λ F → IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
        fst F (f ∘ fst)) (funExt agrees)
        (integralIncrementsHaveDerivativeAlong extendedValue f a b continuous increments)

    hasUniformDerivative :
      IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
        (f ∘ fst) (ℝPremetricSpace .snd) →
      IsRadiuswiseUniformDerivativeAlong
        (ClosedIntervalPremetricSpace a b .snd) fst value (f ∘ fst)
    hasUniformDerivative continuous =
      subst (λ F → IsRadiuswiseUniformDerivativeAlong
        (ClosedIntervalPremetricSpace a b .snd) fst F (f ∘ fst)) (funExt agrees)
        (λ ε → PT.map (λ { (δ , bound) → δ ,
          λ (x , a≤x , x≤b) (y , a≤y , y≤b) → bound x y a≤x x≤b a≤y y≤b })
          (fundamentalTheoremOfCalculusFirstOn extendedValue f a b continuous increments ε))

    -- A real-valued extension is useful when composing the primitive with
    -- an ambient real map. Its derivative statement remains interval-local.
    clampedValue : ℝ → ℝ
    clampedValue = extendedValue

    clampedValueAgrees : ∀ point → clampedValue (fst point) ≡ value point
    clampedValueAgrees = agrees

    clampedValueHasIntegralIncrements : HasIntegralIncrementsOn clampedValue f a b
    clampedValueHasIntegralIncrements = increments

    clampedValueHasUniformDerivativeOn :
      IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
        (f ∘ fst) (ℝPremetricSpace .snd) → IsRadiuswiseUniformDerivativeOn clampedValue f a b
    clampedValueHasUniformDerivativeOn continuous =
      fundamentalTheoremOfCalculusFirstOn extendedValue f a b continuous increments

    valueOfUniformAntiderivative : ∀ F →
      IsRadiuswiseUniformDerivativeOn F f a b →
      ∀ point → value point ≡ F (fst point) - F a
    valueOfUniformAntiderivative F derivative (x , a≤x , x≤b) =
      integralOfUniformDerivative F f a x a≤x
        (radiuswiseUniformDerivativeOn→subinterval F f a b a x
          (≤ℝ-refl a) x≤b derivative)
        (value (x , a≤x , x≤b) , hasValue (x , a≤x , x≤b))
