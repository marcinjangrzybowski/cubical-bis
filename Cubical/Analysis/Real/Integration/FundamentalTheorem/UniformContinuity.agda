module Cubical.Analysis.Real.Integration.FundamentalTheorem.UniformContinuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.RiemannIntegral.UniformContinuity
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Accumulation

opaque
  uniformContinuityIsIntegrableOnSubintervals : ∀ f a b →
    isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd) → IsIntegrableOnSubintervals f a b
  uniformContinuityIsIntegrableOnSubintervals f a b continuous x y a≤x x≤y y≤b =
    uniformContinuityIsRiemannIntegrableOn f x y x≤y
      (uniformContinuityOnSubinterval f a b x y a≤x y≤b continuous)

-- The first fundamental theorem with all subinterval integrals constructed
-- from uniform continuity.  At either endpoint the derivative is relative
-- to the closed interval.
module UniformlyContinuousAccumulation (f : ℝ → ℝ) (a b : ℝ) (a≤b : a ≤ℝ b)
    (continuous : isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd)) where
  private
    module A = Accumulation f a b a≤b
      (uniformContinuityIsIntegrableOnSubintervals f a b continuous)

  open A public using (value; hasValue; valueOfUniformAntiderivative; clampedValue; clampedValueAgrees)

  opaque
    hasDerivative :
      IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst value (f ∘ fst)
    hasDerivative = A.hasDerivative
      (isUniformlyContinuous→isContinuous (ClosedIntervalPremetricSpace a b .snd)
        (f ∘ fst) (ℝPremetricSpace .snd) continuous)

    hasUniformDerivative : IsRadiuswiseUniformDerivativeAlong
      (ClosedIntervalPremetricSpace a b .snd) fst value (f ∘ fst)
    hasUniformDerivative = A.hasUniformDerivative
      (isUniformlyContinuous→isRadiuswiseUniformlyContinuous
        (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) continuous)

    clampedValueHasUniformDerivativeOn : IsRadiuswiseUniformDerivativeOn clampedValue f a b
    clampedValueHasUniformDerivativeOn = A.clampedValueHasUniformDerivativeOn
      (isUniformlyContinuous→isRadiuswiseUniformlyContinuous
        (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) continuous)
