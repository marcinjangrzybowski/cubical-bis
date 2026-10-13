module Cubical.Analysis.Complex.Integration.UniformContinuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
import Cubical.Analysis.Real.Integration.FundamentalTheorem.UniformContinuity as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.FundamentalTheorem

realPartIsUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) (h : A → ℂ) →
  isUniformlyContinuous source h (ℂPremetricSpace .snd) → isUniformlyContinuous source (re ∘ h) (ℝPremetricSpace .snd)
realPartIsUniformlyContinuous source h = PT.map
  (λ { (μ , proof) → μ , record { pres≈ = λ x y ε near → fst (IsUniformlyContinuousWith.pres≈ proof x y ε near) } })

imaginaryPartIsUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) (h : A → ℂ) →
  isUniformlyContinuous source h (ℂPremetricSpace .snd) → isUniformlyContinuous source (im ∘ h) (ℝPremetricSpace .snd)
imaginaryPartIsUniformlyContinuous source h = PT.map
  (λ { (μ , proof) → μ , record { pres≈ = λ x y ε near → snd (IsUniformlyContinuousWith.pres≈ proof x y ε near) } })

-- A first-FTC primitive of a complex function of a real parameter. Standard
-- uniform continuity supplies native subinterval integrals coordinatewise.
-- The primitive is extended by clamping outside the certified interval.
module UniformlyContinuousComplexAccumulation (h : ℝ → ℂ) (a b : ℝ) (ordered : a ≤ℝ b)
  (continuous : isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (h ∘ fst) (ℂPremetricSpace .snd)) where
  private
    module R = Real.UniformlyContinuousAccumulation (re ∘ h) a b ordered
      (realPartIsUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (h ∘ fst) continuous)
    module I = Real.UniformlyContinuousAccumulation (im ∘ h) a b ordered
      (imaginaryPartIsUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (h ∘ fst) continuous)

  clampedValue : ℝ → ℂ
  clampedValue t = R.clampedValue t , I.clampedValue t

  hasUniformDerivative : IsUniformComplexCurveDerivativeOn clampedValue h a b
  hasUniformDerivative = R.clampedValueHasUniformDerivativeOn , I.clampedValueHasUniformDerivativeOn

  hasEndpointIntegral : HasComplexRiemannIntegralOn h a b (clampedValue b -ℂ clampedValue a)
  hasEndpointIntegral = complexFundamentalTheoremOfCalculus clampedValue h a b hasUniformDerivative

  integralValue : ∀ v → HasComplexRiemannIntegralOn h a b v → v ≡ clampedValue b -ℂ clampedValue a
  integralValue v proof = complexRiemannIntegralUnique h a b ordered v (clampedValue b -ℂ clampedValue a) proof hasEndpointIntegral

uniformContinuityIsComplexRiemannIntegrableOn : ∀ h a b → a ≤ℝ b →
  isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (h ∘ fst) (ℂPremetricSpace .snd) → IsComplexRiemannIntegrableOn h a b
uniformContinuityIsComplexRiemannIntegrableOn h a b ordered continuous =
  (A.clampedValue b -ℂ A.clampedValue a) , A.hasEndpointIntegral
  where module A = UniformlyContinuousComplexAccumulation h a b ordered continuous
