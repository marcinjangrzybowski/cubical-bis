module Cubical.Analysis.Real.Integration.FundamentalTheorem.DerivativeLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; max)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Uniform
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Extensionality
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.First
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Accumulation
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Consequences
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Limits

-- Convergence at one endpoint and uniform convergence of the derivatives
-- construct the uniform limit of the functions. The derivative convergence
-- supplies one modulus because constructing a new sequential real requires
-- native Cauchy data. No modulus is requested for the initial-value limit.
module UniformDerivativeLimit (functions derivatives : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (a b initial : ℝ) (a≤b : a ≤ℝ b)
    (derivative : ∀ n → IsRadiuswiseUniformDerivativeOn (functions n) (derivatives n) a b)
    (derivativeConvergence : UniformLimitWitness
      (λ n (x : ClosedInterval a b) → derivatives n (fst x)) (f ∘ fst))
    (initialConvergence : isLimitSequence (λ n → functions n a) initial) where

  limitDerivativeIntegrable : IsIntegrableOnSubintervals f a b
  limitDerivativeIntegrable = uniformLimitIsIntegrableOnSubintervals derivatives f a b
    (λ n → uniformDerivativeIsIntegrableOnSubintervals (functions n) (derivatives n) a b (derivative n))
    derivativeConvergence

  private
    module A = Accumulation f a b a≤b limitDerivativeIntegrable
    derivatives→f : IsUniformLimit
      (λ n (x : ClosedInterval a b) → derivatives n (fst x)) (f ∘ fst)
    derivatives→f = uniformLimitWitness→uniformLimit
      (λ n (x : ClosedInterval a b) → derivatives n (fst x)) (f ∘ fst) derivativeConvergence
    normalized : ℕ → ClosedInterval a b → ℝ
    normalized n point = functions n (fst point) - functions n a

  value : ℝ → ℝ
  value x = initial + A.clampedValue x

  opaque
    normalizedFunctionsConverge : IsUniformLimit normalized A.value
    normalizedFunctionsConverge = indefiniteIntegralsConvergeUniformly derivatives f a b normalized A.value
      (λ n (x , a≤x , x≤b) → uniformDerivativeHasIntegralIncrements
        (functions n) (derivatives n) a b (derivative n) a x (≤ℝ-refl a) a≤x x≤b)
      A.hasValue derivatives→f

  opaque
    convergesUniformly : IsUniformLimit
      (λ n (x : ClosedInterval a b) → functions n (fst x)) (value ∘ fst)
    convergesUniformly ε = PT.map2 combine (initialConvergence (ε /2₊)) (normalizedFunctionsConverge (ε /2₊))
      where
      combine :
        Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → functions n a ∼[ ε /2₊ ] initial) →
        Σ[ M ∈ ℕ ] (∀ n → M ℕ.≤ n → ∀ point → normalized n point ∼[ ε /2₊ ] A.value point) →
        Σ[ K ∈ ℕ ] (∀ n → K ℕ.≤ n → ∀ (point : ClosedInterval a b) → functions n (fst point) ∼[ ε ] value (fst point))
      combine (N , nearInitial) (M , nearPrimitive) = max N M , λ n large point →
        subst2 (λ x y → x ∼[ ε ] y)
          (addComm (functions n a) (normalized n point) ∙ subAddCancel (functions n (fst point)) (functions n a))
          (cong (initial +_) (sym (A.clampedValueAgrees point)))
          (subst (λ ρ → functions n a + normalized n point ∼[ ρ ] initial + A.value point)
            (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst ε)))
            (add-pres∼ (functions n a) initial (normalized n point) (A.value point) (ε /2₊) (ε /2₊)
              (nearInitial n (ℕ.≤-trans (ℕ.left-≤-max {m = N} {n = M}) large))
              (nearPrimitive n (ℕ.≤-trans (ℕ.right-≤-max {n = M} {m = N}) large) point)))

  opaque
    hasUniformDerivative : IsRadiuswiseUniformDerivativeOn value f a b
    hasUniformDerivative = uniformLimitsPreserveUniformDerivative functions derivatives value f a b
      derivative convergesUniformly derivatives→f

  opaque
    hasDerivative : IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (value ∘ fst) (f ∘ fst)
    hasDerivative = uniformDerivativeAlong→derivativeAlong (ClosedIntervalPremetricSpace a b .snd)
      fst (value ∘ fst) (f ∘ fst) (uniformDerivativeOn→alongInterval value f a b hasUniformDerivative)

  opaque
    valueAtLowerEndpoint : value a ≡ initial
    valueAtLowerEndpoint = cong (initial +_)
      (A.clampedValueAgrees (a , ≤ℝ-refl a , a≤b)
        ∙ riemannIntegralOnPointIsZero f a (A.value (a , ≤ℝ-refl a , a≤b)) (A.hasValue (a , ≤ℝ-refl a , a≤b)))
      ∙ addIdR initial

  opaque
    uniqueWithInitialValue : ∀ (F : ℝ → ℝ) → IsRadiuswiseUniformDerivativeOn F f a b → F a ≡ initial →
      ∀ (point : ClosedInterval a b) → F (fst point) ≡ value (fst point)
    uniqueWithInitialValue F FDerivative initialValue (x , lower , upper) =
      uniformAntiderivativeUniqueWithInitialValue F value f a b FDerivative hasUniformDerivative
        (initialValue ∙ sym valueAtLowerEndpoint) x lower upper
