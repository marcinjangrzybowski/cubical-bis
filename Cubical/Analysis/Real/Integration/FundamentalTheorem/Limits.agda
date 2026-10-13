module Cubical.Analysis.Real.Integration.FundamentalTheorem.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse using (_₊／₊_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Uniform
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Error
open import Cubical.Analysis.Real.Integration.RiemannIntegral.UniformLimit
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.First
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Accumulation
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Stability

opaque
  -- One tail works for every upper endpoint, since every subinterval has
  -- length at most b-a. Existing integrals need only radiuswise convergence.
  indefiniteIntegralsConvergeUniformly : ∀ (functions : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (values : ℕ → ClosedInterval a b → ℝ) (value : ClosedInterval a b → ℝ) →
    (∀ n point → HasRiemannIntegralOn (functions n) a (fst point) (values n point)) →
    (∀ point → HasRiemannIntegralOn f a (fst point) (value point)) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → functions n (fst x)) (f ∘ fst) →
    IsUniformLimit values value
  indefiniteIntegralsConvergeUniformly functions f a b values value hasValues hasValue uniform ε =
    PT.rec squash₁ (λ { (k , length<bound) →
      PT.map (λ { (N , close) → N , λ n large point@(x , a≤x , x≤b) →
        riemannIntegralsCloseFromUniformBound a x a≤x (functions n) f (values n point) (value point)
          (naturalBound k) ε
          (≤<ℝ-trans (x - a) (b - a) (rat (naturalRational k)) (addPres≤R x b (- a) x≤b) length<bound)
          (hasValues n point) (hasValue point)
          (λ (z , a≤z , z≤x) → close n large (z , a≤z , ≤ℝ-trans z x b z≤x x≤b)) })
        (uniform (ε ₊／₊ naturalBound k)) }) (∃naturalUpperBound (b - a))

opaque
  uniformLimitIsIntegrableOnSubintervals : ∀ (functions : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (a b : ℝ) →
    (∀ n → IsIntegrableOnSubintervals (functions n) a b) →
    UniformLimitWitness (λ n (x : ClosedInterval a b) → functions n (fst x)) (f ∘ fst) →
    IsIntegrableOnSubintervals f a b
  uniformLimitIsIntegrableOnSubintervals functions f a b integrable uniform x y a≤x x≤y y≤b =
    uniformLimitIsRiemannIntegrableOn functions f x y x≤y (λ n → integrable n x y a≤x x≤y y≤b)
      (PT.map (λ { (μ , close) → μ , λ ε n large (z , x≤z , z≤y) →
        close ε n large (z , ≤ℝ-trans a x z a≤x x≤z , ≤ℝ-trans z y b z≤y y≤b) }) uniform)

opaque
  accumulationsConvergeUniformly : ∀ (functions : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (a b : ℝ) (a≤b : a ≤ℝ b)
    (integrable : ∀ n → IsIntegrableOnSubintervals (functions n) a b)
    (limitIntegrable : IsIntegrableOnSubintervals f a b) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → functions n (fst x)) (f ∘ fst) →
    IsUniformLimit (λ n → Accumulation.value (functions n) a b a≤b (integrable n))
      (Accumulation.value f a b a≤b limitIntegrable)
  accumulationsConvergeUniformly functions f a b a≤b integrable limitIntegrable =
    indefiniteIntegralsConvergeUniformly functions f a b
      (λ n → Accumulation.value (functions n) a b a≤b (integrable n))
      (Accumulation.value f a b a≤b limitIntegrable)
      (λ n → Accumulation.hasValue (functions n) a b a≤b (integrable n))
      (Accumulation.hasValue f a b a≤b limitIntegrable)

  -- Endpoint convergence is enough for every integral increment. No
  -- uniform convergence of the primitives, or native modulus, is needed.
opaque
  pointwiseLimitPreservesIntegralIncrements : ∀ (functions derivatives : ℕ → ℝ → ℝ) (F f : ℝ → ℝ) (a b : ℝ) →
    (∀ n → HasIntegralIncrementsOn (functions n) (derivatives n) a b) →
    (∀ (point : ClosedInterval a b) → isLimitSequence (λ n → functions n (fst point)) (F (fst point))) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → derivatives n (fst x)) (f ∘ fst) →
    HasIntegralIncrementsOn F f a b
  pointwiseLimitPreservesIntegralIncrements functions derivatives F f a b increments functions→F derivatives→f
      x y a≤x x≤y y≤b =
    uniformLimitPreservesIntegral derivatives f x y (λ n → functions n y - functions n x) (F y - F x)
      (λ n → increments n x y a≤x x≤y y≤b)
      (uniformLimitPrecompose (λ n (z : ClosedInterval a b) → derivatives n (fst z)) (f ∘ fst)
        (λ (z , x≤z , z≤y) → z , ≤ℝ-trans a x z a≤x x≤z , ≤ℝ-trans z y b z≤y y≤b) derivatives→f)
      (subPresIsLimitSequence
        (functions→F (y , ≤ℝ-trans a x y a≤x x≤y , y≤b))
        (functions→F (x , a≤x , ≤ℝ-trans x y b x≤y y≤b)))

opaque
  pointwiseLimitPreservesUniformDerivative : ∀ (functions derivatives : ℕ → ℝ → ℝ) (F f : ℝ → ℝ) (a b : ℝ) →
    (∀ n → IsRadiuswiseUniformDerivativeOn (functions n) (derivatives n) a b) →
    (∀ (point : ClosedInterval a b) → isLimitSequence (λ n → functions n (fst point)) (F (fst point))) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → derivatives n (fst x)) (f ∘ fst) →
    IsRadiuswiseUniformDerivativeOn F f a b
  pointwiseLimitPreservesUniformDerivative functions derivatives F f a b derivative functions→F derivatives→f =
    uniformLimitOfIntegralIncrementsHasUniformDerivative F f functions derivatives a b
      (pointwiseLimitPreservesIntegralIncrements functions derivatives F f a b
        (λ n → uniformDerivativeHasIntegralIncrements (functions n) (derivatives n) a b (derivative n))
        functions→F derivatives→f) derivative derivatives→f

opaque
  uniformLimitsPreserveUniformDerivative : ∀ (functions derivatives : ℕ → ℝ → ℝ) (F f : ℝ → ℝ) (a b : ℝ) →
    (∀ n → IsRadiuswiseUniformDerivativeOn (functions n) (derivatives n) a b) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → functions n (fst x)) (F ∘ fst) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → derivatives n (fst x)) (f ∘ fst) →
    IsRadiuswiseUniformDerivativeOn F f a b
  uniformLimitsPreserveUniformDerivative functions derivatives F f a b derivative functions→F =
    pointwiseLimitPreservesUniformDerivative functions derivatives F f a b derivative
      (uniformLimitAt (λ n (z : ClosedInterval a b) → functions n (fst z)) (F ∘ fst) functions→F)
