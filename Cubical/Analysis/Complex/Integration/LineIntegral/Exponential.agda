module Cubical.Analysis.Complex.Integration.LineIntegral.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Uniform.Bounds
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.Path.Bounds
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Bounded

exponentialIsBoundedUniformPrimitiveAlongPath : ∀ {a b} (path : UniformComplexPath a b) →
  IsBoundedUniformPrimitiveAlongPath expℂ expℂ path
exponentialIsBoundedUniformPrimitiveAlongPath {a} {b} path =
  expℂHasUniformDerivativeAlongNormBounded (ClosedIntervalPremetricSpace a b .snd) (UniformComplexPath.curve path ∘ fst)
    (pathImageNormBound path) (λ (t , lo , hi) → pathImageIsBounded path t lo hi) (pathIsRadiuswiseUniformlyContinuous path) ,
  PT.map (λ { (B , bound) → B , λ t lo hi → bound (UniformComplexPath.curve path t) (pathImageIsBounded path t lo hi) })
    (expℂRationalBoundOnBall (pathImageNormBound path))

exponentialHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) →
  HasComplexLineIntegral expℂ path (expℂ (pathFinish path) -ℂ expℂ (pathStart path))
exponentialHasComplexLineIntegral path =
  boundedUniformPrimitiveHasComplexLineIntegral path expℂ expℂ (exponentialIsBoundedUniformPrimitiveAlongPath path)

closedExponentialHasZeroComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) → pathFinish path ≡ pathStart path →
  HasComplexLineIntegral expℂ path 0ℂ
closedExponentialHasZeroComplexLineIntegral path closed = subst (HasComplexLineIntegral expℂ path)
  (cong (λ z → expℂ z -ℂ expℂ (pathStart path)) closed ∙ +ℂInvR (expℂ (pathStart path))) (exponentialHasComplexLineIntegral path)
