module Cubical.Analysis.Complex.Integration.Path.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (mul-rat)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.Exponential

-- The supplied bound is quantitative data used to build a path record.
-- It is not selected from the truncated existence used by the integral FTC.
exponentialComplexPath : ∀ {a b} (path : UniformComplexPath a b) (B : ℚ₊) →
  (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (expℂ (UniformComplexPath.curve path t)) ≤ℝ rat (fst B)) → UniformComplexPath a b
exponentialComplexPath path B bound .UniformComplexPath.ordered = UniformComplexPath.ordered path
exponentialComplexPath path B bound .UniformComplexPath.curve = expℂ ∘ UniformComplexPath.curve path
exponentialComplexPath path B bound .UniformComplexPath.velocity t =
  expℂ (UniformComplexPath.curve path t) ·ℂ UniformComplexPath.velocity path t
exponentialComplexPath path B bound .UniformComplexPath.differentiable =
  primitiveAlongPathHasUniformCurveDerivative path expℂ expℂ B bound (fst (exponentialIsBoundedUniformPrimitiveAlongPath path))
exponentialComplexPath path B bound .UniformComplexPath.speedBound = B ·₊ UniformComplexPath.speedBound path
exponentialComplexPath path B bound .UniformComplexPath.boundedSpeed t lo hi =
  subst (normℂ (expℂ (UniformComplexPath.curve path t) ·ℂ UniformComplexPath.velocity path t) ≤ℝ_)
    (mul-rat (fst B) (fst (UniformComplexPath.speedBound path)))
    (normℂ-mulBound (expℂ (UniformComplexPath.curve path t)) (UniformComplexPath.velocity path t)
      (rat (fst B)) (rat (fst (UniformComplexPath.speedBound path))) (bound t lo hi) (UniformComplexPath.boundedSpeed path t lo hi))
