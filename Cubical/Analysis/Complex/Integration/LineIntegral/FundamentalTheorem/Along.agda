module Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem.Along where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Chain
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.RealParameter
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.Along

-- F and f are values indexed by the real parameter, not ambient complex
-- functions. The derivative estimate is measured against complex path
-- chords. Thus a constructed domain-local primitive can be used directly.
IsUniformPrimitiveValuesAlongPath : ∀ {a b} → (ℝ → ℂ) → (ℝ → ℂ) → UniformComplexPath a b → Type₀
IsUniformPrimitiveValuesAlongPath {a} {b} F f path =
  IsRadiuswiseUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
    (UniformComplexPath.curve path ∘ fst) (F ∘ fst) (f ∘ fst)

module _ {a b : ℝ} (path : UniformComplexPath a b) (F f : ℝ → ℂ) (C : ℚ₊)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (f t) ≤ℝ rat (fst C)) where
  private module P = UniformComplexPath path

  opaque
    primitiveValuesAlongPathHasUniformCurveDerivative : IsUniformPrimitiveValuesAlongPath F f path →
      IsUniformComplexCurveDerivativeOn F (complexLineIntegrandAlong f path) a b
    primitiveValuesAlongPathHasUniformCurveDerivative estimate =
      uniformCurveDerivativeAlong→on F (complexLineIntegrandAlong f path) a b
        (chainHasUniformComplexDerivativeAlongIndexedBounded (ClosedIntervalPremetricSpace a b .snd)
          (fromℝ ∘ fst) (P.curve ∘ fst) (P.velocity ∘ fst) (F ∘ fst) (f ∘ fst)
          (P.speedBound +₊ P.speedBound) C
          (λ x y → subst (normℂ (P.curve (fst y) -ℂ P.curve (fst x)) ≤ℝ_)
            (sym (cong (rat (fst (P.speedBound +₊ P.speedBound)) ·_) (realParameterDisplacementNorm fst x y)))
            (uniformComplexCurveLipschitzOn P.curve P.velocity a b P.speedBound P.differentiable P.boundedSpeed x y))
          (λ x → bounded (fst x) (fst (snd x)) (snd (snd x)))
          (uniformCurveDerivativeOn→along P.curve P.velocity a b P.differentiable) estimate)

  fundamentalTheoremOfComplexLineIntegralsAlong : IsUniformPrimitiveValuesAlongPath F f path →
    HasComplexLineIntegralAlong f path (F b -ℂ F a)
  fundamentalTheoremOfComplexLineIntegralsAlong estimate =
    complexFundamentalTheoremOfCalculus F (complexLineIntegrandAlong f path) a b
      (primitiveValuesAlongPathHasUniformCurveDerivative estimate)

  primitiveValuesComplexLineIntegrableAlong : IsUniformPrimitiveValuesAlongPath F f path →
    IsComplexLineIntegrableAlong f path
  primitiveValuesComplexLineIntegrableAlong estimate =
    (F b -ℂ F a) , fundamentalTheoremOfComplexLineIntegralsAlong estimate

  -- For parameter-indexed values, geometric closedness alone does not make
  -- the primitive endpoints agree (a logarithmic lift illustrates this).
  equalPrimitiveValuesHaveZeroLineIntegral : IsUniformPrimitiveValuesAlongPath F f path →
    F b ≡ F a → HasComplexLineIntegralAlong f path 0ℂ
  equalPrimitiveValuesHaveZeroLineIntegral estimate equal = subst (HasComplexLineIntegralAlong f path)
    (cong (_-ℂ F a) equal ∙ +ℂInvR (F a)) (fundamentalTheoremOfComplexLineIntegralsAlong estimate)
