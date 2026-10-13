module Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem where

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
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Chain
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.RealParameter
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem.Along

-- Only the primitive's remainder along the path is needed. Its controlling
-- displacement is the complex chord γ(y)-γ(x), not the parameter increment.
-- The chain rule below proves the required parameter derivative from this.
IsUniformPrimitiveAlongPath : ∀ {a b} → (ℂ → ℂ) → (ℂ → ℂ) → UniformComplexPath a b → Type₀
IsUniformPrimitiveAlongPath {a} {b} F f path =
  IsRadiuswiseUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
    (UniformComplexPath.curve path ∘ fst) (F ∘ UniformComplexPath.curve path ∘ fst)
    (f ∘ UniformComplexPath.curve path ∘ fst)

module _ {a b : ℝ} (path : UniformComplexPath a b) (F f : ℂ → ℂ) (C : ℚ₊)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (f (UniformComplexPath.curve path t)) ≤ℝ rat (fst C)) where
  private module P = UniformComplexPath path

  opaque
    primitiveAlongPathHasUniformCurveDerivative : IsUniformPrimitiveAlongPath F f path →
      IsUniformComplexCurveDerivativeOn (F ∘ P.curve) (complexLineIntegrand f path) a b
    primitiveAlongPathHasUniformCurveDerivative = primitiveValuesAlongPathHasUniformCurveDerivative
      path (F ∘ P.curve) (f ∘ P.curve) C bounded

  -- Integrability is a conclusion, not an additional hypothesis.
  fundamentalTheoremOfComplexLineIntegrals : IsUniformPrimitiveAlongPath F f path →
    HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
  fundamentalTheoremOfComplexLineIntegrals primitiveEstimate =
    complexFundamentalTheoremOfCalculus (F ∘ P.curve) (complexLineIntegrand f path) a b
      (primitiveAlongPathHasUniformCurveDerivative primitiveEstimate)

  primitiveComplexLineIntegrable : IsUniformPrimitiveAlongPath F f path → IsComplexLineIntegrable f path
  primitiveComplexLineIntegrable primitiveEstimate =
    (F (pathFinish path) -ℂ F (pathStart path)) , fundamentalTheoremOfComplexLineIntegrals primitiveEstimate

  complexLineIntegralOfPrimitive : IsUniformPrimitiveAlongPath F f path →
    (integrable : IsComplexLineIntegrable f path) →
    complexLineIntegral f path integrable ≡ F (pathFinish path) -ℂ F (pathStart path)
  complexLineIntegralOfPrimitive primitiveEstimate integrable =
    complexLineIntegralUnique f path (fst integrable) (F (pathFinish path) -ℂ F (pathStart path))
      (snd integrable) (fundamentalTheoremOfComplexLineIntegrals primitiveEstimate)

  closedPrimitiveComplexLineIntegral : IsUniformPrimitiveAlongPath F f path → pathFinish path ≡ pathStart path →
    HasComplexLineIntegral f path 0ℂ
  closedPrimitiveComplexLineIntegral primitiveEstimate closed = subst (HasComplexLineIntegral f path)
    (cong (λ z → F z -ℂ F (pathStart path)) closed ∙ +ℂInvR (F (pathStart path)))
    (fundamentalTheoremOfComplexLineIntegrals primitiveEstimate)

-- A uniform derivative on the ambient complex space restricts along every
-- such path by its proved uniform continuity. Domain-local clients can use
-- uniformComplexDerivativeAlongPrecompose on their subspace instead.
uniformComplexDerivativeGivesPrimitiveAlongPath : ∀ {a b} (path : UniformComplexPath a b) F f →
  IsRadiuswiseUniformComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ) F f → IsUniformPrimitiveAlongPath F f path
uniformComplexDerivativeGivesPrimitiveAlongPath {a} {b} path F f =
  uniformComplexDerivativeAlongPrecompose (ClosedIntervalPremetricSpace a b .snd) (ℂPremetricSpace .snd)
    (UniformComplexPath.curve path ∘ fst) (idfun ℂ) F f (pathIsRadiuswiseUniformlyContinuous path)
