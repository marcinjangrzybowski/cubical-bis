module Cubical.Analysis.Complex.Integration.LineIntegral.Consequences where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Integration.Operations
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem

constantHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) c →
  HasComplexLineIntegral (λ _ → c) path (c ·ℂ (pathFinish path -ℂ pathStart path))
constantHasComplexLineIntegral {a} {b} path c =
  scaleHasComplexRiemannIntegral c (UniformComplexPath.velocity path) (pathFinish path -ℂ pathStart path)
    (complexFundamentalTheoremOfCalculus (UniformComplexPath.curve path) (UniformComplexPath.velocity path)
      a b (UniformComplexPath.differentiable path))

-- Both paths may have different real parameter intervals. They must have
-- the same endpoints and the same primitive; no homotopy or simple-domain
-- hypothesis is needed once that primitive is supplied.
complexPrimitiveLineIntegralPathIndependent : ∀ {a b c d}
  (firstPath : UniformComplexPath a b) (secondPath : UniformComplexPath c d) F f (B C : ℚ₊) →
  (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (f (UniformComplexPath.curve firstPath t)) ≤ℝ rat (fst B)) →
  (∀ t → c ≤ℝ t → t ≤ℝ d → normℂ (f (UniformComplexPath.curve secondPath t)) ≤ℝ rat (fst C)) →
  IsUniformPrimitiveAlongPath F f firstPath → IsUniformPrimitiveAlongPath F f secondPath →
  pathStart firstPath ≡ pathStart secondPath → pathFinish firstPath ≡ pathFinish secondPath →
  (first : IsComplexLineIntegrable f firstPath) (second : IsComplexLineIntegrable f secondPath) →
  complexLineIntegral f firstPath first ≡ complexLineIntegral f secondPath second
complexPrimitiveLineIntegralPathIndependent firstPath secondPath F f B C firstBound secondBound
  firstPrimitive secondPrimitive sameStart sameFinish first second =
  complexLineIntegralOfPrimitive firstPath F f B firstBound firstPrimitive first
  ∙ cong₂ _-ℂ_ (cong F sameFinish) (cong F sameStart)
  ∙ sym (complexLineIntegralOfPrimitive secondPath F f C secondBound secondPrimitive second)
