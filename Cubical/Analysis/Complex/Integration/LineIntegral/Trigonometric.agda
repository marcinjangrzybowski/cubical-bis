module Cubical.Analysis.Complex.Integration.LineIntegral.Trigonometric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Slack using (rightSlack)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.HasSum
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Operations
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Bounds
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Interior

-- Every certified path already has a finite image bound. Adding one supplies
-- the strict radius margin required by the power-series FTC, so callers need
-- no extra convergence, derivative-bound or integrability hypotheses.
module _ {a b : ℝ} (path : UniformComplexPath a b) where
  private
    module P = UniformComplexPath path
    radius : ℝ
    radius = pathImageNormBound path
    nonnegative : 0ℝ ≤ℝ radius
    nonnegative = ≤ℝ-trans 0ℝ (normℂ (P.curve a)) radius
      (normℂ-nonnegative (P.curve a)) (pathImageIsBounded path a (≤ℝ-refl a) P.ordered)
    outerNonnegative : 0ℝ ≤ℝ radius + 1ℝ
    outerNonnegative = ≤ℝ-trans 0ℝ radius (radius + 1ℝ) nonnegative
      (<ℝ-weaken radius (radius + 1ℝ) (rightSlack radius 1))

  cosineHasComplexLineIntegral :
    HasComplexLineIntegral cosℂ path (sinℂ (pathFinish path) -ℂ sinℂ (pathStart path))
  cosineHasComplexLineIntegral = powerSeriesDerivativeHasComplexLineIntegralFromOuterRadius
    path sinℂ cosℂ sineCoefficientsℂ radius (radius + 1ℝ) nonnegative (rightSlack radius 1)
    (pathImageIsBounded path) (sineComplexMajorantIsCauchy (radius + 1ℝ) outerNonnegative)
    (λ t _ _ → sineComplexPowerSeriesHasSum (P.curve t))
    (λ t _ _ → sineFormalDerivativeHasComplexSum (P.curve t))

  private
    negativeSineHasComplexLineIntegral :
      HasComplexLineIntegral (λ z → -ℂ sinℂ z) path (cosℂ (pathFinish path) -ℂ cosℂ (pathStart path))
    negativeSineHasComplexLineIntegral = powerSeriesDerivativeHasComplexLineIntegralFromOuterRadius
      path cosℂ (λ z → -ℂ sinℂ z) cosineCoefficientsℂ radius (radius + 1ℝ) nonnegative (rightSlack radius 1)
      (pathImageIsBounded path) (cosineComplexMajorantIsCauchy (radius + 1ℝ) outerNonnegative)
      (λ t _ _ → cosineComplexPowerSeriesHasSum (P.curve t))
      (λ t _ _ → cosineFormalDerivativeHasComplexSum (P.curve t))

  opaque
    sineHasComplexLineIntegral :
      HasComplexLineIntegral sinℂ path (cosℂ (pathStart path) -ℂ cosℂ (pathFinish path))
    sineHasComplexLineIntegral = subst (HasComplexLineIntegral sinℂ path)
      (sym (ℂRing.-Dist (cosℂ (pathFinish path)) (-ℂ cosℂ (pathStart path)))
        ∙ cong ((-ℂ cosℂ (pathFinish path)) +ℂ_) (ℂRing.-Idempotent (cosℂ (pathStart path)))
        ∙ +ℂComm (-ℂ cosℂ (pathFinish path)) (cosℂ (pathStart path)))
      (complexHasIntegralCongOn
        (λ t → -ℂ complexLineIntegrand (λ z → -ℂ sinℂ z) path t)
        (complexLineIntegrand sinℂ path) a b (-ℂ (cosℂ (pathFinish path) -ℂ cosℂ (pathStart path)))
        (λ t _ _ → cong -ℂ_ (ℂRing.-DistL· (sinℂ (P.curve t)) (P.velocity t))
          ∙ ℂRing.-Idempotent (sinℂ (P.curve t) ·ℂ P.velocity t))
        (negHasComplexRiemannIntegral (complexLineIntegrand (λ z → -ℂ sinℂ z) path)
          (cosℂ (pathFinish path) -ℂ cosℂ (pathStart path)) negativeSineHasComplexLineIntegral))

  closedCosineHasZeroComplexLineIntegral : pathFinish path ≡ pathStart path → HasComplexLineIntegral cosℂ path 0ℂ
  closedCosineHasZeroComplexLineIntegral closed = subst (HasComplexLineIntegral cosℂ path)
    (cong (λ z → sinℂ z -ℂ sinℂ (pathStart path)) closed ∙ +ℂInvR (sinℂ (pathStart path))) cosineHasComplexLineIntegral

  closedSineHasZeroComplexLineIntegral : pathFinish path ≡ pathStart path → HasComplexLineIntegral sinℂ path 0ℂ
  closedSineHasZeroComplexLineIntegral closed = subst (HasComplexLineIntegral sinℂ path)
    (cong (λ z → cosℂ (pathStart path) -ℂ cosℂ z) closed ∙ +ℂInvR (cosℂ (pathStart path))) sineHasComplexLineIntegral
