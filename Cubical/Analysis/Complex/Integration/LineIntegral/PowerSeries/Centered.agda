module Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Centered where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Domain.Interval
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Translation
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Translation
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Translation
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Interior

-- A genuine local expansion in z-center: the path need not lie in a ball
-- about zero. Only the original coefficient majorant at the outer radius is
-- supplied; the existing strict-interior theorem constructs all derivative
-- convergence and integrability data after recentering the certified path.
module _ {a b : ℝ} (path : UniformComplexPath a b) (F f : ℂ → ℂ)
  (coefficients : ComplexSequence) (center : ℂ) (inner outer : ℝ)
  (nonnegative : 0ℝ ≤ℝ inner) (strict : inner <ℝ outer)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t -ℂ center) ≤ℝ inner)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (originalSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ coefficients (UniformComplexPath.curve path t -ℂ center)) (F (UniformComplexPath.curve path t)))
  (derivativeSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (UniformComplexPath.curve path t -ℂ center)) (f (UniformComplexPath.curve path t))) where
  private
    module P = UniformComplexPath path
    shifted : UniformComplexPath a b
    shifted = recenterComplexPath path center
    shiftedF shiftedf : ℂ → ℂ
    shiftedF z = F (z +ℂ center)
    shiftedf z = f (z +ℂ center)

    shiftedOriginalSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
      HasComplexSum (powerSeriesTermsℂ coefficients (P.curve t -ℂ center)) (shiftedF (P.curve t -ℂ center))
    shiftedOriginalSum t lo hi = subst (HasComplexSum (powerSeriesTermsℂ coefficients (P.curve t -ℂ center)))
      (sym (cong F (ℂRing.minusPlus (P.curve t) center))) (originalSum t lo hi)

    shiftedDerivativeSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
      HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (P.curve t -ℂ center)) (shiftedf (P.curve t -ℂ center))
    shiftedDerivativeSum t lo hi = subst (HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (P.curve t -ℂ center)))
      (sym (cong f (ℂRing.minusPlus (P.curve t) center))) (derivativeSum t lo hi)

  opaque
    centeredPowerSeriesIsUniformPrimitiveAlongPath : IsUniformPrimitiveAlongPath F f path
    centeredPowerSeriesIsUniformPrimitiveAlongPath = subst2
      (IsRadiuswiseUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst))
      (funExt λ x → cong F (ℂRing.minusPlus (P.curve (fst x)) center))
      (funExt λ x → cong f (ℂRing.minusPlus (P.curve (fst x)) center))
      (unshiftUniformComplexDerivativeCoordinate (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst)
        (shiftedF ∘ UniformComplexPath.curve shifted ∘ fst) (shiftedf ∘ UniformComplexPath.curve shifted ∘ fst) center
        (powerSeriesIsUniformPrimitiveAlongPathFromOuterRadius shifted shiftedF shiftedf coefficients inner outer
          nonnegative strict bounded witness shiftedOriginalSum shiftedDerivativeSum))

    centeredPowerSeriesDerivativeHasComplexLineIntegral :
      HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
    centeredPowerSeriesDerivativeHasComplexLineIntegral = subst (HasComplexLineIntegral f path)
      (cong₂ _-ℂ_ (cong F (ℂRing.minusPlus (pathFinish path) center))
        (cong F (ℂRing.minusPlus (pathStart path) center)))
      (recenterHasComplexLineIntegral path center f (shiftedF (pathFinish shifted) -ℂ shiftedF (pathStart shifted))
        (powerSeriesDerivativeHasComplexLineIntegralFromOuterRadius shifted shiftedF shiftedf coefficients inner outer
          nonnegative strict bounded witness shiftedOriginalSum shiftedDerivativeSum))

  centeredPowerSeriesDerivativeComplexLineIntegrable : IsComplexLineIntegrable f path
  centeredPowerSeriesDerivativeComplexLineIntegrable =
    (F (pathFinish path) -ℂ F (pathStart path)) , centeredPowerSeriesDerivativeHasComplexLineIntegral

  closedCenteredPowerSeriesDerivativeHasZeroLineIntegral :
    pathFinish path ≡ pathStart path → HasComplexLineIntegral f path 0ℂ
  closedCenteredPowerSeriesDerivativeHasZeroLineIntegral closed = subst (HasComplexLineIntegral f path)
    (cong (λ z → F z -ℂ F (pathStart path)) closed ∙ +ℂInvR (F (pathStart path)))
    centeredPowerSeriesDerivativeHasComplexLineIntegral
