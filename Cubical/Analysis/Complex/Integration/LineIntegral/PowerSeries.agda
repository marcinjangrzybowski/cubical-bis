module Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Domain.Interval
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Derivative.Uniform
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem

-- Only values on the path matter. F and f can be any ambient extensions of
-- supplied sums of a power series and its formal derivative. The derivative
-- majorant supplies the uniform remainder and a bound; integrability follows.
module _ {a b : ℝ} (path : UniformComplexPath a b) (F f : ℂ → ℂ)
  (coefficients : ComplexSequence) (radius : ℝ)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t) ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius))
  (originalSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ coefficients (UniformComplexPath.curve path t)) (F (UniformComplexPath.curve path t)))
  (derivativeSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (UniformComplexPath.curve path t)) (f (UniformComplexPath.curve path t))) where
  private module P = UniformComplexPath path

  powerSeriesIsUniformPrimitiveAlongPath : IsUniformPrimitiveAlongPath F f path
  powerSeriesIsUniformPrimitiveAlongPath = complexPowerSeriesHasUniformFormalDerivativeAlong
    (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst) (F ∘ P.curve ∘ fst) (f ∘ P.curve ∘ fst)
    coefficients radius (λ x → bounded (fst x) (fst (snd x)) (snd (snd x))) witness
    (pathIsRadiuswiseUniformlyContinuous path)
    (λ x → originalSum (fst x) (fst (snd x)) (snd (snd x)))
    (λ x → derivativeSum (fst x) (fst (snd x)) (snd (snd x)))

  private
    majorant : Real.RealSequence
    majorant = complexPowerSeriesDerivativeMajorant coefficients radius
    majorantSum : Real.Summable majorant
    majorantSum = Real.cauchySeriesIsSummable majorant witness
    bound : ℝ
    bound = Real.seriesSum majorant majorantSum

    derivativeBound : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (f (P.curve t)) ≤ℝ bound
    derivativeBound t lo hi = seriesSumℂBoundBy
      (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (P.curve t)) majorant
      (f (P.curve t) , derivativeSum t lo hi) majorantSum
      (formalDerivativeℂTermBound coefficients (P.curve t) radius (bounded t lo hi))

  opaque
    powerSeriesDerivativeHasComplexLineIntegral :
      HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
    powerSeriesDerivativeHasComplexLineIntegral = PT.rec
      (isPropHasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path)))
      (λ { (n , below) → fundamentalTheoremOfComplexLineIntegrals path F f (naturalBound n)
        (λ t lo hi → ≤ℝ-trans (normℂ (f (P.curve t))) bound (rat (naturalRational n))
          (derivativeBound t lo hi) (<ℝ-weaken bound (rat (naturalRational n)) below))
        powerSeriesIsUniformPrimitiveAlongPath }) (∃naturalUpperBound bound)

  powerSeriesDerivativeComplexLineIntegrable : IsComplexLineIntegrable f path
  powerSeriesDerivativeComplexLineIntegrable =
    (F (pathFinish path) -ℂ F (pathStart path)) , powerSeriesDerivativeHasComplexLineIntegral

  closedPowerSeriesDerivativeHasZeroLineIntegral : pathFinish path ≡ pathStart path → HasComplexLineIntegral f path 0ℂ
  closedPowerSeriesDerivativeHasZeroLineIntegral closed = subst (HasComplexLineIntegral f path)
    (cong (λ z → F z -ℂ F (pathStart path)) closed ∙ +ℂInvR (F (pathStart path)))
    powerSeriesDerivativeHasComplexLineIntegral
