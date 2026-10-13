module Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Reexpansion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties using (subAddCancel)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (addPres≤L)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Density
open import Cubical.Analysis.Real.Domain.Interval
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Derivatives
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Centered

-- Apply canonical Taylor reexpansion to the FTC. A relative path bound and
-- one original outer majorant construct a convergent local expansion and its
-- differentiated sums. One intermediate radius is eliminated into the pair
-- of propositional conclusions, never into a chosen radiuswise modulus.
module _ {a b : ℝ} (path : UniformComplexPath a b) (F f : ℂ → ℂ)
  (coefficients : ComplexSequence) (outer : ℝ)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (center : ℂ) (inner : ℝ) (nonnegative : 0ℝ ≤ℝ inner)
  (fits : normℂ center + inner <ℝ outer)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t -ℂ center) ≤ℝ inner)
  (originalSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ coefficients (UniformComplexPath.curve path t)) (F (UniformComplexPath.curve path t)))
  (derivativeSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (UniformComplexPath.curve path t)) (f (UniformComplexPath.curve path t))) where
  private
    module P = UniformComplexPath path

    inside : normℂ center <ℝ outer
    inside = ≤<ℝ-trans (normℂ center) (normℂ center + inner) outer
      (subst (_≤ℝ normℂ center + inner) (addIdR (normℂ center))
        (addPres≤L 0ℝ inner (normℂ center) nonnegative)) fits

    translated : ComplexSequence
    translated = complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside

    restore : ∀ z → center +ℂ (z -ℂ center) ≡ z
    restore z = +ℂComm center (z -ℂ center) ∙ ℂRing.minusPlus z center

    Conclusion : Type₀
    Conclusion = IsUniformPrimitiveAlongPath F f path ×
      HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))

    conclusionIsProp : isProp Conclusion
    conclusionIsProp = isProp×
      (isPropIsRadiuswiseUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
        (P.curve ∘ fst) (F ∘ P.curve ∘ fst) (f ∘ P.curve ∘ fst))
      (isPropHasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path)))

    module AtRadius (localOuter : ℝ) (strict : inner <ℝ localOuter)
      (localFits : normℂ center + localOuter <ℝ outer) where
      localNonnegative : 0ℝ ≤ℝ localOuter
      localNonnegative = ≤ℝ-trans 0ℝ inner localOuter nonnegative (<ℝ-weaken inner localOuter strict)

      native : Real.IsCauchySeries (complexPowerSeriesMajorant translated localOuter)
      native = translatedTaylorMajorantIsCauchy coefficients outer witness center inside localOuter localNonnegative localFits

      point : ∀ t → a ≤ℝ t → t ≤ℝ b → OpenComplexNormRadius localOuter
      point t lo hi = P.curve t -ℂ center ,
        ≤<ℝ-trans (normℂ (P.curve t -ℂ center)) inner localOuter (bounded t lo hi) strict

      originalTranslatedSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
        HasComplexSum (powerSeriesTermsℂ translated (P.curve t -ℂ center)) (F (P.curve t))
      originalTranslatedSum t lo hi = translatedTaylorDerivativeHasSum coefficients outer witness center inside
        localOuter localNonnegative localFits 0 (point t lo hi) (F (P.curve t))
        (subst (λ z → HasComplexSum (powerSeriesTermsℂ coefficients z) (F (P.curve t)))
          (sym (restore (P.curve t))) (originalSum t lo hi))

      derivativeTranslatedSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
        HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ translated) (P.curve t -ℂ center)) (f (P.curve t))
      derivativeTranslatedSum t lo hi = subst
        (λ c → HasComplexSum (powerSeriesTermsℂ c (P.curve t -ℂ center)) (f (P.curve t)))
        (repeatedFormalDerivativeℂ-successor 0 translated)
        (translatedTaylorDerivativeHasSum coefficients outer witness center inside localOuter localNonnegative localFits
          1 (point t lo hi) (f (P.curve t))
          (subst (λ c → HasComplexSum (powerSeriesTermsℂ c (center +ℂ (P.curve t -ℂ center))) (f (P.curve t)))
            (sym (repeatedFormalDerivativeℂ-successor 0 coefficients))
            (subst (λ z → HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) z) (f (P.curve t)))
              (sym (restore (P.curve t))) (derivativeSum t lo hi))))

      result : Conclusion
      result = centeredPowerSeriesIsUniformPrimitiveAlongPath path F f translated center inner localOuter
        nonnegative strict bounded native originalTranslatedSum derivativeTranslatedSum ,
        centeredPowerSeriesDerivativeHasComplexLineIntegral path F f translated center inner localOuter
          nonnegative strict bounded native originalTranslatedSum derivativeTranslatedSum

    atIntermediate : ∀ middle → normℂ center + inner <ℝ middle → middle <ℝ outer → Conclusion
    atIntermediate middle below above = AtRadius.result localOuter strict localFits
      where
      localOuter : ℝ
      localOuter = middle - normℂ center
      restoreRadius : normℂ center + localOuter ≡ middle
      restoreRadius = addComm (normℂ center) localOuter ∙ subAddCancel middle (normℂ center)
      strict : inner <ℝ localOuter
      strict = <ℝ-addL-cancel inner localOuter (normℂ center)
        (subst (normℂ center + inner <ℝ_) (sym restoreRadius) below)
      localFits : normℂ center + localOuter <ℝ outer
      localFits = subst (_<ℝ outer) (sym restoreRadius) above

    opaque
      result : Conclusion
      result = PT.rec conclusionIsProp (λ { (q , below , above) → atIntermediate (rat q) below above })
        (denseℚinℝ (normℂ center + inner) outer fits)

  reexpandedPowerSeriesIsUniformPrimitiveAlongPath : IsUniformPrimitiveAlongPath F f path
  reexpandedPowerSeriesIsUniformPrimitiveAlongPath = fst result

  reexpandedPowerSeriesDerivativeHasComplexLineIntegral :
    HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
  reexpandedPowerSeriesDerivativeHasComplexLineIntegral = snd result

  reexpandedPowerSeriesDerivativeComplexLineIntegrable : IsComplexLineIntegrable f path
  reexpandedPowerSeriesDerivativeComplexLineIntegrable =
    (F (pathFinish path) -ℂ F (pathStart path)) , reexpandedPowerSeriesDerivativeHasComplexLineIntegral

  closedReexpandedPowerSeriesDerivativeHasZeroLineIntegral :
    pathFinish path ≡ pathStart path → HasComplexLineIntegral f path 0ℂ
  closedReexpandedPowerSeriesDerivativeHasZeroLineIntegral closed = subst (HasComplexLineIntegral f path)
    (cong (λ z → F z -ℂ F (pathStart path)) closed ∙ +ℂInvR (F (pathStart path)))
    reexpandedPowerSeriesDerivativeHasComplexLineIntegral
