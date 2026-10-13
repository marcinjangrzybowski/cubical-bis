module Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Primitive where

open import Cubical.Foundations.Prelude
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Along
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem.Along
open import Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Primitive.Path

-- The integrand and primitive are both constructed from the coefficient
-- sequence. Native convergence at the path's closed radius suffices; no
-- separate primitive, derivative majorant or strict radius gap is supplied.
module _ {a b : ℝ} (path : UniformComplexPath a b) (center : ℂ)
  (coefficients : ComplexSequence) (radius : ℝ) (nonnegative : 0ℝ ≤ℝ radius)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t -ℂ center) ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius)) (constant : ℂ) where
  private
    module P = UniformComplexPath path
    value antiderivative : ℝ → ℂ
    value = powerSeriesPathValue path center coefficients radius bounded witness
    antiderivative = powerSeriesPathPrimitive path center coefficients radius bounded witness constant nonnegative
    majorant : Real.RealSequence
    majorant = complexPowerSeriesMajorant coefficients radius
    majorantSum : Real.Summable majorant
    majorantSum = Real.cauchySeriesIsSummable majorant witness
    bound : ℝ
    bound = Real.seriesSum majorant majorantSum

    valueBound : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (value t) ≤ℝ bound
    valueBound t lo hi = seriesSumℂBoundBy (powerSeriesTermsℂ coefficients (P.curve t -ℂ center)) majorant
      (value t , powerSeriesPathHasSum path center coefficients radius bounded witness t lo hi) majorantSum
      (complexPowerSeriesTermBound coefficients (P.curve t -ℂ center) radius (bounded t lo hi))

  opaque
    convergentPowerSeriesHasLineIntegralAlong : HasComplexLineIntegralAlong value path (antiderivative b -ℂ antiderivative a)
    convergentPowerSeriesHasLineIntegralAlong = PT.rec
      (isPropHasComplexRiemannIntegralOn (complexLineIntegrandAlong value path) a b (antiderivative b -ℂ antiderivative a))
      (λ { (n , below) → fundamentalTheoremOfComplexLineIntegralsAlong path antiderivative value (naturalBound n)
        (λ t lo hi → ≤ℝ-trans (normℂ (value t)) bound (rat (naturalRational n))
          (valueBound t lo hi) (<ℝ-weaken bound (rat (naturalRational n)) below))
        (powerSeriesPathHasUniformPrimitive path center coefficients radius bounded witness constant nonnegative) })
      (∃naturalUpperBound bound)

  convergentPowerSeriesLineIntegrableAlong : IsComplexLineIntegrableAlong value path
  convergentPowerSeriesLineIntegrableAlong = (antiderivative b -ℂ antiderivative a) , convergentPowerSeriesHasLineIntegralAlong

  closedConvergentPowerSeriesHasZeroLineIntegralAlong : pathFinish path ≡ pathStart path → HasComplexLineIntegralAlong value path 0ℂ
  closedConvergentPowerSeriesHasZeroLineIntegralAlong closed = subst (HasComplexLineIntegralAlong value path)
    (cong (_-ℂ antiderivative a)
      (powerSeriesPathPrimitiveEndpointsAgree path center coefficients radius bounded witness constant nonnegative closed)
      ∙ +ℂInvR (antiderivative a)) convergentPowerSeriesHasLineIntegralAlong

  -- Any supplied ambient integrand representing the original series only on
  -- the path has the same integral. No ambient primitive is requested.
  module _ (f : ℂ → ℂ)
    (sums : ∀ t → a ≤ℝ t → t ≤ℝ b → HasComplexSum
      (powerSeriesTermsℂ coefficients (P.curve t -ℂ center)) (f (P.curve t))) where

    convergentPowerSeriesHasComplexLineIntegral : HasComplexLineIntegral f path (antiderivative b -ℂ antiderivative a)
    convergentPowerSeriesHasComplexLineIntegral = complexHasIntegralCongOn
      (complexLineIntegrandAlong value path) (complexLineIntegrand f path) a b (antiderivative b -ℂ antiderivative a)
      (λ t lo hi → cong (_·ℂ P.velocity t)
        (complexSumUnique (powerSeriesTermsℂ coefficients (P.curve t -ℂ center)) (value t) (f (P.curve t))
          (powerSeriesPathHasSum path center coefficients radius bounded witness t lo hi) (sums t lo hi)))
      convergentPowerSeriesHasLineIntegralAlong

    convergentPowerSeriesComplexLineIntegrable : IsComplexLineIntegrable f path
    convergentPowerSeriesComplexLineIntegrable = (antiderivative b -ℂ antiderivative a) , convergentPowerSeriesHasComplexLineIntegral

    convergentPowerSeriesIntegralFromEndpointSums : ∀ start finish →
      HasComplexSum (powerSeriesTermsℂ (formalPrimitiveℂ constant coefficients) (pathStart path -ℂ center)) start →
      HasComplexSum (powerSeriesTermsℂ (formalPrimitiveℂ constant coefficients) (pathFinish path -ℂ center)) finish →
      HasComplexLineIntegral f path (finish -ℂ start)
    convergentPowerSeriesIntegralFromEndpointSums start finish startSum finishSum = subst (HasComplexLineIntegral f path)
      (cong₂ _-ℂ_
        (complexSumUnique (powerSeriesTermsℂ (formalPrimitiveℂ constant coefficients) (pathFinish path -ℂ center))
          (antiderivative b) finish
          (powerSeriesPathPrimitiveHasSum path center coefficients radius bounded witness constant nonnegative b P.ordered (≤ℝ-refl b)) finishSum)
        (complexSumUnique (powerSeriesTermsℂ (formalPrimitiveℂ constant coefficients) (pathStart path -ℂ center))
          (antiderivative a) start
          (powerSeriesPathPrimitiveHasSum path center coefficients radius bounded witness constant nonnegative a (≤ℝ-refl a) P.ordered) startSum))
      convergentPowerSeriesHasComplexLineIntegral

    closedConvergentPowerSeriesHasZeroLineIntegral : pathFinish path ≡ pathStart path → HasComplexLineIntegral f path 0ℂ
    closedConvergentPowerSeriesHasZeroLineIntegral closed = subst (HasComplexLineIntegral f path)
      (cong (_-ℂ antiderivative a)
        (powerSeriesPathPrimitiveEndpointsAgree path center coefficients radius bounded witness constant nonnegative closed)
        ∙ +ℂInvR (antiderivative a)) convergentPowerSeriesHasComplexLineIntegral
