module Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Interior where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.InteriorConvergence
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries

-- A path contained in a strictly smaller norm radius needs only the native
-- ORIGINAL majorant at the outer radius. The derivative convergence, uniform
-- primitive estimate, integrand bound and integrability are all consequences.
-- F and f represent the two sums on the path; their off-path values are free.
module _ {a b : ℝ} (path : UniformComplexPath a b) (F f : ℂ → ℂ)
  (coefficients : ComplexSequence) (inner outer : ℝ)
  (positive : 0ℝ ≤ℝ inner) (strict : inner <ℝ outer)
  (bounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t) ≤ℝ inner)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (originalSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ coefficients (UniformComplexPath.curve path t)) (F (UniformComplexPath.curve path t)))
  (derivativeSum : ∀ t → a ≤ℝ t → t ≤ℝ b →
    HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (UniformComplexPath.curve path t)) (f (UniformComplexPath.curve path t))) where

  private
    derivativeWitness : Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients inner)
    derivativeWitness = complexPowerSeriesDerivativeMajorantIsCauchyAtInterior coefficients inner outer positive strict witness

  powerSeriesIsUniformPrimitiveAlongPathFromOuterRadius : IsUniformPrimitiveAlongPath F f path
  powerSeriesIsUniformPrimitiveAlongPathFromOuterRadius = powerSeriesIsUniformPrimitiveAlongPath
    path F f coefficients inner bounded derivativeWitness originalSum derivativeSum

  powerSeriesDerivativeHasComplexLineIntegralFromOuterRadius :
    HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
  powerSeriesDerivativeHasComplexLineIntegralFromOuterRadius = powerSeriesDerivativeHasComplexLineIntegral
    path F f coefficients inner bounded derivativeWitness originalSum derivativeSum

  powerSeriesDerivativeComplexLineIntegrableFromOuterRadius : IsComplexLineIntegrable f path
  powerSeriesDerivativeComplexLineIntegrableFromOuterRadius = powerSeriesDerivativeComplexLineIntegrable
    path F f coefficients inner bounded derivativeWitness originalSum derivativeSum

  closedPowerSeriesDerivativeHasZeroLineIntegralFromOuterRadius :
    pathFinish path ≡ pathStart path → HasComplexLineIntegral f path 0ℂ
  closedPowerSeriesDerivativeHasZeroLineIntegralFromOuterRadius = closedPowerSeriesDerivativeHasZeroLineIntegral
    path F f coefficients inner bounded derivativeWitness originalSum derivativeSum
