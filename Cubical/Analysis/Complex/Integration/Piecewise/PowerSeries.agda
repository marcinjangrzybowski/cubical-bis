module Cubical.Analysis.Complex.Integration.Piecewise.PowerSeries where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
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
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Centered
open import Cubical.Analysis.Complex.Integration.Piecewise.Base
open import Cubical.Analysis.Complex.Integration.Piecewise.FundamentalTheorem

-- Each certified piece may have its own center, coefficients and radii.
-- The common F and f identify the local sums, including at shared endpoints.
-- These data assert a power-series representation, not mere holomorphicity.
CenteredPowerSeriesPrimitiveData : (ℂ → ℂ) → (ℂ → ℂ) → ∀ {a b} → UniformComplexPath a b → Type₀
CenteredPowerSeriesPrimitiveData F f {a} {b} path =
  Σ[ center ∈ ℂ ] Σ[ coefficients ∈ ComplexSequence ] Σ[ inner ∈ ℝ ] Σ[ outer ∈ ℝ ]
  (0ℝ ≤ℝ inner) × (inner <ℝ outer) ×
  (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t -ℂ center) ≤ℝ inner) ×
  Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer) ×
  (∀ t → a ≤ℝ t → t ≤ℝ b → HasComplexSum
    (powerSeriesTermsℂ coefficients (UniformComplexPath.curve path t -ℂ center)) (F (UniformComplexPath.curve path t))) ×
  (∀ t → a ≤ℝ t → t ≤ℝ b → HasComplexSum
    (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (UniformComplexPath.curve path t -ℂ center)) (f (UniformComplexPath.curve path t)))

centeredPowerSeriesPrimitiveDataHasLineIntegral : ∀ F f {a b} (path : UniformComplexPath a b) →
  CenteredPowerSeriesPrimitiveData F f path →
  HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
centeredPowerSeriesPrimitiveDataHasLineIntegral F f path
  (center , coefficients , inner , outer , nonnegative , strict , bounded , witness , originalSum , derivativeSum) =
  centeredPowerSeriesDerivativeHasComplexLineIntegral path F f coefficients center inner outer
    nonnegative strict bounded witness originalSum derivativeSum

-- Local certificates may remain truncated: each is eliminated directly into
-- the proposition that its integral has the endpoint value. Finite telescoping
-- then supplies the actual piecewise integral without choosing expansions.
piecewiseCenteredPowerSeriesHasLineIntegral : ∀ F f {z w} (chain : PiecewiseComplexPath z w) →
  AllComplexPieces (λ path → PT.∥ CenteredPowerSeriesPrimitiveData F f path ∥₁) chain →
  HasPiecewiseComplexLineIntegral f chain (F w -ℂ F z)
piecewiseCenteredPowerSeriesHasLineIntegral F f chain localData =
  piecewisePrimitiveFromPieceIntegrals F f chain
    (mapAllComplexPieces (λ path → PT.∥ CenteredPowerSeriesPrimitiveData F f path ∥₁)
      (λ path → HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path)))
      (λ path → PT.rec (isPropHasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path)))
        (centeredPowerSeriesPrimitiveDataHasLineIntegral F f path)) chain localData)

closedPiecewiseCenteredPowerSeriesHasZeroIntegral : ∀ F f {z} (chain : PiecewiseComplexPath z z) →
  AllComplexPieces (λ path → PT.∥ CenteredPowerSeriesPrimitiveData F f path ∥₁) chain →
  HasPiecewiseComplexLineIntegral f chain 0ℂ
closedPiecewiseCenteredPowerSeriesHasZeroIntegral F f {z} chain localData =
  subst (HasPiecewiseComplexLineIntegral f chain) (+ℂInvR (F z))
    (piecewiseCenteredPowerSeriesHasLineIntegral F f chain localData)

piecewiseCenteredPowerSeriesPathIndependent : ∀ F f {z w} (first second : PiecewiseComplexPath z w) →
  AllComplexPieces (λ path → PT.∥ CenteredPowerSeriesPrimitiveData F f path ∥₁) first →
  AllComplexPieces (λ path → PT.∥ CenteredPowerSeriesPrimitiveData F f path ∥₁) second →
  ∀ v u → HasPiecewiseComplexLineIntegral f first v → HasPiecewiseComplexLineIntegral f second u → v ≡ u
piecewiseCenteredPowerSeriesPathIndependent F f {z} {w} first second firstData secondData v u vi ui =
  piecewiseComplexLineIntegralUnique f first v (F w -ℂ F z) vi
    (piecewiseCenteredPowerSeriesHasLineIntegral F f first firstData)
  ∙ sym (piecewiseComplexLineIntegralUnique f second u (F w -ℂ F z) ui
    (piecewiseCenteredPowerSeriesHasLineIntegral F f second secondData))
