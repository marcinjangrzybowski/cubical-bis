module Cubical.Analysis.Complex.Integration.Piecewise.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Bounded
open import Cubical.Analysis.Complex.Integration.LineIntegral.Exponential
open import Cubical.Analysis.Complex.Integration.Piecewise.Base
open import Cubical.Analysis.Complex.Integration.Piecewise.FundamentalTheorem

exponentialHasPiecewiseComplexLineIntegral : ∀ {z w} (chain : PiecewiseComplexPath z w) →
  HasPiecewiseComplexLineIntegral expℂ chain (expℂ w -ℂ expℂ z)
exponentialHasPiecewiseComplexLineIntegral chain = fundamentalTheoremOfPiecewiseComplexLineIntegrals expℂ expℂ chain
  (allComplexPieces (IsBoundedUniformPrimitiveAlongPath expℂ expℂ) exponentialIsBoundedUniformPrimitiveAlongPath chain)

closedExponentialHasZeroPiecewiseIntegral : ∀ {z} (chain : PiecewiseComplexPath z z) → HasPiecewiseComplexLineIntegral expℂ chain 0ℂ
closedExponentialHasZeroPiecewiseIntegral {z} chain =
  subst (HasPiecewiseComplexLineIntegral expℂ chain) (+ℂInvR (expℂ z)) (exponentialHasPiecewiseComplexLineIntegral chain)
