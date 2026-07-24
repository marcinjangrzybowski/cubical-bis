module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Scaling where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Metric.Continuity
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Mapping.Lipschitz


scaleConverges :
  ∀ c →
  ComplexScalarBound c →
  (sequence : ComplexSequence) → (limit : ℂ) →
  ConvergesToℂ sequence limit →
  ConvergesToℂ
    (λ n → leftMultiplyℂ c (sequence n))
    (leftMultiplyℂ c limit)
scaleConverges
  c bound sequence limit converges =
  mapConvergesLipschitzWith
    (fst bound)
    (leftMultiplyℂ c)
    (leftMultiplyℂIsLipschitzWith c bound)
    sequence limit converges


scaleCauchy :
  ∀ c →
  ComplexScalarBound c →
  (sequence : ComplexSequence) →
  IsCauchySequenceℂ sequence →
  IsCauchySequenceℂ
    (λ n → leftMultiplyℂ c (sequence n))
scaleCauchy
  c bound sequence cauchy =
  mapCauchyLipschitzWith
    (fst bound)
    (leftMultiplyℂ c)
    (leftMultiplyℂIsLipschitzWith c bound)
    sequence cauchy
