module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Mapping.Isometries where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.Metric.Mappings
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Mapping.NonExpanding


translateConverges : ∀ u sequence limit →
  ConvergesToℂ sequence limit →
  ConvergesToℂ (λ n → sequence n +ℂ u) (limit +ℂ u)
translateConverges u sequence limit (N , converges) =
  mapConvergesPres≈ (_+ℂ u) (translateℂ-pres≈ u)
    sequence limit (N , converges)


translateCauchy : ∀ u sequence →
  IsCauchySequenceℂ sequence →
  IsCauchySequenceℂ (λ n → sequence n +ℂ u)
translateCauchy u sequence (N , cauchy) =
  mapCauchyPres≈ (_+ℂ u) (translateℂ-pres≈ u)
    sequence (N , cauchy)


negConverges : ∀ sequence limit →
  ConvergesToℂ sequence limit →
  ConvergesToℂ (λ n → -ℂ sequence n) (-ℂ limit)
negConverges sequence limit (N , converges) =
  mapConvergesPres≈ -ℂ_ negℂ-pres≈
    sequence limit (N , converges)


negCauchy : ∀ sequence →
  IsCauchySequenceℂ sequence →
  IsCauchySequenceℂ (λ n → -ℂ sequence n)
negCauchy sequence (N , cauchy) =
  mapCauchyPres≈ -ℂ_ negℂ-pres≈
    sequence (N , cauchy)


conjConverges : ∀ sequence limit →
  ConvergesToℂ sequence limit →
  ConvergesToℂ (λ n → conj (sequence n)) (conj limit)
conjConverges sequence limit (N , converges) =
  mapConvergesPres≈ conj conj-pres≈
    sequence limit (N , converges)


conjCauchy : ∀ sequence →
  IsCauchySequenceℂ sequence →
  IsCauchySequenceℂ (λ n → conj (sequence n))
conjCauchy sequence (N , cauchy) =
  mapCauchyPres≈ conj conj-pres≈
    sequence (N , cauchy)
