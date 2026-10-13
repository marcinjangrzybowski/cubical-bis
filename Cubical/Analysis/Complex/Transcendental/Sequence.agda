module Cubical.Analysis.Complex.Transcendental.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Sequence.Continuous
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Continuity
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Continuity

expComplexLimit : ∀ {z l} → IsComplexLimit z l → IsComplexLimit (λ n → expℂ (z n)) (expℂ l)
expComplexLimit = continuousComplexMapPreservesLimit expℂ expℂ-isContinuous

sinComplexLimit : ∀ {z l} → IsComplexLimit z l → IsComplexLimit (λ n → sinℂ (z n)) (sinℂ l)
sinComplexLimit = continuousComplexMapPreservesLimit sinℂ sinℂ-isContinuous

cosComplexLimit : ∀ {z l} → IsComplexLimit z l → IsComplexLimit (λ n → cosℂ (z n)) (cosℂ l)
cosComplexLimit = continuousComplexMapPreservesLimit cosℂ cosℂ-isContinuous
