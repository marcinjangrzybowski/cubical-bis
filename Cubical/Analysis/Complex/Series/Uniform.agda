module Cubical.Analysis.Complex.Series.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Uniform as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base

-- Each coordinate has one (merely supplied) modulus valid at every point.
-- This is stronger than separate pointwise Cauchy witnesses. Combining two
-- coordinate witnesses is finite and needs no choice over the parameter set.
UniformlyComplexCauchySeries : ∀ {ℓ} (A : Type ℓ) → (A → ComplexSequence) → Type ℓ
UniformlyComplexCauchySeries A terms =
  Real.UniformlyCauchySeries A (λ x → re ∘ terms x) ×
  Real.UniformlyCauchySeries A (λ x → im ∘ terms x)

UniformHasComplexSum : ∀ {ℓ} {A : Type ℓ} → (A → ComplexSequence) → (A → ℂ) → Type ℓ
UniformHasComplexSum terms value =
  Real.UniformHasSum (λ x → re ∘ terms x) (re ∘ value) ×
  Real.UniformHasSum (λ x → im ∘ terms x) (im ∘ value)

isPropUniformlyComplexCauchySeries : ∀ {ℓ} (A : Type ℓ) terms → isProp (UniformlyComplexCauchySeries A terms)
isPropUniformlyComplexCauchySeries A terms = isProp×
  (Real.isPropUniformlyCauchySeries A (λ x → re ∘ terms x))
  (Real.isPropUniformlyCauchySeries A (λ x → im ∘ terms x))

isPropUniformHasComplexSum : ∀ {ℓ} {A : Type ℓ} (terms : A → ComplexSequence) value →
  isProp (UniformHasComplexSum terms value)
isPropUniformHasComplexSum terms value = isProp×
  (Real.isPropUniformHasSum (λ x → re ∘ terms x) (re ∘ value))
  (Real.isPropUniformHasSum (λ x → im ∘ terms x) (im ∘ value))

uniformlyComplexCauchySeriesAt : ∀ {ℓ} {A : Type ℓ} {terms} →
  UniformlyComplexCauchySeries A terms → ∀ x → IsComplexCauchySeries (terms x)
uniformlyComplexCauchySeriesAt uniform x =
  Real.uniformlyCauchySeriesAt (fst uniform) x , Real.uniformlyCauchySeriesAt (snd uniform) x

uniformHasComplexSumAt : ∀ {ℓ} {A : Type ℓ} {terms : A → ComplexSequence} {value} →
  UniformHasComplexSum terms value → ∀ x → HasComplexSum (terms x) (value x)
uniformHasComplexSumAt uniform x = Real.uniformHasSumAt (fst uniform) x , Real.uniformHasSumAt (snd uniform) x

uniformComplexSeriesValue : ∀ {ℓ} {A : Type ℓ} (terms : A → ComplexSequence) →
  UniformlyComplexCauchySeries A terms → A → ℂ
uniformComplexSeriesValue terms uniform x =
  Real.uniformSeriesValue (λ y → re ∘ terms y) (fst uniform) x ,
  Real.uniformSeriesValue (λ y → im ∘ terms y) (snd uniform) x

uniformlyComplexCauchySeriesHasUniformSum : ∀ {ℓ} {A : Type ℓ} (terms : A → ComplexSequence)
  (uniform : UniformlyComplexCauchySeries A terms) → UniformHasComplexSum terms (uniformComplexSeriesValue terms uniform)
uniformlyComplexCauchySeriesHasUniformSum terms uniform =
  Real.uniformlyCauchySeriesHasUniformSum (λ x → re ∘ terms x) (fst uniform) ,
  Real.uniformlyCauchySeriesHasUniformSum (λ x → im ∘ terms x) (snd uniform)

uniformComplexSeriesValueAgrees : ∀ {ℓ} {A : Type ℓ} (terms : A → ComplexSequence)
  (uniform : UniformlyComplexCauchySeries A terms) x (summed : ComplexSummable (terms x)) →
  uniformComplexSeriesValue terms uniform x ≡ seriesSumℂ (terms x) summed
uniformComplexSeriesValueAgrees terms uniform x summed = complexSumUnique (terms x)
  (uniformComplexSeriesValue terms uniform x) (seriesSumℂ (terms x) summed)
  (uniformHasComplexSumAt (uniformlyComplexCauchySeriesHasUniformSum terms uniform) x) (snd summed)

uniformlyComplexCauchySeriesPrecompose : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (terms : A → ComplexSequence) (mapping : B → A) → UniformlyComplexCauchySeries A terms →
  UniformlyComplexCauchySeries B (terms ∘ mapping)
uniformlyComplexCauchySeriesPrecompose terms mapping (real , imaginary) =
  Real.uniformlyCauchySeriesPrecompose (λ x → re ∘ terms x) mapping real ,
  Real.uniformlyCauchySeriesPrecompose (λ x → im ∘ terms x) mapping imaginary

opaque
  uniformlyDominatedComplexSeriesIsUniformlyCauchy : ∀ {ℓ} {A : Type ℓ}
    (terms : A → ComplexSequence) bound → (∀ x n → normℂ (terms x n) ≤ℝ bound n) →
    Real.IsCauchySeries bound → UniformlyComplexCauchySeries A terms
  uniformlyDominatedComplexSeriesIsUniformlyCauchy terms bound dominates witness =
    Real.uniformlyDominatedSeriesIsUniformlyCauchy (λ x → re ∘ terms x) bound
      (λ x n → ≤ℝ-trans (absℝ (re (terms x n))) (normℂ (terms x n)) (bound n)
        (reAbs≤normℂ (terms x n)) (dominates x n)) witness ,
    Real.uniformlyDominatedSeriesIsUniformlyCauchy (λ x → im ∘ terms x) bound
      (λ x n → ≤ℝ-trans (absℝ (im (terms x n))) (normℂ (terms x n)) (bound n)
        (imAbs≤normℂ (terms x n)) (dominates x n)) witness

-- Continuity is transferred from the real uniform-limit theorem, rather
-- than proved again using a new complex epsilon estimate.
uniformComplexSeriesValueIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (terms : A → ComplexSequence)
  (uniform : UniformlyComplexCauchySeries A terms) →
  (∀ n → isContinuous source (λ x → terms x n) (ℂPremetricSpace .snd)) →
  isContinuous source (uniformComplexSeriesValue terms uniform) (ℂPremetricSpace .snd)
uniformComplexSeriesValueIsContinuous source terms uniform continuous = pairℂ-isContinuous source
  (Real.uniformSeriesValue (λ x → re ∘ terms x) (fst uniform))
  (Real.uniformSeriesValue (λ x → im ∘ terms x) (snd uniform))
  (Real.uniformSeriesValueIsContinuous source (λ x → re ∘ terms x) (fst uniform)
    (λ n → reOfComplexContinuous source (λ x → terms x n) (continuous n)))
  (Real.uniformSeriesValueIsContinuous source (λ x → im ∘ terms x) (snd uniform)
    (λ n → imOfComplexContinuous source (λ x → terms x n) (continuous n)))
