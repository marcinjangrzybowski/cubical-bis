module Cubical.Analysis.Complex.Series.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Series.Base as Real using ()
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence

-- Reuse the native real finite sums; their coordinate equations compute.
partialSumℂ : ComplexSequence → ComplexSequence
partialSumℂ terms n = Real.partialSum (re ∘ terms) n , Real.partialSum (im ∘ terms) n

partialSumℂ-zero : ∀ terms → partialSumℂ terms zero ≡ 0ℂ
partialSumℂ-zero terms = refl

partialSumℂ-step : ∀ terms n → partialSumℂ terms (suc n) ≡ partialSumℂ terms n +ℂ terms n
partialSumℂ-step terms n = refl

partialSumℂ-pointwise : ∀ a b → (∀ n → a n ≡ b n) → ∀ n → partialSumℂ a n ≡ partialSumℂ b n
partialSumℂ-pointwise a b equal n = ℂ≡
  (Real.partialSum-pointwise (re ∘ a) (re ∘ b) (λ k → cong re (equal k)) n)
  (Real.partialSum-pointwise (im ∘ a) (im ∘ b) (λ k → cong im (equal k)) n)

HasComplexSum : ComplexSequence → ℂ → Type₀
HasComplexSum terms = IsComplexLimit (partialSumℂ terms)

ComplexSummable : ComplexSequence → Type₀
ComplexSummable terms = Σ[ value ∈ ℂ ] HasComplexSum terms value

-- Two supplied global native witnesses, each under one truncation.
-- Radiuswise truncated tail existence is not used to construct these.
IsComplexCauchySeries : ComplexSequence → Type₀
IsComplexCauchySeries terms = ComplexSeqWitness (partialSumℂ terms)

isPropHasComplexSum : ∀ terms value → isProp (HasComplexSum terms value)
isPropHasComplexSum terms = isPropIsComplexLimit (partialSumℂ terms)

complexSumUnique : ∀ terms x y → HasComplexSum terms x → HasComplexSum terms y → x ≡ y
complexSumUnique terms = complexLimitUnique (partialSumℂ terms)

isPropComplexSummable : ∀ terms → isProp (ComplexSummable terms)
isPropComplexSummable terms (x , xs) (y , ys) = Σ≡Prop (isPropHasComplexSum terms)
  (complexSumUnique terms x y xs ys)

isPropIsComplexCauchySeries : ∀ terms → isProp (IsComplexCauchySeries terms)
isPropIsComplexCauchySeries terms = isPropComplexSeqWitness (partialSumℂ terms)

complexCauchySeriesIsSummable : ∀ terms → IsComplexCauchySeries terms → ComplexSummable terms
complexCauchySeriesIsSummable terms witness =
  limitℂ (partialSumℂ terms) witness , limitℂ-isLimit (partialSumℂ terms) witness

seriesSumℂ : ∀ terms → ComplexSummable terms → ℂ
seriesSumℂ terms summable = fst summable

seriesSumℂHasSum : ∀ terms summable → HasComplexSum terms (seriesSumℂ terms summable)
seriesSumℂHasSum terms summable = snd summable

seriesSumℂIndependent : ∀ terms (p q : ComplexSummable terms) → seriesSumℂ terms p ≡ seriesSumℂ terms q
seriesSumℂIndependent terms p q = cong fst (isPropComplexSummable terms p q)

complexHasSumPointwise : ∀ a b → (∀ n → a n ≡ b n) → ∀ value →
  HasComplexSum a value → HasComplexSum b value
complexHasSumPointwise a b equal value = subst (λ terms → HasComplexSum terms value) (funExt equal)

-- Explicit coordinate bridges, with no new convergence notion or choice.
complexSummableCoordinates : ∀ terms → ComplexSummable terms →
  Real.Summable (re ∘ terms) × Real.Summable (im ∘ terms)
complexSummableCoordinates terms (value , real , imaginary) =
  (re value , real) , (im value , imaginary)

coordinatesComplexSummable : ∀ terms →
  Real.Summable (re ∘ terms) → Real.Summable (im ∘ terms) → ComplexSummable terms
coordinatesComplexSummable terms (x , xs) (y , ys) = (x , y) , xs , ys

complexSummableTermsTendToZero : ∀ terms → ComplexSummable terms → IsComplexLimit terms 0ℂ
complexSummableTermsTendToZero terms summable =
  Real.summableTermsTendToZero (re ∘ terms) (fst (complexSummableCoordinates terms summable)) ,
  Real.summableTermsTendToZero (im ∘ terms) (snd (complexSummableCoordinates terms summable))
