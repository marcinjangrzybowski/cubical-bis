module Cubical.Analysis.Complex.Series.Tails where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Analysis.Real.Series.Tails as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base

-- Use the same indexing convention as the real series tail API.
dropComplexSeries : ℕ → ComplexSequence → ComplexSequence
dropComplexSeries start terms n = terms (n ℕ.+ start)

partialSumℂ-drop : ∀ start terms n → partialSumℂ (dropComplexSeries start terms) n ≡
  partialSumℂ terms (n ℕ.+ start) -ℂ partialSumℂ terms start
partialSumℂ-drop start terms n = ℂ≡
  (Real.partialSum-drop start (re ∘ terms) n) (Real.partialSum-drop start (im ∘ terms) n)

partialSumℂ-drop-recombine : ∀ start terms n → partialSumℂ terms (n ℕ.+ start) ≡
  partialSumℂ terms start +ℂ partialSumℂ (dropComplexSeries start terms) n
partialSumℂ-drop-recombine start terms n = ℂ≡
  (Real.partialSum-drop-recombine start (re ∘ terms) n)
  (Real.partialSum-drop-recombine start (im ∘ terms) n)

dropComplexSeriesIsCauchy : ∀ start terms → IsComplexCauchySeries terms →
  IsComplexCauchySeries (dropComplexSeries start terms)
dropComplexSeriesIsCauchy start terms (real , imaginary) =
  Real.dropSeriesIsCauchy start (re ∘ terms) real , Real.dropSeriesIsCauchy start (im ∘ terms) imaginary

dropComplexSeriesHasSum : ∀ start terms value → HasComplexSum terms value →
  HasComplexSum (dropComplexSeries start terms) (value -ℂ partialSumℂ terms start)
dropComplexSeriesHasSum start terms value (real , imaginary) =
  Real.dropSeriesHasSum start (re ∘ terms) (re value) real ,
  Real.dropSeriesHasSum start (im ∘ terms) (im value) imaginary

dropComplexSeriesReflectsHasSum : ∀ start terms value → HasComplexSum (dropComplexSeries start terms) value →
  HasComplexSum terms (partialSumℂ terms start +ℂ value)
dropComplexSeriesReflectsHasSum start terms value (real , imaginary) =
  Real.dropSeriesReflectsHasSum start (re ∘ terms) (re value) real ,
  Real.dropSeriesReflectsHasSum start (im ∘ terms) (im value) imaginary

dropComplexSeriesSummable : ∀ start terms → ComplexSummable terms → ComplexSummable (dropComplexSeries start terms)
dropComplexSeriesSummable start terms (value , summed) =
  value -ℂ partialSumℂ terms start , dropComplexSeriesHasSum start terms value summed

dropComplexSeriesReflectsSummable : ∀ start terms → ComplexSummable (dropComplexSeries start terms) → ComplexSummable terms
dropComplexSeriesReflectsSummable start terms (value , summed) =
  partialSumℂ terms start +ℂ value , dropComplexSeriesReflectsHasSum start terms value summed

seriesSumℂ-drop : ∀ start terms (p : ComplexSummable terms) (q : ComplexSummable (dropComplexSeries start terms)) →
  seriesSumℂ (dropComplexSeries start terms) q ≡ seriesSumℂ terms p -ℂ partialSumℂ terms start
seriesSumℂ-drop start terms p q = seriesSumℂIndependent (dropComplexSeries start terms) q (dropComplexSeriesSummable start terms p)

seriesSumℂ-from-drop : ∀ start terms (p : ComplexSummable (dropComplexSeries start terms)) (q : ComplexSummable terms) →
  seriesSumℂ terms q ≡ partialSumℂ terms start +ℂ seriesSumℂ (dropComplexSeries start terms) p
seriesSumℂ-from-drop start terms p q = seriesSumℂIndependent terms q (dropComplexSeriesReflectsSummable start terms p)
