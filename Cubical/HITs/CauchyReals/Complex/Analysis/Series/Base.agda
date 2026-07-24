module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


partialSumℂ : ComplexSequence → ℕ → ℂ
partialSumℂ terms zero = 0ℂ
partialSumℂ terms (suc n) = partialSumℂ terms n +ℂ terms n


SeriesConvergesToℂ : ComplexSequence → ℂ → Type₀
SeriesConvergesToℂ terms = ConvergesToℂ (partialSumℂ terms)


ConvergentComplexSeries : ComplexSequence → Type₀
ConvergentComplexSeries terms =
  Σ[ sum ∈ ℂ ] SeriesConvergesToℂ terms sum


IsCauchySeriesℂ : ComplexSequence → Type₀
IsCauchySeriesℂ terms = IsCauchySequenceℂ (partialSumℂ terms)


sumCauchySeries : ∀ terms →
  IsCauchySeriesℂ terms → HasComplexLimit (partialSumℂ terms)
sumCauchySeries terms cauchy =
  fst (complexSequenceLimitPackage (partialSumℂ terms) cauchy) ,
  cauchySequenceConverges (partialSumℂ terms) cauchy


opaque
  partialSum-add : ∀ a b n →
    partialSumℂ (λ k → a k +ℂ b k) n ≡
    partialSumℂ a n +ℂ partialSumℂ b n
  partialSum-add a b zero = sym (+ℂIdR 0ℂ)
  partialSum-add a b (suc n) =
    cong (_+ℂ (a n +ℂ b n)) (partialSum-add a b n)
    ∙ ℂ≡ ℝ! ℝ!


opaque
  partialSum-scale : ∀ c a n →
    partialSumℂ (λ k → c ·ℂ a k) n ≡ c ·ℂ partialSumℂ a n
  partialSum-scale c a zero = sym (Cℂ.0RightAnnihilates c)
  partialSum-scale c a (suc n) =
    cong (_+ℂ (c ·ℂ a n)) (partialSum-scale c a n)
    ∙ sym (Cℂ.·DistR+ c (partialSumℂ a n) (a n))


opaque
  partialSum-conj : ∀ a n →
    partialSumℂ (conj ∘ a) n ≡ conj (partialSumℂ a n)
  partialSum-conj a zero = sym conj-pres0
  partialSum-conj a (suc n) =
    cong (_+ℂ conj (a n)) (partialSum-conj a n)
    ∙ sym (conj-pres+ (partialSumℂ a n) (a n))


powerTerm : ComplexSequence → ℂ → ComplexSequence
powerTerm coefficients z n = coefficients n ·ℂ (z ^ℂ n)


powerPartialSum : ComplexSequence → ℂ → ℕ → ℂ
powerPartialSum coefficients z = partialSumℂ (powerTerm coefficients z)


PowerSeriesConvergesTo : ComplexSequence → ℂ → ℂ → Type₀
PowerSeriesConvergesTo coefficients z =
  SeriesConvergesToℂ (powerTerm coefficients z)


PowerSeriesConvergesAt : ComplexSequence → ℂ → Type₀
PowerSeriesConvergesAt coefficients z =
  Σ[ sum ∈ ℂ ] PowerSeriesConvergesTo coefficients z sum


geometricTerms : ℂ → ComplexSequence
geometricTerms z n = z ^ℂ n


opaque
  geometricPartialSumStep : ∀ z n →
    (1ℂ -ℂ z) ·ℂ partialSumℂ (geometricTerms z) (suc n) ≡
    (1ℂ -ℂ z) ·ℂ partialSumℂ (geometricTerms z) n +ℂ
      (1ℂ -ℂ z) ·ℂ (z ^ℂ n)
  geometricPartialSumStep z n =
    Cℂ.·DistR+ (1ℂ -ℂ z)
      (partialSumℂ (geometricTerms z) n) (z ^ℂ n)


opaque
  geometricPartialSumTail : ∀ z n →
    (1ℂ -ℂ (z ^ℂ n)) +ℂ ((1ℂ -ℂ z) ·ℂ (z ^ℂ n)) ≡
      1ℂ -ℂ (z ^ℂ (suc n))
  geometricPartialSumTail z n =
    let p = z ^ℂ n
        q = z ·ℂ p
    in cong ((1ℂ -ℂ p) +ℂ_) (Cℂ.·DistL- 1ℂ z p)
      ∙ cong ((1ℂ -ℂ p) +ℂ_) (cong (_-ℂ q) (Cℂ.·IdL p))
      ∙ Cℂ.+Assoc (1ℂ -ℂ p) p (-ℂ q)
      ∙ cong (_-ℂ q) (Cℂ.minusPlus 1ℂ p)


opaque
  geometricPartialSum : ∀ z n →
    (1ℂ -ℂ z) ·ℂ partialSumℂ (geometricTerms z) n ≡
    1ℂ -ℂ (z ^ℂ n)
  geometricPartialSum z zero = ℂ≡ ℝ! ℝ!
  geometricPartialSum z (suc n) =
    geometricPartialSumStep z n
    ∙ cong (_+ℂ ((1ℂ -ℂ z) ·ℂ (z ^ℂ n)))
        (geometricPartialSum z n)
    ∙ geometricPartialSumTail z n
