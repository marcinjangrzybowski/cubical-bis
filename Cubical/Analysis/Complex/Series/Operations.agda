module Cubical.Analysis.Complex.Series.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Sequence
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Operations as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base

partialSumℂ-add : ∀ a b n → partialSumℂ (λ k → a k +ℂ b k) n ≡ partialSumℂ a n +ℂ partialSumℂ b n
partialSumℂ-add a b n = ℂ≡ (Real.partialSum-add (re ∘ a) (re ∘ b) n)
  (Real.partialSum-add (im ∘ a) (im ∘ b) n)

partialSumℂ-neg : ∀ a n → partialSumℂ (λ k → -ℂ a k) n ≡ -ℂ partialSumℂ a n
partialSumℂ-neg a n = ℂ≡ (Real.partialSum-neg (re ∘ a) n) (Real.partialSum-neg (im ∘ a) n)

partialSumℂ-sub : ∀ a b n → partialSumℂ (λ k → a k -ℂ b k) n ≡ partialSumℂ a n -ℂ partialSumℂ b n
partialSumℂ-sub a b n = ℂ≡ (Real.partialSum-sub (re ∘ a) (re ∘ b) n)
  (Real.partialSum-sub (im ∘ a) (im ∘ b) n)

scaleComplexSeries : ℂ → ComplexSequence → ComplexSequence
scaleComplexSeries c terms n = c ·ℂ terms n

opaque
  partialSumℂ-scale : ∀ c terms n → partialSumℂ (scaleComplexSeries c terms) n ≡ c ·ℂ partialSumℂ terms n
  partialSumℂ-scale c terms n = ℂ≡
    (Real.partialSum-sub (λ k → re c · re (terms k)) (λ k → im c · im (terms k)) n
      ∙ cong₂ _-_ (Real.partialSum-scale (re c) (re ∘ terms) n) (Real.partialSum-scale (im c) (im ∘ terms) n))
    (Real.partialSum-add (λ k → re c · im (terms k)) (λ k → im c · re (terms k)) n
      ∙ cong₂ _+_ (Real.partialSum-scale (re c) (im ∘ terms) n) (Real.partialSum-scale (im c) (re ∘ terms) n))

partialSumℂ-conjugate : ∀ terms n → partialSumℂ (conjugate ∘ terms) n ≡ conjugate (partialSumℂ terms n)
partialSumℂ-conjugate terms n = ℂ≡ refl (Real.partialSum-neg (im ∘ terms) n)

addHasComplexSum : ∀ a b x y → HasComplexSum a x → HasComplexSum b y → HasComplexSum (λ n → a n +ℂ b n) (x +ℂ y)
addHasComplexSum a b x y first second = subst (λ s → IsComplexLimit s (x +ℂ y))
  (sym (funExt (partialSumℂ-add a b))) (addComplexLimit first second)

negHasComplexSum : ∀ terms value → HasComplexSum terms value → HasComplexSum (λ n → -ℂ terms n) (-ℂ value)
negHasComplexSum terms value summed = subst (λ s → IsComplexLimit s (-ℂ value))
  (sym (funExt (partialSumℂ-neg terms))) (negComplexLimit summed)

subHasComplexSum : ∀ a b x y → HasComplexSum a x → HasComplexSum b y → HasComplexSum (λ n → a n -ℂ b n) (x -ℂ y)
subHasComplexSum a b x y first second = addHasComplexSum a (λ n → -ℂ b n) x (-ℂ y)
  first (negHasComplexSum b y second)

scaleHasComplexSum : ∀ c terms value → HasComplexSum terms value → HasComplexSum (scaleComplexSeries c terms) (c ·ℂ value)
scaleHasComplexSum c terms value summed = subst (λ s → IsComplexLimit s (c ·ℂ value))
  (sym (funExt (partialSumℂ-scale c terms))) (mulComplexLimit (constantComplexLimit c) summed)

conjugateHasComplexSum : ∀ terms value → HasComplexSum terms value → HasComplexSum (conjugate ∘ terms) (conjugate value)
conjugateHasComplexSum terms value summed = subst (λ s → IsComplexLimit s (conjugate value))
  (sym (funExt (partialSumℂ-conjugate terms))) (fst summed , negPresIsLimitSequence (snd summed))

zeroComplexSeriesSummable : ComplexSummable (λ _ → 0ℂ)
zeroComplexSeriesSummable = coordinatesComplexSummable (λ _ → 0ℂ) Real.zeroSeriesSummable Real.zeroSeriesSummable

addComplexSummable : ∀ a b → ComplexSummable a → ComplexSummable b → ComplexSummable (λ n → a n +ℂ b n)
addComplexSummable a b (x , xs) (y , ys) = x +ℂ y , addHasComplexSum a b x y xs ys

negComplexSummable : ∀ terms → ComplexSummable terms → ComplexSummable (λ n → -ℂ terms n)
negComplexSummable terms (value , summed) = -ℂ value , negHasComplexSum terms value summed

subComplexSummable : ∀ a b → ComplexSummable a → ComplexSummable b → ComplexSummable (λ n → a n -ℂ b n)
subComplexSummable a b (x , xs) (y , ys) = x -ℂ y , subHasComplexSum a b x y xs ys

scaleComplexSummable : ∀ c terms → ComplexSummable terms → ComplexSummable (scaleComplexSeries c terms)
scaleComplexSummable c terms (value , summed) = c ·ℂ value , scaleHasComplexSum c terms value summed

conjugateComplexSummable : ∀ terms → ComplexSummable terms → ComplexSummable (conjugate ∘ terms)
conjugateComplexSummable terms (value , summed) = conjugate value , conjugateHasComplexSum terms value summed

seriesSumℂ-add : ∀ a b (p : ComplexSummable a) (q : ComplexSummable b)
  (r : ComplexSummable (λ n → a n +ℂ b n)) →
  seriesSumℂ (λ n → a n +ℂ b n) r ≡ seriesSumℂ a p +ℂ seriesSumℂ b q
seriesSumℂ-add a b p q r = seriesSumℂIndependent (λ n → a n +ℂ b n) r (addComplexSummable a b p q)

seriesSumℂ-neg : ∀ terms (p : ComplexSummable terms) (q : ComplexSummable (λ n → -ℂ terms n)) →
  seriesSumℂ (λ n → -ℂ terms n) q ≡ -ℂ seriesSumℂ terms p
seriesSumℂ-neg terms p q = seriesSumℂIndependent (λ n → -ℂ terms n) q (negComplexSummable terms p)

seriesSumℂ-sub : ∀ a b (p : ComplexSummable a) (q : ComplexSummable b)
  (r : ComplexSummable (λ n → a n -ℂ b n)) →
  seriesSumℂ (λ n → a n -ℂ b n) r ≡ seriesSumℂ a p -ℂ seriesSumℂ b q
seriesSumℂ-sub a b p q r = seriesSumℂIndependent (λ n → a n -ℂ b n) r (subComplexSummable a b p q)

seriesSumℂ-scale : ∀ c terms (p : ComplexSummable terms) (q : ComplexSummable (scaleComplexSeries c terms)) →
  seriesSumℂ (scaleComplexSeries c terms) q ≡ c ·ℂ seriesSumℂ terms p
seriesSumℂ-scale c terms p q = seriesSumℂIndependent (scaleComplexSeries c terms) q (scaleComplexSummable c terms p)

seriesSumℂ-conjugate : ∀ terms (p : ComplexSummable terms) (q : ComplexSummable (conjugate ∘ terms)) →
  seriesSumℂ (conjugate ∘ terms) q ≡ conjugate (seriesSumℂ terms p)
seriesSumℂ-conjugate terms p q = seriesSumℂIndependent (conjugate ∘ terms) q (conjugateComplexSummable terms p)
