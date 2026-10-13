module Cubical.Analysis.Complex.Series.Product.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
import Cubical.Analysis.Real.Algebra.Multiplication as RealMul
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Product.Finite as Real
import Cubical.Analysis.Real.FiniteSum.Reindexing as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations

-- Finite sums are still the existing coordinate sums. Reindexing requires
-- equality only on the finite interval, not on the whole sequence.
partialSumℂ-pointwiseBefore : ∀ a b n →
  (∀ k → k ℕ.< n → a k ≡ b k) → partialSumℂ a n ≡ partialSumℂ b n
partialSumℂ-pointwiseBefore a b n equal = ℂ≡
  (Real.partialSum-pointwiseBefore (re ∘ a) (re ∘ b) n (λ k before → cong re (equal k before)))
  (Real.partialSum-pointwiseBefore (im ∘ a) (im ∘ b) n (λ k before → cong im (equal k before)))

partialSumℂ-reverse : ∀ terms n →
  partialSumℂ terms (suc n) ≡ partialSumℂ (λ k → terms (n ∸ k)) (suc n)
partialSumℂ-reverse terms n = ℂ≡
  (Real.partialSum-reverse (re ∘ terms) n) (Real.partialSum-reverse (im ∘ terms) n)

partialSumℂ-right-scale : ∀ terms c n →
  partialSumℂ (λ k → terms k ·ℂ c) n ≡ partialSumℂ terms n ·ℂ c
partialSumℂ-right-scale terms c n =
  partialSumℂ-pointwise (λ k → terms k ·ℂ c) (scaleComplexSeries c terms)
    (λ k → ·ℂComm (terms k) c) n
  ∙ partialSumℂ-scale c terms n ∙ ·ℂComm c (partialSumℂ terms n)

-- The coefficient at n is the finite anti-diagonal, including both ends.
cauchyProductℂ : ComplexSequence → ComplexSequence → ComplexSequence
cauchyProductℂ a b n = partialSumℂ (λ k → a k ·ℂ b (n ∸ k)) (suc n)

opaque
  -- This bridge transfers the existing native real Mertens theorem without
  -- reproving its estimates or changing the convergence predicate.
  cauchyProductℂ-re : ∀ a b n → re (cauchyProductℂ a b n) ≡
    Real.cauchyProduct (re ∘ a) (re ∘ b) n - Real.cauchyProduct (im ∘ a) (im ∘ b) n
  cauchyProductℂ-re a b n = Real.partialSum-sub
    (λ k → re (a k) RealMul.· re (b (n ∸ k)))
    (λ k → im (a k) RealMul.· im (b (n ∸ k))) (suc n)

  cauchyProductℂ-im : ∀ a b n → im (cauchyProductℂ a b n) ≡
    Real.cauchyProduct (re ∘ a) (im ∘ b) n + Real.cauchyProduct (im ∘ a) (re ∘ b) n
  cauchyProductℂ-im a b n = Real.partialSum-add
    (λ k → re (a k) RealMul.· im (b (n ∸ k)))
    (λ k → im (a k) RealMul.· re (b (n ∸ k))) (suc n)

cauchyProductℂ-zero : ∀ a b → cauchyProductℂ a b zero ≡ a zero ·ℂ b zero
cauchyProductℂ-zero a b = +ℂComm 0ℂ (a zero ·ℂ b zero) ∙ +ℂIdR (a zero ·ℂ b zero)

cauchyProductℂ-left-step : ∀ a b n → cauchyProductℂ a b (suc n) ≡
  a zero ·ℂ b (suc n) +ℂ cauchyProductℂ (a ∘ suc) b n
cauchyProductℂ-left-step a b n = ℂ≡
  (Real.partialSum-first (λ k → re (a k ·ℂ b (suc n ∸ k))) (suc n))
  (Real.partialSum-first (λ k → im (a k ·ℂ b (suc n ∸ k))) (suc n))

opaque
  cauchyProductℂ-comm : ∀ a b n → cauchyProductℂ a b n ≡ cauchyProductℂ b a n
  cauchyProductℂ-comm a b n =
    partialSumℂ-reverse (λ k → a k ·ℂ b (n ∸ k)) n
    ∙ partialSumℂ-pointwiseBefore
        (λ k → a (n ∸ k) ·ℂ b (n ∸ (n ∸ k)))
        (λ k → b k ·ℂ a (n ∸ k)) (suc n)
        (λ k before → cong (a (n ∸ k) ·ℂ_)
          (cong b (sym (Real.boundedSubtractInvolutive k n (ℕ.pred-≤-pred before))))
          ∙ ·ℂComm (a (n ∸ k)) (b k))

  cauchyProductℂ-addRight : ∀ a b c n →
    cauchyProductℂ a (λ k → b k +ℂ c k) n ≡ cauchyProductℂ a b n +ℂ cauchyProductℂ a c n
  cauchyProductℂ-addRight a b c n =
    partialSumℂ-pointwise (λ k → a k ·ℂ (b (n ∸ k) +ℂ c (n ∸ k)))
      (λ k → a k ·ℂ b (n ∸ k) +ℂ a k ·ℂ c (n ∸ k))
      (λ k → ·ℂDistR+ (a k) (b (n ∸ k)) (c (n ∸ k))) (suc n)
    ∙ partialSumℂ-add (λ k → a k ·ℂ b (n ∸ k)) (λ k → a k ·ℂ c (n ∸ k)) (suc n)

  cauchyProductℂ-scaleLeft : ∀ c a b n →
    cauchyProductℂ (scaleComplexSeries c a) b n ≡ c ·ℂ cauchyProductℂ a b n
  cauchyProductℂ-scaleLeft c a b n =
    partialSumℂ-pointwise (λ k → (c ·ℂ a k) ·ℂ b (n ∸ k))
      (λ k → c ·ℂ (a k ·ℂ b (n ∸ k)))
      (λ k → sym (·ℂAssoc c (a k) (b (n ∸ k)))) (suc n)
    ∙ partialSumℂ-scale c (λ k → a k ·ℂ b (n ∸ k)) (suc n)

  cauchyProductℂ-conjugate : ∀ a b n →
    cauchyProductℂ (conjugate ∘ a) (conjugate ∘ b) n ≡ conjugate (cauchyProductℂ a b n)
  cauchyProductℂ-conjugate a b n =
    partialSumℂ-pointwise (λ k → conjugate (a k) ·ℂ conjugate (b (n ∸ k)))
      (λ k → conjugate (a k ·ℂ b (n ∸ k)))
      (λ k → sym (conjugate-pres· (a k) (b (n ∸ k)))) (suc n)
    ∙ partialSumℂ-conjugate (λ k → a k ·ℂ b (n ∸ k)) (suc n)

cauchyProductℂ-addLeft : ∀ a b c n →
  cauchyProductℂ (λ k → a k +ℂ b k) c n ≡ cauchyProductℂ a c n +ℂ cauchyProductℂ b c n
cauchyProductℂ-addLeft a b c n = cauchyProductℂ-comm (λ k → a k +ℂ b k) c n
  ∙ cauchyProductℂ-addRight c a b n
  ∙ cong₂ _+ℂ_ (cauchyProductℂ-comm c a n) (cauchyProductℂ-comm c b n)

cauchyProductℂ-scaleRight : ∀ c a b n →
  cauchyProductℂ a (scaleComplexSeries c b) n ≡ c ·ℂ cauchyProductℂ a b n
cauchyProductℂ-scaleRight c a b n = cauchyProductℂ-comm a (scaleComplexSeries c b) n
  ∙ cauchyProductℂ-scaleLeft c b a n ∙ cong (c ·ℂ_) (cauchyProductℂ-comm b a n)

-- Constants are represented by the sequence concentrated in degree zero.
-- Its coordinates are the existing real singleton series.
singletonComplexSeries : ℂ → ComplexSequence
singletonComplexSeries c n = Real.singletonSeries (re c) n , Real.singletonSeries (im c) n

opaque
  cauchyProductℂ-singleton-left : ∀ c b n → cauchyProductℂ (singletonComplexSeries c) b n ≡ c ·ℂ b n
  cauchyProductℂ-singleton-left c b n = ℂ≡
    (cauchyProductℂ-re (singletonComplexSeries c) b n
      ∙ cong₂ _-_ (Real.cauchyProduct-singleton-left (re c) (re ∘ b) n)
        (Real.cauchyProduct-singleton-left (im c) (im ∘ b) n))
    (cauchyProductℂ-im (singletonComplexSeries c) b n
      ∙ cong₂ _+_ (Real.cauchyProduct-singleton-left (re c) (im ∘ b) n)
        (Real.cauchyProduct-singleton-left (im c) (re ∘ b) n))

cauchyProductℂ-singleton-right : ∀ a c n → cauchyProductℂ a (singletonComplexSeries c) n ≡ a n ·ℂ c
cauchyProductℂ-singleton-right a c n = cauchyProductℂ-comm a (singletonComplexSeries c) n
  ∙ cauchyProductℂ-singleton-left c a n ∙ ·ℂComm c (a n)

unitComplexSeries : ComplexSequence
unitComplexSeries = singletonComplexSeries 1ℂ

cauchyProductℂ-unitLeft : ∀ b n → cauchyProductℂ unitComplexSeries b n ≡ b n
cauchyProductℂ-unitLeft b n = cauchyProductℂ-singleton-left 1ℂ b n ∙ ·ℂComm 1ℂ (b n) ∙ ·ℂIdR (b n)

cauchyProductℂ-unitRight : ∀ a n → cauchyProductℂ a unitComplexSeries n ≡ a n
cauchyProductℂ-unitRight a n = cauchyProductℂ-singleton-right a 1ℂ n ∙ ·ℂIdR (a n)
