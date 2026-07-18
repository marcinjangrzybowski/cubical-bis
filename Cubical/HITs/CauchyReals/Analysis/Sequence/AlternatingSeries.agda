module Cubical.HITs.CauchyReals.Analysis.Sequence.AlternatingSeries where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

import Cubical.Data.Rationals.Series.Alternating as Rational
open Rational public using
  ( AlternatesPositiveFirst
  ; _∣2
  ; ∣2-cases
  ; StrictlyDecreasingAlternating
  )

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting
open import Cubical.HITs.CauchyReals.Foundation.Rationals

module AlternatingSeries s
       (alternates : AlternatesPositiveFirst s)
       (decreases : StrictlyDecreasingAlternating s)
       where

  module RationalSeries = Rational.AlternatingSeries s alternates decreases
  open RationalSeries public

  module WithLim
    (s→0 : (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n → abs (s n) ℚ.< fst ε))
    where

    alternatingPartialSumsCauchy : IsCauchySequence' (rat ∘ ℚ.seqΣ s)
    alternatingPartialSumsCauchy ε =
      let N , cs = s→0 ε
      in suc N , λ n m <n <m →
         isTrans≡<ᵣ _ _ _
           (cong absᵣ (-ᵣ-rat₂ (ℚ.seqΣ s m) (ℚ.seqΣ s n))
             ∙ absᵣ-rat (ℚ.seqΣ s m ℚ.- ℚ.seqΣ s n))
           (<ℚ→<ᵣ _ _
             (ℚ.isTrans≤< _ _ _
               (cauchyByAlt (suc N) m n <m <n)
               (cs (suc N) ℕ.≤-refl)))

module AlternatingFromMagnitudes (s : ℕ → ℚ₊)
      (s-decr : ∀ k → fst (s (suc k)) ℚ.< fst (s k))
      (s→0 : (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n → fst (s n) ℚ.< fst ε))
      where

  terms : ℕ → ℚ
  terms k = ℚ.-1ⁿ· k (fst (s k))

  alternates : AlternatesPositiveFirst terms
  alternates k =
    subst (0 ℚ.<_) (sym (ℚ.-1ⁿ·-·2 k (fst (s _)))) (snd (s _))
    , subst (ℚ._< 0)
        (cong ℚ.-_
          (sym (ℚ.-1ⁿ·-·2 k (fst (s (suc (k ℕ.· 2))))))
          ∙ sym (ℚ.-1ⁿ·-suc (k ℕ.· 2) _))
        (ℚ.minus-< _ _ (snd (s _)))

  strictlyDecreasing : StrictlyDecreasingAlternating terms
  strictlyDecreasing k =
    subst2 ℚ._<_ (sym negOdd≡oddMagnitude) (sym evenTerm≡evenMagnitude)
      (s-decr (k ℕ.· 2))
    , subst2 ℚ._<_ (sym nextEvenTerm≡nextEvenMagnitude)
        (sym negOdd≡oddMagnitude)
        (s-decr (suc (k ℕ.· 2)))
    where
    negOdd≡oddMagnitude :
      ℚ.- terms (suc (k ℕ.· 2)) ≡ fst (s (suc (k ℕ.· 2)))
    negOdd≡oddMagnitude =
      cong ℚ.-_
        (ℚ.-1ⁿ·-suc (k ℕ.· 2) (fst (s (suc (k ℕ.· 2)))))
      ∙ ℚ.-Invol (ℚ.-1ⁿ· (k ℕ.· 2) (fst (s (suc (k ℕ.· 2)))))
      ∙ ℚ.-1ⁿ·-·2 k (fst (s (suc (k ℕ.· 2))))

    evenTerm≡evenMagnitude :
      terms (k ℕ.· 2) ≡ fst (s (k ℕ.· 2))
    evenTerm≡evenMagnitude =
      ℚ.-1ⁿ·-·2 k (fst (s (k ℕ.· 2)))

    nextEvenTerm≡nextEvenMagnitude :
      terms (suc (suc (k ℕ.· 2))) ≡ fst (s (suc (suc (k ℕ.· 2))))
    nextEvenTerm≡nextEvenMagnitude =
      ℚ.-1ⁿ·-·2 (suc k) (fst (s (suc (suc (k ℕ.· 2)))))

  private
    signedTerms→0 : (ε : ℚ₊) →
      Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n → abs (terms n) ℚ.< fst ε)
    signedTerms→0 ε =
      map-snd
        (λ X n N<n →
          subst (ℚ._< fst ε)
            (sym (0<→abs≡id _ (snd (s n)))
              ∙ sym (ℚ.absᵣ∘-1ⁿ· n (fst (s n))))
            (X n N<n))
        (s→0 ε)

  module Series = AlternatingSeries terms alternates strictlyDecreasing

  alternatingPartialSumsCauchy :
    IsCauchySequence' (rat ∘ ℚ.seqΣ terms)
  alternatingPartialSumsCauchy =
    Series.WithLim.alternatingPartialSumsCauchy signedTerms→0
