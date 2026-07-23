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
open import Cubical.Tactics.CauchyReals.ExpressionLifting
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

  module RationalMagnitudes = Rational.AlternatingFromMagnitudes s s-decr
  open RationalMagnitudes public using
    ( terms
    ; alternates
    ; strictlyDecreasing
    )

  module Series = AlternatingSeries terms alternates strictlyDecreasing

  alternatingPartialSumsCauchy :
    IsCauchySequence' (rat ∘ ℚ.seqΣ terms)
  alternatingPartialSumsCauchy =
    Series.WithLim.alternatingPartialSumsCauchy
      (RationalMagnitudes.terms→0 s→0)
