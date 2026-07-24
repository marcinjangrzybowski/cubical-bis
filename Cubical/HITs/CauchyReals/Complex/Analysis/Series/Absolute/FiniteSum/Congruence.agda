module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.FiniteSum.Congruence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  (Seq; seqΣ)


opaque
  seqΣ-cong : (s t : Seq) →
    ((n : ℕ) → s n ≡ t n) →
    (n : ℕ) →
    seqΣ s n ≡ seqΣ t n
  seqΣ-cong s t pointwise zero = refl
  seqΣ-cong s t pointwise (suc n) =
    cong₂ _+ᵣ_
      (seqΣ-cong s t pointwise n)
      (pointwise n)
