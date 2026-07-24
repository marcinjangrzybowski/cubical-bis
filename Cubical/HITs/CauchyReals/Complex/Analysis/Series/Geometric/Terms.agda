module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Terms where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  (Seq; seqΣ; IsConvSeries')


private
  singleTailTerm : (s : Seq) → (N n : ℕ) → N ℕ.< n →
    seqΣ
      (λ k →
        s
          (k ℕ.+
           ((n ℕ.∸ suc N) ℕ.+ suc N)))
      (suc zero) ≡
    s n
  singleTailTerm s N n N<n =
    Rℝ.+IdL
      (s ((n ℕ.∸ suc N) ℕ.+ suc N))
    ∙ cong s
        (ℕ.[n-m]+m (suc N) n N<n)


opaque
  convergentSeriesTermsEventuallySmall :
    (s : Seq) →
    IsConvSeries' s →
    (ε : ℚ₊) →
    Σ[ N ∈ ℕ ]
      ((n : ℕ) → N ℕ.< n →
        absᵣ (s n) <ᵣ rat (fst ε))
  convergentSeriesTermsEventuallySmall s converges ε =
    let
      N = fst (converges ε)
      tailBound = snd (converges ε)
    in
    N ,
    λ n N<n →
      subst
        (λ x →
          absᵣ x <ᵣ rat (fst ε))
        (singleTailTerm s N n N<n)
        (tailBound
          (n ℕ.∸ suc N)
          (suc zero))
