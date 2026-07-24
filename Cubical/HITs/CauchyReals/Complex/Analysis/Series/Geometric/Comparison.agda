module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Comparison where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  ( Seq
  ; seqΣ
  ; Seq'≤→Σ≤
  ; abs[seqΣ]≡seqΣ
  ; IsConvSeries'
  )


opaque
  nonnegativeSeriesComparison :
    (s t : Seq) →
    ((n : ℕ) → 0 ≤ᵣ s n) →
    ((n : ℕ) → 0 ≤ᵣ t n) →
    ((n : ℕ) → s n ≤ᵣ t n) →
    IsConvSeries' t →
    IsConvSeries' s
  nonnegativeSeriesComparison s t sNonnegative tNonnegative s≤t tConverges ε =
    let
      N = fst (tConverges ε)

      sTail : ℕ → Seq
      sTail n k = s (k ℕ.+ (n ℕ.+ suc N))

      tTail : ℕ → Seq
      tTail n k = t (k ℕ.+ (n ℕ.+ suc N))

      tailBound : (n m : ℕ) →
        absᵣ (seqΣ (sTail n) m) ≤ᵣ
        absᵣ (seqΣ (tTail n) m)
      tailBound n m =
        subst2 _≤ᵣ_
          (sym
            (abs[seqΣ]≡seqΣ
              (sTail n) m
              (λ k →
                sNonnegative
                  (k ℕ.+ (n ℕ.+ suc N)))))
          (sym
            (abs[seqΣ]≡seqΣ
              (tTail n) m
              (λ k →
                tNonnegative
                  (k ℕ.+ (n ℕ.+ suc N)))))
          (Seq'≤→Σ≤
            (sTail n) (tTail n)
            (λ k →
              s≤t
                (k ℕ.+ (n ℕ.+ suc N)))
            m)
    in
    N ,
    λ n m →
      isTrans≤<ᵣ _ _ _
        (tailBound n m)
        (snd (tConverges ε) n m)
