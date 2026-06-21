module Cubical.Algebra.OrderedCommRing.Floor where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Fast.Base using (ℤ)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' : Level

module FloorTheory (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    RRing = OrderedCommRing→Ring R'

  open OrderedCommRingStr (snd R')
  open RingTheory RRing using (fromℤ)

  record Floor (x : R) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      integralPart : ℤ
      fractionalPart : Σ[ r ∈ R ] 0r ≤ r
      x≡ip+fp : x ≡ fromℤ integralPart + fst fractionalPart
      fp<1 : fst fractionalPart < 1r

  unquoteDecl FloorIsoΣ = declareRecordIsoΣ FloorIsoΣ (quote Floor)

  ∙floor : ∀ {x y} → x ≡ y → Floor x → Floor y
  ∙floor p f = f'
    where
    open Floor
    module F = Floor f

    f' : _
    f' .integralPart = F.integralPart
    f' .fractionalPart = F.fractionalPart
    f' .x≡ip+fp = sym p ∙ F.x≡ip+fp
    f' .fp<1 = F.fp<1
