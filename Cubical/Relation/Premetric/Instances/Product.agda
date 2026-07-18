module Cubical.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings


private
  variable
    ℓM ℓM' ℓN ℓN' ℓO ℓO' : Level


PremetricProductStr :
  {M : Type ℓM} {N : Type ℓN} →
  PremetricStr ℓM' M → PremetricStr ℓN' N →
  PremetricStr (ℓ-max ℓM' ℓN') (M × N)
PremetricProductStr metricM metricN = product
  where
  module M = PremetricStr metricM
  module N = PremetricStr metricN

  product : PremetricStr _ _
  PremetricStr._≈[_]_ product x ε y =
    (fst x M.≈[ ε ] fst y) × (snd x N.≈[ ε ] snd y)
  PremetricStr.isPremetric product = isProductPremetric
    where
    open IsPremetric

    isProductPremetric : IsPremetric (PremetricStr._≈[_]_ product)
    isProductPremetric .isSetM = isSet× M.isSetM N.isSetM
    isProductPremetric .isProp≈ x y ε =
      isProp× (M.isProp≈ (fst x) (fst y) ε)
        (N.isProp≈ (snd x) (snd y) ε)
    isProductPremetric .isRefl≈ x ε =
      M.isRefl≈ (fst x) ε , N.isRefl≈ (snd x) ε
    isProductPremetric .isSym≈ x y ε x≈y =
      M.isSym≈ (fst x) (fst y) ε (fst x≈y)
      , N.isSym≈ (snd x) (snd y) ε (snd x≈y)
    isProductPremetric .isSeparated≈ x y allClose =
      cong₂ _,_
        (M.isSeparated≈ (fst x) (fst y) (λ ε → fst (allClose ε)))
        (N.isSeparated≈ (snd x) (snd y) (λ ε → snd (allClose ε)))
    isProductPremetric .isTriangular≈ x y z ε δ x≈y y≈z =
      M.isTriangular≈ (fst x) (fst y) (fst z) ε δ
        (fst x≈y) (fst y≈z)
      , N.isTriangular≈ (snd x) (snd y) (snd z) ε δ
          (snd x≈y) (snd y≈z)
    isProductPremetric .isRounded≈ x y ε x≈y = PT.map2
      (λ (delta , delta<ε , x≈delta) (eta , eta<ε , y≈eta) →
        max₊ delta eta
        , subst (fst (max₊ delta eta) ℚ.<_)
            (ℚ.maxIdem (fst ε))
            (ℚ.<MonotoneMax
              (fst delta) (fst eta) (fst ε) (fst ε)
              delta<ε eta<ε)
        , M.isMonotone≈≤ (fst x) (fst y) delta (max₊ delta eta)
            (ℚ.≤max (fst delta) (fst eta)) x≈delta
        , N.isMonotone≈≤ (snd x) (snd y) eta (max₊ delta eta)
            (ℚ.≤max' (fst delta) (fst eta)) y≈eta)
      (M.isRounded≈ (fst x) (fst y) ε (fst x≈y))
      (N.isRounded≈ (snd x) (snd y) ε (snd x≈y))


PremetricProduct :
  PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' →
  PremetricSpace (ℓ-max ℓM ℓN) (ℓ-max ℓM' ℓN')
PremetricProduct M N =
  ⟨ M ⟩ × ⟨ N ⟩ , PremetricProductStr (snd M) (snd N)


productFstNE :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  NE[ PremetricProduct M N , M ]
fst productFstNE = fst
IsNonExpanding.pres≈ (snd productFstNE) x y ε = fst


productSndNE :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  NE[ PremetricProduct M N , N ]
fst productSndNE = snd
IsNonExpanding.pres≈ (snd productSndNE) x y ε = snd


pairNE :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} →
  NE[ O , M ] → NE[ O , N ] → NE[ O , PremetricProduct M N ]
fst (pairNE f g) x = fst f x , fst g x
IsNonExpanding.pres≈ (snd (pairNE f g)) x y ε x≈y =
  IsNonExpanding.pres≈ (snd f) x y ε x≈y
  , IsNonExpanding.pres≈ (snd g) x y ε x≈y


leftInsertionNE :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ M ⟩ → NE[ N , PremetricProduct M N ]
fst (leftInsertionNE M N x) y = x , y
IsNonExpanding.pres≈ (snd (leftInsertionNE M N x)) y z ε y≈z =
  PremetricStr.isRefl≈ (snd M) x ε , y≈z


rightInsertionNE :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ N ⟩ → NE[ M , PremetricProduct M N ]
fst (rightInsertionNE M N y) x = x , y
IsNonExpanding.pres≈ (snd (rightInsertionNE M N y)) x z ε x≈z =
  x≈z , PremetricStr.isRefl≈ (snd N) y ε


productFstUC :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  UC[ PremetricProduct M N , M ]
productFstUC {M = M} {N = N} =
  NE→UC (productFstNE {M = M} {N = N})


productSndUC :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  UC[ PremetricProduct M N , N ]
productSndUC {M = M} {N = N} =
  NE→UC (productSndNE {M = M} {N = N})


leftInsertionUC :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ M ⟩ → UC[ N , PremetricProduct M N ]
leftInsertionUC M N x = NE→UC (leftInsertionNE M N x)


rightInsertionUC :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ N ⟩ → UC[ M , PremetricProduct M N ]
rightInsertionUC M N y = NE→UC (rightInsertionNE M N y)
