module Cubical.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (fromNatℚ)
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

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


productFstC :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  C[ PremetricProduct M N , M ]
productFstC = NE→C productFstNE


productSndC :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  C[ PremetricProduct M N , N ]
productSndC = NE→C productSndNE


productFstL :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  L[ PremetricProduct M N , M ]
productFstL = NE→L productFstNE


productSndL :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  L[ PremetricProduct M N , N ]
productSndL = NE→L productSndNE


pairNE :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} →
  NE[ O , M ] → NE[ O , N ] → NE[ O , PremetricProduct M N ]
fst (pairNE f g) x = fst f x , fst g x
IsNonExpanding.pres≈ (snd (pairNE f g)) x y ε x≈y =
  IsNonExpanding.pres≈ (snd f) x y ε x≈y
  , IsNonExpanding.pres≈ (snd g) x y ε x≈y


pairC :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} →
  C[ O , M ] → C[ O , N ] → C[ O , PremetricProduct M N ]
fst (pairC f g) x = fst f x , fst g x
IsContinuousAt.pres≈ (snd (pairC {O = O} f g) x) ε = do
  (δM , fδ) ← IsContinuousAt.pres≈ (snd f x) ε
  (δN , gδ) ← IsContinuousAt.pres≈ (snd g x) ε
  return
    ( min₊ δM δN
    , λ y x≈y →
      ( fδ y (PremetricStr.isMonotone≈≤ (snd O) x y
          (min₊ δM δN) δM (min₊≤L δM δN) x≈y)
      , gδ y (PremetricStr.isMonotone≈≤ (snd O) x y
          (min₊ δM δN) δN (min₊≤R δM δN) x≈y)))


pairUC :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} →
  UC[ O , M ] → UC[ O , N ] → UC[ O , PremetricProduct M N ]
fst (pairUC f g) x = fst f x , fst g x
snd (pairUC {O = O} f g) = do
  (μ , fμ) ← snd f
  (ν , gν) ← snd g
  return
    ( (λ ε → min₊ (μ ε) (ν ε))
    , isuniformlycontinuouswith λ x y ε x≈y →
      ( IsUniformlyContinuousWith.pres≈ fμ x y ε
          (PremetricStr.isMonotone≈≤ (snd O) x y
            (min₊ (μ ε) (ν ε)) (μ ε)
            (min₊≤L (μ ε) (ν ε)) x≈y)
      , IsUniformlyContinuousWith.pres≈ gν x y ε
          (PremetricStr.isMonotone≈≤ (snd O) x y
            (min₊ (μ ε) (ν ε)) (ν ε)
            (min₊≤R (μ ε) (ν ε)) x≈y)))


pairL :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} →
  L[ O , M ] → L[ O , N ] → L[ O , PremetricProduct M N ]
fst (pairL f g) x = fst f x , fst g x
snd (pairL {M = M} {N = N} f g) = do
  (L , fL) ← snd f
  (R , gR) ← snd g
  return
    ( max₊ L R
    , islipschitzwith λ x y ε x≈y →
      ( PremetricStr.isMonotone≈≤ (snd M) (fst f x) (fst f y)
          (L ·₊ ε) (max₊ L R ·₊ ε)
          (ℚ.≤-·o ⟨ L ⟩₊ ⟨ max₊ L R ⟩₊ ⟨ ε ⟩₊
            (ℚ.<Weaken≤ 0 ⟨ ε ⟩₊ (snd ε))
            (ℚ.≤max ⟨ L ⟩₊ ⟨ R ⟩₊))
          (IsLipschitzWith.pres≈ fL x y ε x≈y)
      , PremetricStr.isMonotone≈≤ (snd N) (fst g x) (fst g y)
          (R ·₊ ε) (max₊ L R ·₊ ε)
          (ℚ.≤-·o ⟨ R ⟩₊ ⟨ max₊ L R ⟩₊ ⟨ ε ⟩₊
            (ℚ.<Weaken≤ 0 ⟨ ε ⟩₊ (snd ε))
            (ℚ.≤max' ⟨ L ⟩₊ ⟨ R ⟩₊))
          (IsLipschitzWith.pres≈ gR x y ε x≈y)))


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


leftInsertionC :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ M ⟩ → C[ N , PremetricProduct M N ]
leftInsertionC M N x = NE→C (leftInsertionNE M N x)


rightInsertionC :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ N ⟩ → C[ M , PremetricProduct M N ]
rightInsertionC M N y = NE→C (rightInsertionNE M N y)


leftInsertionL :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ M ⟩ → L[ N , PremetricProduct M N ]
leftInsertionL M N x = NE→L (leftInsertionNE M N x)


rightInsertionL :
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') →
  ⟨ N ⟩ → L[ M , PremetricProduct M N ]
rightInsertionL M N y = NE→L (rightInsertionNE M N y)


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
