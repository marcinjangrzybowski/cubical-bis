module Cubical.Data.Rationals.Order.Floor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Involution

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Fast.Base as ℤ using (ℤ;pos;negsuc;ℕ₊₁→ℤ)
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Int.Fast.Properties as ℤ using ()
open import Cubical.Data.Int.Fast.Order as ℤ using ()
open import Cubical.Data.Int.Fast.Divisibility as ℤ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero;znots)
open import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.Data.Rationals.Order

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Foundations.Powerset


open import Cubical.Tactics.CommRingSolver.OrderedReflection
import Cubical.Tactics.CommRingSolver.Imports as 𝓢
open import Cubical.Algebra.OrderedCommRing

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals


open PositiveRationals
open NonNegativeRationals
open PositiveHalvesℚ

open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)
open FloorTheory ℚOrderedCommRing public
open import Cubical.Data.Rationals.Order.AbsoluteValue

private
 module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

 fromℕ≡[pos/1] : ∀ n → ℚRing.fromℕ n ≡ [ pos n / 1 ]
 fromℕ≡[pos/1] zero = refl
 fromℕ≡[pos/1] (suc zero) = refl
 fromℕ≡[pos/1] (suc (suc n)) =
     cong (1 +_) (fromℕ≡[pos/1] (suc n))
   ∙ ℤ+→ℚ+ (pos 1) (pos (suc n))
   ∙ cong [_/ 1 ] (sym (ℤ.pos+ 1 (suc n)))

 fromℤ≡[_/1] : ∀ z → ℚRing.fromℤ z ≡ [ z / 1 ]
 fromℤ≡[_/1] (pos n) = fromℕ≡[pos/1] n
 fromℤ≡[_/1] (negsuc n) =
     cong -_ (fromℕ≡[pos/1] (suc n))
   ∙ sym (-fromNat (suc n))

 fromℤ-≡ℤ- : ∀ m n →
   ℚRing.fromℤ m - ℚRing.fromℤ n ≡ [ m / 1 ] - [ n / 1 ]
 fromℤ-≡ℤ- m n = cong₂ _-_ (fromℤ≡[_/1] m) (fromℤ≡[_/1] n)

 -ℤ→ℚ- : ∀ z → - [ z / 1 ] ≡ [ ℤ.- z / 1 ]
 -ℤ→ℚ- z = eq/ _ _ ℤ!

 fromℤ-minus : ∀ z → - ℚRing.fromℤ z ≡ ℚRing.fromℤ (ℤ.- z)
 fromℤ-minus z =
     cong -_ (fromℤ≡[_/1] z)
   ∙ -ℤ→ℚ- z
   ∙ sym (fromℤ≡[_/1] (ℤ.- z))

isPropFloor : ∀ x → isProp (Floor x) 
isPropFloor x = isOfHLevelRetractFromIso 1 FloorIsoΣ $ w
 where
  w : isProp _
  w (integralPart₀ , fractionalPart₀ ,  x≡ip+fp₀ , fp<1₀)
    (integralPart₁ , fractionalPart₁ ,  x≡ip+fp₁ , fp<1₁) =
      ΣPathP (iP₀=iP₁ , ΣPathP (fP₀=fP₁ ,
              isProp→PathP (λ i → isProp× (isSetℚ _ _) (isProp< _ _))  _ _))
    where

    p :   ℚRing.fromℤ integralPart₀ - ℚRing.fromℤ integralPart₁
        ≡ fst fractionalPart₁ - fst fractionalPart₀
    p = ℚR.equalByDifference (ℚRing.fromℤ integralPart₀ - ℚRing.fromℤ integralPart₁)
         _ (ℚ!! ∙ sym (cong₂ _-_ (x≡ip+fp₀) (x≡ip+fp₁)) ∙ ℚ!!)

    iP₀=iP₁ : integralPart₀ ≡ integralPart₁
    iP₀=iP₁ = distFromℤ integralPart₀ integralPart₁
                 (subst (λ z → abs z < 1) (fromℤ-≡ℤ- integralPart₀ integralPart₁)
                 (subst (_< 1) (sym (cong abs p))
                   (byAbsCases (fst fractionalPart₁ - fst fractionalPart₀)
                    {_< 1} (<≤ℚ![ fp<1₀ ]) (<≤ℚ![ fp<1₁ ]))))
                  
    fP₀=fP₁ : fractionalPart₀ ≡ fractionalPart₁
    fP₀=fP₁ = sym $ ℚ₀₊≡ (ℚR.equalByDifference _ _
                (sym p ∙ ℚR.differenceByEqual _ _ (cong ℚRing.fromℤ iP₀=iP₁)))
    


pqFloor₊ : ∀ p q → Floor [ pos p / q ]
pqFloor₊ p (1+ q) = rf
 where
 open Floor

 rf : _
 rf .integralPart = pos (ℕ.quotient p / (suc q))
 rf .fractionalPart = [ ℤ.pos (ℕ.remainder p / (suc q)) / 1+ q ]
   , inj (subst (0 ℤ.≤_) (sym (ℤ.·IdR _)) (ℤ.zero-≤pos {remainder p / suc q}))
 rf .x≡ip+fp =
   sym (cong (_+ [ ℤ.pos (ℕ.remainder p / (suc q)) / 1+ q ])
          (fromℕ≡[pos/1] (ℕ.quotient p / (suc q)))
        ∙ floor-lemma p q)
 rf .fp<1 = inj (subst2 ℤ._<_
     (sym (ℤ.·IdR (pos (remainder p / suc q)))) (sym (ℤ.·IdL (pos (suc q))))
     (ℤ.suc≤→< (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.mod< q p))))

pqFloor : ∀ p q → Floor [ p / q ]
pqFloor (pos p) q = pqFloor₊ p q
pqFloor (negsuc n) q = decRec rf
 (rf' ∘S (≤→¬≡→< 0 (fst F₊.fractionalPart) (snd F₊.fractionalPart) ))
 (discreteℚ 0 (fst F₊.fractionalPart))

 where
  open Floor ; module F₊ = Floor (pqFloor₊ (suc n) q)

  module _ (p : 0 ≡ fst (F₊.fractionalPart)) where
   rf : Floor [ negsuc n / q ]    
   rf .integralPart = ℤ.- F₊.integralPart
   rf .fractionalPart = 0
   rf .x≡ip+fp =
      ℚ! ∙∙ cong -_ (F₊.x≡ip+fp
           ∙ cong (ℚRing.fromℤ F₊.integralPart +_) (sym p))
          ∙∙ (cong -_ (+IdR (ℚRing.fromℤ F₊.integralPart))
              ∙ sym (+IdR (- ℚRing.fromℤ F₊.integralPart))
              ∙ cong (_+ 0) (fromℤ-minus F₊.integralPart))

   rf .fp<1 = inj (ℤ.pos<pos tt)

  module _ ((F₊fp , _) : ℚ₊) (F₊fp<1 : F₊fp < 1) where
   lem1 : 0 ≤ - (F₊fp - 1)
   lem1 = <≤ℚ![ F₊fp<1 ]
   lem2 :  - (F₊fp - 1) < 1
   lem2 = <≤ℚ!
   
  module _ (0<fp : 0 < fst F₊.fractionalPart) where
   rf' : Floor [ negsuc n / q ]

   rf' .integralPart = ℤ.- (1 ℤ.+ F₊.integralPart)
   rf' .fractionalPart = (- (fst F₊.fractionalPart - 1) ,
     lem1 (_ , 0<fp) F₊.fp<1)
   rf' .x≡ip+fp =
     ℚ! ∙∙ cong -_ F₊.x≡ip+fp ∙∙
       (cong -_ (cong (_+ fst F₊.fractionalPart) (fromℤ≡[_/1] F₊.integralPart))
        ∙ ℚ!
        ∙ cong (_+ (- (fst F₊.fractionalPart - 1)))
            (sym (fromℤ≡[_/1] (ℤ.- (1 ℤ.+ F₊.integralPart)))))
   rf' .fp<1 = lem2 (_ , 0<fp) F₊.fp<1
    


floorℚ : ∀ x → Floor x
floorℚ = ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB = isPropFloor
 w .ElimProp.f (p , q) = pqFloor p q  

floor-fracℚ₊ : ∀ (x : ℚ₊) → Σ (ℕ × ℚ) λ (k , q) →
                       (fromNat k + q ≡ fst x ) × ((0 ≤ q)  × (q < 1))
floor-fracℚ₊ (x , 0<x) =
 let fx = floorℚ x
     (k , q) = lem fx (x≡ip+fp fx)
 in (k , fst (fx .fractionalPart)) ,
    cong (_+ fst (fractionalPart fx)) (sym (fromℕ≡[pos/1] k))
     ∙ cong (λ z → ℚRing.fromℤ z + fst (fractionalPart fx)) q
     ∙ sym (fx .x≡ip+fp) , snd (fractionalPart fx)  , fx .fp<1

 where
  open Floor
  lem : (f : Floor x) → x ≡ ℚRing.fromℤ (integralPart f) + fst (fractionalPart f)
           →  Σ[ k ∈ ℕ ] pos k ≡ f .integralPart
  lem f p with f .integralPart
  ... | pos n = _ , refl
  ... | negsuc n = ⊥.rec (isAsym< _ _
     (isTrans<≤ _ _ _ (<-o+ _ _ [ negsuc _ / 1 ] (f .fp<1))
       (≤minus→≤ _ _ (subst {x = [ pos n / 1 ]} (0 ≤_) ℚ!  (inj (ℤ.pos≤pos tt))))
       )
     (subst (0 <_) (p ∙ cong (_+ fst (fractionalPart f)) (fromℤ≡[_/1] (negsuc n))) 0<x))

ceilℚ₊ : (q : ℚ₊) → Σ[ k ∈ ℕ₊₁ ] (fst q) < fromNat (ℕ₊₁→ℕ k)
ceilℚ₊ q = 

 1+ (fst (fst (floor-fracℚ₊ q))) ,
    subst2 (_<_) --  (fromNat (suc (fst (fst (floor-fracℚ₊ q)))))
       (+Comm (floor-fracℚ₊ q .fst .snd) _ ∙ fst (snd (floor-fracℚ₊ q)))
       ((ℕ+→ℚ+ 1 _))
        (<-+o _ _ (fromNat (fst (fst (floor-fracℚ₊ q))))
          (snd (snd (snd (floor-fracℚ₊ q)))))






boundℕ : ∀ q → Σ[ k ∈ ℕ₊₁ ] (abs q < ([ ℕ₊₁→ℤ k , 1 ]))
boundℕ q =
  ⊎.rec (λ x → 1 , subst (_< 1) x (decℚ<? {0} {1}))
        (λ x →  let ((k , f) , e , e' , e'') = floor-fracℚ₊ (abs q ,  x)
                in
                 (1+ k , subst2 (_<_)
                         (+Comm f _ ∙ e)
                          (ℕ+→ℚ+ 1 k) ((<-+o f 1 [ pos k / 1+ 0 ] e''))))
    (≤→≡⊎< 0 (abs q) (0≤abs q))
    
