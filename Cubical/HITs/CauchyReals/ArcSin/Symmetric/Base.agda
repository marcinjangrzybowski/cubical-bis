module Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset


open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.PiNumber

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Range
ointerval→abs< : ∀ x y → x ∈ ointervalℙ (-ᵣ y) y → absᵣ x <ᵣ y
ointerval→abs< x y (-y<x , x<y) =
   isTrans≡<ᵣ _ _ _  (abs-max _)
    (max<-lem x (-ᵣ x) y x<y (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ -y<x) (-ᵣInvol _)))

abs<→ointerval : ∀ x y → absᵣ x <ᵣ y → x ∈ ointervalℙ (-ᵣ y) y
abs<→ointerval x y ∣x∣<y =
     isTrans<≡ᵣ _ _ _
       ( -ᵣ<ᵣ _ _ (isTrans≤<ᵣ _ _ _
        (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ x)) (sym (-absᵣ x)))
       ∣x∣<y)) (-ᵣInvol x)
   , isTrans≤<ᵣ _ _ _ (≤absᵣ x) ∣x∣<y

abs≤→interval : ∀ x y → absᵣ x ≤ᵣ y → x ∈ intervalℙ (-ᵣ y) y
abs≤→interval x y ∣x∣≤y =
     isTrans≤≡ᵣ _ _ _
       ( -ᵣ≤ᵣ _ _ (isTrans≤ᵣ _ _ _
        (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ x)) (sym (-absᵣ x)))
       ∣x∣≤y)) (-ᵣInvol x)
   , isTrans≤ᵣ _ _ _ (≤absᵣ x) ∣x∣≤y

opaque
 arcSin⟨⟩ : ∀ x → (x∈ : x ∈ ointervalℙ -1 1) → ℝ
 arcSin⟨⟩ x x∈ =
   -ᵣ (arcSin (clampᵣ 0 1 (-ᵣ x))
    ((≤clampᵣ 0 1 (-ᵣ x) decℚ≤ᵣ?) ,
     isTrans≤<ᵣ _ (maxᵣ 0 (-ᵣ x)) _
         (min≤ᵣ (maxᵣ 0 (-ᵣ x)) 1 )
         (max<-lem 0 (-ᵣ x) 1 (decℚ<ᵣ? {0} {1})
           ((isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (fst x∈))
            (-ᵣ-rat -1))))))
    +ᵣ arcSin (clampᵣ 0 1 x)
     ((≤clampᵣ 0 1 x decℚ≤ᵣ?)
      , isTrans≤<ᵣ _ (maxᵣ 0 x) _
         (min≤ᵣ (maxᵣ 0 x) 1 )
         (max<-lem 0 x 1 (decℚ<ᵣ? {0} {1}) (snd x∈)) )

 arcSin⟨⟩∈ : ∀ x x∈ → arcSin⟨⟩ x x∈ ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
 arcSin⟨⟩∈ x x∈@(≤x , x≤) =
     isTrans<≤ᵣ _ _ _
       (-ᵣ<ᵣ _ _ ((snd (arcSin∈[0,1⟩ (clampᵣ 0 1 (-ᵣ x))
           clamp-negx∈))))
       (isTrans≡≤ᵣ _ _ _
        (sym (+IdR _))
        (≤ᵣ-o+ 0 _ _ ((isTrans≡≤ᵣ _ _ _
           (sym (arcSin[0]≡0 _))
           (arcSin-Monotone 0 (clampᵣ 0 1 x)
             (≤ᵣ-refl 0 , decℚ<ᵣ?)
              clamp-x∈ ((≤clampᵣ _ _ x decℚ≤ᵣ?)))))))
   , isTrans≤<ᵣ _ _ _
      (isTrans≤≡ᵣ _ _ _
       (≤ᵣ-+o _ _ _ (-ᵣ≤ᵣ 0 _
         (isTrans≡≤ᵣ _ _ _
           (sym (arcSin[0]≡0 _))
           (arcSin-Monotone 0 (clampᵣ 0 1 (-ᵣ x))
             (≤ᵣ-refl 0 , decℚ<ᵣ?)
              clamp-negx∈ ((≤clampᵣ _ _ (-ᵣ x) decℚ≤ᵣ?))))))
       ((𝐑'.+IdL' _ _ (-ᵣ-rat 0))))
      (snd (arcSin∈[0,1⟩ (clampᵣ 0 1 x)
       clamp-x∈))

    where
    clamp-x∈ : (clampᵣ 0 1 x) ∈ pred≤< 0 1
    clamp-x∈ = ((≤clampᵣ 0 1 x decℚ≤ᵣ?)
       , isTrans≤<ᵣ _ (maxᵣ 0 x) _
          (min≤ᵣ (maxᵣ 0 x) 1 )
          (max<-lem 0 x 1 (decℚ<ᵣ? {0} {1}) (snd x∈)))

    clamp-negx∈ : (clampᵣ 0 1 (-ᵣ x)) ∈ pred≤< 0 1
    clamp-negx∈ = ((≤clampᵣ 0 1 (-ᵣ x) decℚ≤ᵣ?) ,
     isTrans≤<ᵣ _ (maxᵣ 0 (-ᵣ x)) _
         (min≤ᵣ (maxᵣ 0 (-ᵣ x)) 1 )
         (max<-lem 0 (-ᵣ x) 1 (decℚ<ᵣ? {0} {1})
           ((isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (fst x∈))
            (-ᵣ-rat -1)))))

 opaque
  unfolding minᵣ maxᵣ
  arcSin⟨⟩[0]≡0 : arcSin⟨⟩ 0 (decℚ<ᵣ? { -1} {0} , decℚ<ᵣ? {0} {1}) ≡ 0
  arcSin⟨⟩[0]≡0 =
     cong₂ _+ᵣ_
       (cong -ᵣ_ (cong (uncurry arcSin)
        (Σ≡Prop (∈-isProp (pred≤< 0 1))
          {u = clampᵣ 0 1 (-ᵣ 0) , _}
          {rat [ pos 0 / 1 ] , ≤ᵣ-refl 0 , decℚ<ᵣ?}
          (cong (clampᵣ 0 1) (-ᵣ-rat 0) ∙ clampᵣ-rat 0 1 0))
         ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , (decℚ<ᵣ? {0} {1})))
         ∙ -ᵣ-rat 0)
       (cong (uncurry arcSin)
        (Σ≡Prop (∈-isProp (pred≤< 0 1)) (clampᵣ-rat 0 1 0)) ∙
    arcSin[0]≡0 (≤ᵣ-refl 0 , (decℚ<ᵣ? {0} {1})))
    ∙ +ᵣ-rat 0 0
