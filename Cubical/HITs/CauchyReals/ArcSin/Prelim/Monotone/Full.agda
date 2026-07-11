module Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone.Full where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.TrigBase
open import Cubical.HITs.CauchyReals.PiNumber

open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone.Quarter

sin⟨⟩-strictMonotone :
      (x y : ℝ)
      (x∈ : x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2)
      (y∈ : y ∈ ointervalℙ (-ᵣ π-number/2) π-number/2)
      → x <ᵣ y → sin x <ᵣ sin y
sin⟨⟩-strictMonotone x y x∈ y∈ x<y =
   0<y-x→x<y _ _ (isTrans<≤ᵣ _ _ _
    (snd ((_ , ∣x∣<π/2→0<cos[x] _
      (isTrans<≤ᵣ _ _ _
        (-ᵣ<ᵣ _ _ 0<π-number/2) (isTrans≡≤ᵣ _ _ _ (-ᵣ-rat 0)
         (isTrans≤ᵣ _ _ _ (0≤absᵣ y) (≤maxᵣ _ _) )) ,
          <π/2 )) ₊·ᵣ
      (_ , x<y→0<y-x _ _ x<y)))
    ((Integral-≤ x y x≤y _ _ _ _
      (λ x' ≤x' x'≤ →
        isTrans≤≡ᵣ _ _ _ ((cos-firstQuarter-Monotone
         _ _ (0≤absᵣ _ , <ᵣWeaken≤ᵣ _ _ (isTrans≡<ᵣ _ _ _
              (abs-max x')
              ((max<-lem x' (-ᵣ x') π-number/2
               ( isTrans≤<ᵣ _ _ _ x'≤  (snd y∈) )
               (isTrans<≡ᵣ _ _ _
                (-ᵣ<ᵣ _ _ (isTrans<≤ᵣ _ _ _ (fst x∈) ≤x'))
                 (-ᵣInvol _))))))
          ((isTrans≤ᵣ _ _ _ (0≤absᵣ _) (≤maxᵣ _ _)) ,
           <ᵣWeaken≤ᵣ _ _ <π/2)
          (isTrans≡≤ᵣ _ _ _
           (abs-max x')
            (maxMonotoneᵣ x' (absᵣ y) (-ᵣ x') (absᵣ x)
               (isTrans≤ᵣ _ _ _ x'≤ (≤absᵣ y))
                 (isTrans≤ᵣ _ _ _ (-ᵣ≤ᵣ _ _ ≤x')
                  (isTrans≤≡ᵣ _ _ _
                   (≤absᵣ _)
                   (sym (-absᵣ _))))

              ))))
         (sym (cos∘absᵣ x')))
      (IntegralConstℙ _ _ x≤y (cos (maxᵣ (absᵣ y) (absᵣ x))))
      (∫cos x y x≤y))))
  where
  x≤y = <ᵣWeaken≤ᵣ _ _ x<y

  <π/2 : maxᵣ (absᵣ y) (absᵣ x) <ᵣ π-number/2
  <π/2 = max<-lem (absᵣ y) (absᵣ x) _
             (isTrans≡<ᵣ _ _ _
              (abs-max y) (max<-lem y (-ᵣ y) π-number/2
               ((snd y∈))
               (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ ( (fst y∈)))
                 (-ᵣInvol _))))
             ((isTrans≡<ᵣ _ _ _
              (abs-max x)
              ((max<-lem x (-ᵣ x) π-number/2
               ( (snd x∈))
               (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ ((fst x∈)))
                 (-ᵣInvol _))))))

sin-strictMonotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      (y∈ : y ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      → x <ᵣ y → sin x <ᵣ sin y
sin-strictMonotone x y x∈ y∈ x<y =

 let (m , x<m , m<y)  = denseℝ _ _ x<y
     (m' , x<m' , m'<m)  = denseℝ _ _ x<m
     m∈ : m ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
     m∈ = (isTrans≤<ᵣ _ _ _ (fst x∈) x<m) , (isTrans<≤ᵣ _ _ _ m<y (snd y∈) )
     m'∈ : m' ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
     m'∈ = (isTrans≤<ᵣ _ _ _ (fst x∈) x<m') , isTrans<≤ᵣ _ _ _
         (isTrans<ᵣ _ _ _ m'<m m<y) (snd y∈)
 in isTrans<≤ᵣ _ _ _ (isTrans≤<ᵣ _ _ _
      (sin-Monotone _ _ x∈ (ointervalℙ⊆intervalℙ _ _ m' m'∈)
       (<ᵣWeaken≤ᵣ _ _ x<m'))
     (sin⟨⟩-strictMonotone m' m
       m'∈
       m∈ m'<m))
      (sin-Monotone _ _ (ointervalℙ⊆intervalℙ _ _ m m∈) y∈
      (<ᵣWeaken≤ᵣ _ _ m<y))




