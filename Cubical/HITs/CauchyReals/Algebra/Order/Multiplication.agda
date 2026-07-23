module Cubical.HITs.CauchyReals.Algebra.Order.Multiplication where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict using
  (x<y→0<y-x-bootstrap)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Bootstrap using
  (0<y-x→x<y)


opaque
 unfolding _≤ᵣ_ maxᵣ

 ≤ᵣ-·ᵣo : ∀ m n o → 0 ≤ᵣ o → m ≤ᵣ n → m ·ᵣ o ≤ᵣ n ·ᵣ o
 ≤ᵣ-·ᵣo m n o 0≤o m≤n = subst
   (λ o' → m ·ᵣ o' ≤ᵣ n ·ᵣ o') 0≤o
   (w ∙ cong (_·ᵣ maxᵣ (rat [ pos 0 / 1+ 0 ]) o) m≤n)
  where
  w : maxᵣ (m ·ᵣ maxᵣ 0 o) (n ·ᵣ maxᵣ 0 o)
      ≡ maxᵣ m n ·ᵣ maxᵣ 0 o
  w = ≡Continuous _ _
      (cont₂maxᵣ _ _
        (IsContinuous∘ _ _ (IsContinuous·ᵣL m) (IsContinuousMaxL 0))
        (IsContinuous∘ _ _ (IsContinuous·ᵣL n) (IsContinuousMaxL 0)))
      (IsContinuous∘ _ _ (IsContinuous·ᵣL _) (IsContinuousMaxL 0))
      (λ o' →
        ≡Continuous _ _
          (IsContinuous∘ _ _
            (IsContinuousMaxR (n ·ᵣ maxᵣ 0 (rat o')))
            (IsContinuous·ᵣR (maxᵣ 0 (rat o'))))
          (IsContinuous∘ _ _
            (IsContinuous·ᵣR (maxᵣ 0 (rat o')))
            (IsContinuousMaxR n))
          (λ m' →
            ≡Continuous
              (λ n' → maxᵣ
                (rat m' ·ᵣ maxᵣ 0 (rat o'))
                (n' ·ᵣ maxᵣ 0 (rat o')))
              (λ n' → maxᵣ (rat m') n' ·ᵣ maxᵣ 0 (rat o'))
              (IsContinuous∘ _ _
                (IsContinuousMaxL (rat m' ·ᵣ maxᵣ 0 (rat o')))
                (IsContinuous·ᵣR (maxᵣ 0 (rat o'))))
              (IsContinuous∘ _ _
                (IsContinuous·ᵣR (maxᵣ 0 (rat o')))
                (IsContinuousMaxL (rat m')))
              (λ n' →
                ℚℝ!
                ∙∙ cong rat
                  (sym (ℚ.·MaxDistrℚ' m' n' (ℚ.max 0 o') (ℚ.≤max 0 o')))
                ∙∙ ℚℝ!)
              n)
          m)
      o

 ≤ᵣ-o·ᵣ : ∀ m n o → 0 ≤ᵣ o → m ≤ᵣ n → o ·ᵣ m ≤ᵣ o ·ᵣ n
 ≤ᵣ-o·ᵣ m n o 0≤o p =
   subst2 _≤ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _) (≤ᵣ-·ᵣo m n o 0≤o p)


 ≤ᵣ-·o : ∀ m n o → 0 ℚ.≤ o → m ≤ᵣ n → m ·ᵣ rat o ≤ᵣ n ·ᵣ rat o
 ≤ᵣ-·o m n o 0≤o =
   ≤ᵣ-·ᵣo m n (rat o) (≤ℚ→≤ᵣ 0 o 0≤o)


 ≤ᵣ-o· : ∀ m n o → 0 ℚ.≤ o → m ≤ᵣ n → rat o ·ᵣ m ≤ᵣ rat o ·ᵣ n
 ≤ᵣ-o· m n o 0≤o =
   ≤ᵣ-o·ᵣ m n (rat o) (≤ℚ→≤ᵣ 0 o 0≤o)


≤ᵣ₊Monotone·ᵣ : ∀ m n o s → 0 ≤ᵣ n → 0 ≤ᵣ o
  → m ≤ᵣ n → o ≤ᵣ s → m ·ᵣ o ≤ᵣ n ·ᵣ s
≤ᵣ₊Monotone·ᵣ m n o s 0≤n 0≤o m≤n o≤s =
  isTrans≤ᵣ _ _ _ (≤ᵣ-·ᵣo m n o 0≤o m≤n)
    (≤ᵣ-o·ᵣ o s n 0≤n o≤s)


opaque
 unfolding _<ᵣ_

 ℝ₊· : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ fst m ·ᵣ fst n
 ℝ₊· (m , 0<m) (n , 0<n) = PT.map2
   (λ ((q , q') , 0≤q , q<q' , q'≤m) →
    λ ((r , r') , 0≤r , r<r' , r'≤n) →
     let 0<r' = ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 r 0≤r) r<r'
         qr₊ =
           (q' , ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 q 0≤q) q<q')
           ·₊ (r' , 0<r')
     in (fst (qr₊ /2₊) , fst qr₊) ,
          ≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ (qr₊ /2₊)) ,
          /2₊<id qr₊ ,
          subst (_≤ᵣ (m ·ᵣ n))
            (sym (rat·ᵣrat q' r'))
            (≤ᵣ₊Monotone·ᵣ (rat q') m (rat r') n
              (<ᵣWeaken≤ᵣ 0 _ 0<m)
              (<ᵣWeaken≤ᵣ 0 _ (<ℚ→<ᵣ _ _ 0<r'))
              q'≤m r'≤n))
   0<m 0<n


<ᵣ-·ᵣo : ∀ m n (o : ℝ₊) → m <ᵣ n → m ·ᵣ fst o <ᵣ n ·ᵣ fst o
<ᵣ-·ᵣo m n (o , 0<o) p =
  let z = subst (0 <ᵣ_)
        (·DistR+ n (-ᵣ m) o ∙ cong ((n ·ᵣ o) +ᵣ_) (-ᵣ· m o))
        (ℝ₊· (_ , x<y→0<y-x-bootstrap _ _ p) (o , 0<o))
  in 0<y-x→x<y _ _ z


<ᵣ-o·ᵣ : ∀ m n (o : ℝ₊) → m <ᵣ n → fst o ·ᵣ m <ᵣ fst o ·ᵣ n
<ᵣ-o·ᵣ m n (o , 0<o) p =
  subst2 _<ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _)
    (<ᵣ-·ᵣo m n (o , 0<o) p)
