{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.ArcSin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities


Integral-≤ : ∀ a b → a ≤ᵣ b → ∀ f f' s s'
            → (∀ x ≤x x≤ → f x ≤x x≤ ≤ᵣ f' x ≤x x≤)
            → on[ a , b ]IntegralOf f is s
            → on[ a , b ]IntegralOf f' is s'
            → s ≤ᵣ s'
Integral-≤ a b a≤b f f' s s' f≤f' s=∫ s'=∫ =
  Integral'-≤ a b a≤b
   _ _
   s s'
      (λ x x∈ → f≤f' _ _ _)
       (invEq (clampᵣ-IntegralOf' a b a≤b _ _) s=∫)
       (invEq (clampᵣ-IntegralOf' a b a≤b _ _) s'=∫)



Integral0ℙ : (a b : ℝ) →
             a ≤ᵣ b →
             on[ a , b ]IntegralOf (λ _ _ _ → 0) is 0
Integral0ℙ a b a≤b =
  subst (on[ a , b ]IntegralOf (λ _ _ _ → rat [ pos 0 / 1+ 0 ]) is_)
    (𝐑'.0LeftAnnihilates _) (IntegralConstℙ a b a≤b 0)

cos∘absᵣ : ∀ x → cos x ≡ cos (absᵣ x)
cos∘absᵣ = ≡Continuous _ _
  isContinuousCos
  (IsContinuous∘ _ _ isContinuousCos IsContinuousAbsᵣ)
   λ q → ⊎.rec
     (λ 0≤q → cong cos $ sym (absᵣNonNeg _ (≤ℚ→≤ᵣ _ _ 0≤q)))
     (λ q≤0 → cong cos (sym (-ᵣInvol _)) ∙
              ((cong cos $ sym (cong -ᵣ_
               ((absᵣNonNeg _ (isTrans≡≤ᵣ _ _ _
                 (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _
                  (((≤ℚ→≤ᵣ q 0 q≤0)))) )) ∙
                  refl))))
              ∙ sym (cos-even _) ∙ cong cos
               (sym (-absᵣ _)))
     (ℚ.≤cases 0 q)

∣x∣≤π/2→0≤cos[x] : ∀ x → x ∈ intervalℙ (-ᵣ π-number/2) π-number/2 → 0 ≤ᵣ cos x
∣x∣≤π/2→0≤cos[x] x x∈ =
  isTrans≤≡ᵣ _ _ _
   (x≤π/2→0≤cos[x] (absᵣ x)
     (0≤absᵣ _ , (isTrans≡≤ᵣ _ _ _  (abs-max _)
     (max≤-lem x (-ᵣ x) _ (snd x∈)
      (isTrans≤≡ᵣ _  _ _  (-ᵣ≤ᵣ _ _ (fst x∈)) (-ᵣInvol _ ))))))
   (sym (cos∘absᵣ x))

∣x∣<π/2→0<cos[x] : ∀ x → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2 → 0 <ᵣ cos x
∣x∣<π/2→0<cos[x] x x∈ =
  isTrans<≡ᵣ _ _ _
   (0≤x<π/2→0<cos[x] (absᵣ x)
     (0≤absᵣ _)
     ((isTrans≡<ᵣ _ _ _  (abs-max _)
     (max<-lem x (-ᵣ x) _ (snd x∈)
      (isTrans<≡ᵣ _  _ _  (-ᵣ<ᵣ _ _ (fst x∈)) (-ᵣInvol _ ))))))
   (sym (cos∘absᵣ x))


sin-firstQuarter-Monotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2)
      → x ≤ᵣ y → sin x ≤ᵣ sin y
sin-firstQuarter-Monotone x y x∈ y∈ x≤y =
 invEq (x≤y≃0≤y-x _ _)
   (Integral-≤ x y x≤y _ _ _ _
      (λ x' ≤x' x'≤ →
        x≤π/2→0≤cos[x] x'
          (isTrans≤ᵣ _ _ _ (fst x∈) ≤x' ,
           isTrans≤ᵣ _ _ _ x'≤ (snd y∈ ) ))
      (Integral0ℙ _ _ x≤y)
      (∫cos x y x≤y))

sin-Monotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      (y∈ : y ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      → x ≤ᵣ y → sin x ≤ᵣ sin y
sin-Monotone x y x∈ y∈ x≤y =
 invEq (x≤y≃0≤y-x _ _)
   (Integral-≤ x y x≤y _ _ _ _
      (λ x' ≤x' x'≤ →
        ∣x∣≤π/2→0≤cos[x] x'
         (isTrans≤ᵣ _ _ _ (fst x∈ ) ≤x' ,
          isTrans≤ᵣ _ _ _ x'≤ (snd y∈ )))
      (Integral0ℙ _ _ x≤y)
      (∫cos x y x≤y))



cos-firstQuarter-Monotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2)
      → x ≤ᵣ y → cos y ≤ᵣ cos x
cos-firstQuarter-Monotone x y x∈ y∈ x≤y =
  invEq (x≤y≃0≤y-x _ _)
           (Integral-≤ x y x≤y _ _ _ _
              (λ x' ≤x' x'≤ →
                isTrans≡≤ᵣ _ _ _
                  (sym sin0=0) (sin-firstQuarter-Monotone 0 x'
                   (≤ᵣ-refl 0 , <ᵣWeaken≤ᵣ _ _ 0<π-number/2)
                   (isTrans≤ᵣ _ _ _ (fst x∈) ≤x'
                   , isTrans≤ᵣ _ _ _ x'≤ (snd y∈))
                   (isTrans≤ᵣ _ _ _ (fst x∈) ≤x')))
              (Integral0ℙ _ _ x≤y)
              (∫sin x y x≤y))


denseℝ : ∀ u v → u <ᵣ v → Σ[ r ∈ ℝ ] ((u <ᵣ r) × (r <ᵣ v))
denseℝ u v u<v =
  (u +ᵣ v) ·ᵣ rat [ 1 / 2 ]
    , isTrans<≡ᵣ _ _ _
      (isTrans≡<ᵣ _ _ _
        (((sym (𝐑'.·IdR' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
         ∙ ·ᵣAssoc _ _ _ ) ∙ ·ᵣComm _ _ )
         ∙ sym (x+x≡2x (u ·ᵣ rat [ 1 / 2 ])))
        (<ᵣ-o+ _ _ _
          (<ᵣ-·ᵣo _ _ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)) u<v)))
        (sym (·DistR+ _ _ _))
    , isTrans≡<ᵣ _ _ _ (·DistR+ _ _ _)
      (isTrans<≡ᵣ _ _ _
        (<ᵣ-+o _ _ _ (<ᵣ-·ᵣo _ _ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)) u<v))
        ((x+x≡2x (v ·ᵣ rat [ 1 / 2 ]))
         ∙ sym ((sym (𝐑'.·IdR' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
         ∙ ·ᵣAssoc _ _ _ ) ∙ ·ᵣComm _ _ )))

sin-firstQuarter-strictMonotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2)
      → x <ᵣ y → sin x <ᵣ sin y
sin-firstQuarter-strictMonotone x y x∈ y∈ x<y =
  let (y' , x<y' , y'<y)  = denseℝ _ _ x<y
      y'<π/2 = isTrans<≤ᵣ _ _ _ y'<y (snd y∈)
      y'∈ = (isTrans≤ᵣ _ _ _ (fst x∈) (<ᵣWeaken≤ᵣ _ _ x<y')
          , <ᵣWeaken≤ᵣ _ _ y'<π/2)
  in isTrans<≤ᵣ _ _ _
       (0<y-x→x<y _ _
        (isTrans<≤ᵣ _ _ _
         (snd ((_ , 0≤x<π/2→0<cos[x] y'
            (isTrans≤ᵣ _ _ _ (fst x∈) (<ᵣWeaken≤ᵣ _ _ x<y')) y'<π/2)
           ₊·ᵣ (_ , x<y→0<y-x _ _ x<y')))
         ((Integral-≤ x y' (<ᵣWeaken≤ᵣ _ _ x<y') _ _ _ _
          (λ x' ≤x' x'≤ →
            cos-firstQuarter-Monotone x' y'
             ((isTrans≤ᵣ _ _ _ (fst x∈) ≤x'
               , isTrans≤ᵣ _ _ _ x'≤ (snd y'∈))) y'∈  x'≤)
          (IntegralConstℙ _ _ (<ᵣWeaken≤ᵣ _ _ x<y')
           (cos y'))
          (∫cos x y' (<ᵣWeaken≤ᵣ _ _ x<y'))))))
       (sin-firstQuarter-Monotone y' y
         y'∈ y∈
         (<ᵣWeaken≤ᵣ _ _ y'<y))


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





-- reciporalDerivativeUℙ :
--     ∀ P (f f' : ∀ x → x ∈ P → ℝ)
--      → (fPos : ∀ x x∈ → 0 <ᵣ f x x∈)
--     → IsUContinuousℙ P f
--     → uDerivativeOfℙ P ,
--        ((λ x x∈ → fst (invℝ₊ (f x x∈ , fPos _ _)))) is
--          λ x x∈ → (-ᵣ (f' x x∈ ／ᵣ₊ ((f x x∈ , fPos _ _ ) ₊^ⁿ 2)))
-- reciporalDerivativeUℙ = {!!}

-- DerivativeUℙ-invℝ₊ : ∀ (q : ℚ₊) →
--   uDerivativeOfℙ (pred<≤ 0 (rat (fst q))) ,
--     (λ x x∈ → fst (invℝ₊ (x , (fst x∈))))
--      is λ x x∈ → fst (invℝ₊ ((x , (fst x∈)) ₊^ⁿ 2))
-- DerivativeUℙ-invℝ₊ q = {!!}


-- TODO : if we switch to bishop definition of derivative,
-- we can ditch injectivity of f

opaque
 chainRule-uDℙ : ∀ P P' →
   (f : ∀ x → x ∈ P → ℝ)
   (f' : ∀ x → x ∈ P → ℝ)
   (g : ∀ x → x ∈ P' → ℝ)
   (g' : ∀ x → x ∈ P' → ℝ)
   → (Bounded P f')
   → ∥ (Bounded P' g') ∥₁
   → (f∈ : ∀ x x∈ → f x x∈ ∈ P')
   → IsUContinuousℙ P f
   → (-- (IsUContinuousℙ (pred≤< fa fb) g') ⊎
     (∀ x y x∈ y∈ → x ＃ y → f x x∈ ＃ f y y∈))
   → uDerivativeOfℙ P'
     , g is g'
   → uDerivativeOfℙ P , f is f'
   → uDerivativeOfℙ P , (λ x x∈ → g (f x x∈) (f∈ x x∈))
       is λ x x∈ → g' (f x x∈) (f∈ x x∈)
                     ·ᵣ f' x x∈
 chainRule-uDℙ P P' f f' g g' (∣f'∣ , <∣f'∣) gBd
   f∈ ucf ucg' gD fD ε = do
  (∣g'∣ , <∣g'∣) ← gBd
  let α = ℚ.invℚ₊ (1 ℚ₊+ (∣f'∣)) ℚ₊· /2₊ ε
      β = ℚ.invℚ₊ (α ℚ₊+ ∣g'∣) ℚ₊· /2₊ ε
  (δ-g , <δ-g) ← (gD α)
  (δ-f , <δ-f) ← (fD β)
  let ω-f , <ω-f = ucf δ-g
      δ : ℚ₊
      δ = ℚ.min₊ ω-f δ-f
      g∘f : ∀ x → x ∈ P → ℝ
      g∘f = λ x x∈ → g (f x x∈) (f∈ x x∈)
      g'∘f : ∀ x → x ∈ P → ℝ
      g'∘f = λ x x∈ → g' (f x x∈) (f∈ x x∈)
  ∣ δ , (λ x x∈ h h∈ 0＃h h< →
    let ∣h∣ : ℝ₊
        ∣h∣ = absᵣ h , 0＃→0<abs h 0＃h
        zL : absᵣ
               (g (f (x +ᵣ h) h∈) (f∈ (x +ᵣ h) h∈) -ᵣ g (f x x∈) (f∈ x x∈) -ᵣ
                g' (f x x∈) (f∈ x x∈) ·ᵣ (f (x +ᵣ h) h∈ -ᵣ f x x∈))
               ≤ᵣ
               rat (fst α) ·ᵣ
               (rat (fst ∣f'∣) ·ᵣ absᵣ h +ᵣ
                absᵣ (f' x x∈ ·ᵣ h -ᵣ (f (x +ᵣ h) h∈ -ᵣ f x x∈)))
        zL = isTrans≡≤ᵣ _ _ _
                (minusComm-absᵣ _ _ ∙
                  cong absᵣ (cong₂ _-ᵣ_
                    refl
                    (cong₂ _-ᵣ_
                     (cong (uncurry g)
                      (ΣPathP (sym L𝐑.lem--05 ,
                        toPathP refl)))
                     refl)))
                (isTrans≤ᵣ _ _ _
                   (<ᵣWeaken≤ᵣ _ _
                     (fst  (diff-≃ P' g g' α δ-g _ _ _ _
                      (invEq (＃Δ _ _) (ucg' x (x +ᵣ h) x∈ h∈
                        (fst (＃Δ _ _) (subst (0 ＃_)
                         (sym L𝐑.lem--05 ∙ +ᵣAssoc _ _ _) 0＃h)))))
                        (<δ-g _ _ _ _  _
                          (fst (∼≃abs<ε _ _ _)
                            (<ω-f _ _ _ _
                              (invEq (∼≃abs<ε _ _ _)
                                (isTrans≡<ᵣ _ _ _
                                  (cong absᵣ (sym (+ᵣAssoc _ _ _) ∙ L𝐑.lem--05))
                                  (isTrans<≤ᵣ _ _ _ h< (≤ℚ→≤ᵣ _ _
                            (ℚ.min≤ (fst ω-f) (fst δ-f)))))))))))
                   (≤ᵣ-o·ᵣ _ _
                     _
                     (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ α))
                      (isTrans≤ᵣ _ _ _
                        (isTrans≤≡ᵣ _ _ _ (absᵣ-triangle' _ (f' x x∈ ·ᵣ h))
                        (+ᵣComm _ _ ∙ cong₂ _+ᵣ_
                          (·absᵣ _ _)
                          (minusComm-absᵣ _ _)) )
                          (≤ᵣ-+o _ _ _
                            (≤ᵣ-·ᵣo _ _ _
                              (0≤absᵣ _)
                              (<∣f'∣ _ _)))) ))
        zR : absᵣ
             (g'∘f _ x∈ ·ᵣ
              (f _ h∈ -ᵣ f _ x∈ -ᵣ f' _ x∈ ·ᵣ h))
             ≤ᵣ rat (fst ∣g'∣) ·ᵣ absᵣ (f' _ x∈ ·ᵣ h -ᵣ (f _ h∈ -ᵣ f _ x∈))
        zR = isTrans≡≤ᵣ _ _ _
               (·absᵣ _ _)
               (isTrans≤≡ᵣ _ _ _
                 (≤ᵣ-·ᵣo _ _ _
                              (0≤absᵣ _) (<∣g'∣ _ _))
                 (cong₂ _·ᵣ_ refl
                   (minusComm-absᵣ _ _)))
        uR : absᵣ (f' x x∈ ·ᵣ h -ᵣ (f (x +ᵣ h) h∈ -ᵣ f x x∈)) <ᵣ
             rat (fst β) ·ᵣ absᵣ h
        uR = fst  (diff-≃ P f f' β δ _ _ _ _ _)
                        ((<δ-f x x∈ h h∈ 0＃h
                          (isTrans<≤ᵣ _ _ _ h< (≤ℚ→≤ᵣ _ _
                            (ℚ.min≤' (fst ω-f) (fst δ-f))))))


        z : absᵣ (((g'∘f x x∈) ·ᵣ f' x x∈) ·ᵣ h
             -ᵣ ((g∘f (x +ᵣ h) h∈ -ᵣ g∘f x x∈))) <ᵣ rat (fst ε) ·ᵣ absᵣ h
        z = isTrans≤<ᵣ _
                     ((rat (fst α) ·ᵣ rat (fst ∣f'∣) ·ᵣ absᵣ h)
                   +ᵣ rat (fst (α ℚ₊+ ∣g'∣)) ·ᵣ
                      (absᵣ (f' x x∈ ·ᵣ h -ᵣ (f _ h∈ -ᵣ f _ x∈)))) _
              (isTrans≤ᵣ _ _ _
                (isTrans≡≤ᵣ _ _ _
                  (minusComm-absᵣ _ _  ∙ cong absᵣ
                    (cong₂ _-ᵣ_ refl (sym (·ᵣAssoc _ _ _))))
                  (absᵣ-triangle-midpt
                    _ (g'∘f x x∈ ·ᵣ (f _ h∈ -ᵣ f _ x∈)) _))
                (isTrans≡≤ᵣ _ _ _
                   (cong₂ _+ᵣ_ refl (cong absᵣ (sym (𝐑'.·DistR- _ _ _))))
                   (isTrans≤≡ᵣ _ _ _
                     (≤ᵣMonotone+ᵣ _ _ _ _
                       zL
                       zR)
                     ((cong₂ _+ᵣ_ (·DistL+ _ _ _)
                       refl)
                       ∙ sym (+ᵣAssoc _ _ _)
                      ∙ cong₂ _+ᵣ_
                       (·ᵣAssoc _ _ _)
                       (sym (·DistR+ _ _ _) ∙
                        cong₂ _·ᵣ_ ((+ᵣ-rat (fst α)  (fst ∣g'∣)))
                        refl) ))))
              (isTrans<≡ᵣ _ _ _
                (<ᵣMonotone+ᵣ _ _ _ _
                  ((<ᵣ-·ᵣo _ _ ∣h∣
                    (isTrans<≡ᵣ _ _ _
                      (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ α)
                         (isTrans≡<ᵣ _ _ _
                           (sym (+IdL _))
                           (<ᵣ-+o _ _ (rat (fst ∣f'∣)) (decℚ<ᵣ? {0} {1}))))
                      (·ᵣComm _ _ ∙
                        cong₂ _·ᵣ_ (+ᵣ-rat _ _) refl
                         ∙ sym (rat·ᵣrat _ _)
                          ∙ cong rat (ℚ.y·[x/y] (1 ℚ₊+ (∣f'∣)) _ ) ))))
                  (isTrans<≡ᵣ _ _ _
                    (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ (α ℚ₊+ ∣g'∣)) uR)
                     (·ᵣAssoc _ _ _
                     ∙ cong (_·ᵣ absᵣ h)
                       (sym (rat·ᵣrat _ _) ∙
                        cong rat (ℚ.y·[x/y] (α ℚ₊+ ∣g'∣) _)))))
                (sym (·DistR+ _ _ _) ∙
                  cong₂ _·ᵣ_ (+ᵣ-rat (fst (/2₊ ε)) _ ∙
                   cong rat (ℚ.ε/2+ε/2≡ε (fst ε))) refl))
    in invEq (diff-≃ P g∘f
          (λ x x∈ → g' (f x x∈) (f∈ x x∈)
                     ·ᵣ f' x x∈) ε δ _ _ _ _ _) z ) ∣₁


arcSin'₊ : ∀ x → x ∈ pred≤< 0 1 → ℝ₊
arcSin'₊ x (0≤x , x<1) =
  invℝ₊ (root 2 (1 -ᵣ (x ^ⁿ 2) , x<y→0<y-x _ _
   (^<1 x 0≤x 1 x<1)))

-- uContRoot
arcSin' : ∀ x → x ∈ pred≤< 0 1 → ℝ
arcSin' x x∈ = fst (arcSin'₊ x x∈)

1≡arcSin'0 : 1 ≡ arcSin' 0 (≤ᵣ-refl _ , decℚ<ᵣ? {0} {1})
1≡arcSin'0 = cong fst (sym invℝ₊1) ∙
  cong (fst ∘ invℝ₊) (ℝ₊≡ (sym (cong fst (ₙ√1 2)) ∙
    cong (fst ∘ (root 2))
    (ℝ₊≡ (sym (𝐑'.+IdR' _ _
      (cong -ᵣ_ (0^ⁿ 1) ∙ -ᵣ-rat 0)))) ))

arcSin'-Monotone : ∀ x y x∈ y∈ → x ≤ᵣ y → arcSin' x x∈ ≤ᵣ arcSin' y y∈
arcSin'-Monotone x y x∈ y∈ x≤y =
  invEq (invℝ₊-≤-invℝ₊ _ _)
    (ₙ√-Monotone 2 ((≤ᵣ-o+ _ _ 1
                    (-ᵣ≤ᵣ _ _ (^ⁿ-Monotone 2 (fst x∈)  x≤y)))))

·invℝ₊ : ∀ x y → fst (invℝ₊ (x ₊·ᵣ y)) ≡ fst (invℝ₊ x) ·ᵣ fst (invℝ₊ y)
·invℝ₊ x y =
  sym (·IdL _) ∙
  sym (x·y≡z→x≡z/₊y _ _ _
    (·ᵣComm _ _
     ∙∙    sym (·ᵣAssoc _ _ _)
        ∙∙ cong (fst x ·ᵣ_) (·ᵣAssoc _ _ _ ∙ ·ᵣComm _ _)
        ∙∙ (·ᵣAssoc _ _ _)
     ∙∙ cong₂ _·ᵣ_ (x·invℝ₊[x] x) (x·invℝ₊[x] y) ∙ ·IdL _ )
     )
   ∙ ·ᵣComm _ _

1/v-1/u= : ∀ u₊ v₊ → (fst (invℝ₊ v₊) +ᵣ -ᵣ fst (invℝ₊ u₊)) ≡
          ((u₊ .fst -ᵣ v₊ .fst) ·ᵣ invℝ₊ (u₊ ₊·ᵣ v₊) .fst)
1/v-1/u= u₊@(u , _) v₊@(v , _) =
  cong₂ _-ᵣ_
    (sym ([x/₊y]·yᵣ _ u₊)
      ∙ cong₂ _·ᵣ_ (·ᵣComm _ _) refl)
    (sym ([x/₊y]·yᵣ _ v₊))
    ∙ sym (𝐑'.·DistR- _ _ _)
    ∙ ·ᵣComm _ _
    ∙ cong₂ _·ᵣ_ refl (sym (·invℝ₊ u₊ v₊))


pre-invℝ₊UC : ∀ (x : ℚ₊) →
  IsUContinuousℙ (pred≥ (rat (fst x)))
         (λ x' x≤x' → fst (invℝ₊ (x' ,
           isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ x)) x≤x')))
pre-invℝ₊UC q ε =
  ((q ℚ₊^ⁿ 2) ℚ₊· ε) ,
   λ u v u∈ v∈ → invEq (∼≃abs<ε _ _ _) ∘S
     (λ ∣u-v∣<ε² →
      let u₊ : ℝ₊
          u₊ = (u , isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ q)) u∈)
          v₊ : ℝ₊
          v₊ = (v , isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ q)) v∈)
      in isTrans≡<ᵣ _ (absᵣ (u -ᵣ v) ·ᵣ
        fst (invℝ₊ (u₊ ₊·ᵣ v₊))) _
          (minusComm-absᵣ _ _ ∙ cong absᵣ (1/v-1/u= u₊ v₊)
            -- (cong₂ _-ᵣ_ {!!} {!!}
            --  ∙ sym (𝐑'.·DistR- _ _ _) ∙ ·ᵣComm _ _)
             ∙ ·absᵣ _ _ ∙
            cong₂ _·ᵣ_
              refl (absᵣPos _ (snd (invℝ₊ (u₊ ₊·ᵣ v₊)))))

           (invEq (z/y<x₊≃z<y₊·x _ _ _)
             (isTrans<≤ᵣ _ _ _ ∣u-v∣<ε²
              (isTrans≡≤ᵣ _ _ _
               (rat·ᵣrat (fst (q ℚ₊^ⁿ 2)) _)
               (≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ ε)))
                (isTrans≡≤ᵣ _ _ _
                 (cong fst (sym (^ℤ-rat q (pos 2))))
                 (≤ᵣ₊Monotone·ᵣ _ _ _ _
                   (<ᵣWeaken≤ᵣ _ _ (snd u₊))
                   (<ᵣWeaken≤ᵣ _ _ (ℚ₊→ℝ₊ q .snd))
                   (isTrans≡≤ᵣ _ _ _ (·IdL _) u∈) v∈))))))) ∘S
     fst (∼≃abs<ε _ _ _)





invℝ₊UC : ∀ x → (0<x : 0 <ᵣ x) → ∥ IsUContinuousℙ (pred≥ x)
         (λ x' x≤x' → fst (invℝ₊ (x' , isTrans<≤ᵣ _ _ _ 0<x x≤x'))) ∥₁
invℝ₊UC x 0<x =
  PT.map (λ (δ , 0<q , q<x) →
    subst (IsUContinuousℙ (pred≥ x))
      (funExt₂ λ _ _ →
        cong (fst ∘ invℝ₊)
          (Σ≡Prop (∈-isProp (pred> _)) refl))
      (IsUContinuousℙ-restr (pred≥ (rat δ)) (pred≥ x) _
       (λ x x∈ → isTrans≤ᵣ _ _ _
         (<ᵣWeaken≤ᵣ _ _ q<x)
         x∈)
      (pre-invℝ₊UC (δ , ℚ.<→0< δ (<ᵣ→<ℚ 0 δ 0<q)))))
    (denseℚinℝ _ _ 0<x)

arcSin'-UC : ∀ x → (x∈ : x ∈ pred≤< 0 1) →
   ∥ IsUContinuousℙ (intervalℙ 0 x)
      (λ x' x'∈ → arcSin' x' (fst x'∈ , isTrans≤<ᵣ x' x 1 (snd x'∈) (snd x∈)))
      ∥₁
arcSin'-UC y (0≤y , y<1) =
 let z =
      PT.map (flip (IsUContinuousℙ∘ℙ (intervalℙ 0 y)
        (intervalℙ (fst (root 2 (1 -ᵣ y ^ⁿ 2 ,
          (x<y→0<y-x _ _ (^<1 y 0≤y 1 y<1)))))  1)
        {λ x x∈ → fst
          (invℝ₊
           ((x , isTrans<≤ᵣ _ _ _
             (snd (root 2 (1 -ᵣ (y ^ⁿ 2) ,
             x<y→0<y-x (y ^ⁿ 2) 1 (^<1 y 0≤y 1 y<1))))
             (fst  x∈))))}
                 λ x' (0≤x' , x'<y) →
                   ₙ√-Monotone 2 (≤ᵣ-o+ _ _ 1
                    (-ᵣ≤ᵣ _ _ (^ⁿ-Monotone 2 0≤x'  x'<y)))  ,
                   (isTrans≤≡ᵣ _ _ _
                   (ₙ√-Monotone {y = 1} 2 (isTrans≤≡ᵣ _ _ _
                     (≤ᵣ-o+ _ _ 1 (-ᵣ≤ᵣ _ _ ( 0≤x^ⁿ x' 2 0≤x')))
                      (𝐑'.+IdR' _ _ (-ᵣ-rat 0))))
                    (cong fst (ₙ√1 2) )) )

         (IsUContinuousℙ∘ℙ (intervalℙ 0 y) (pred> 0)
           {λ x x∈ → fst (root 2 (x , x∈)) }
            {λ x _ → 1 -ᵣ (x ^ⁿ 2)}
           (λ x x∈ → x<y→0<y-x _ _ (^<1 x (fst x∈) 1
            (isTrans≤<ᵣ _ _ _ (snd x∈) y<1)))
           (uContRoot 2)
           (IsUContinuousℙ+ᵣ₂ (intervalℙ 0 y) _ _
            (IsUContinuousℙ-const (intervalℙ 0 y) 1)
            (IsUContinuousℙ-ᵣ∘
             (intervalℙ 0 y) _
               (IsUContinuousℙ-restr (intervalℙ 0 1) (intervalℙ 0 y)
                 _ (λ x → map-snd (flip (isTrans≤ᵣ _ _ _) (<ᵣWeaken≤ᵣ _ _ y<1) ))
               (IsUContinuousℙ^ⁿ 0 1 ((decℚ≤ᵣ? {0} {1})) 2)))))
               )

        (PT.map
         (subst (IsUContinuousℙ (intervalℙ _ 1))
          (funExt₂ λ x _ → cong (fst ∘ invℝ₊) (ℝ₊≡ refl)) ∘
            IsUContinuousℙ-restr (pred≥ _)
             (intervalℙ _ 1)
              (λ x x∈ → fst (invℝ₊ (x , _)))
               λ _ → fst)
            (invℝ₊UC _ ((snd (root 2 (1 -ᵣ y ^ⁿ 2 ,
          (x<y→0<y-x _ _ (^<1 y 0≤y 1 y<1))))))))
  in
    PT.map (subst (IsUContinuousℙ (intervalℙ (rat [ pos 0 / 1+ 0 ]) y))
     (funExt₂ λ x x∈ →
        cong (fst ∘ invℝ₊) (ℝ₊≡
          refl))) z

opaque
 arcSinDef : ∀ x → (x∈ : x ∈ pred≤< 0 1) →
   Σ[ arcSinX ∈ ℝ ]
     (on[ 0 , x ]IntegralOf
       (λ x' ≤x x< → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x< (snd x∈))) is arcSinX )
 arcSinDef x x∈@(0≤x , x<1) =
  PT.rec
   (IntegratedℙPropℙ _ _ 0≤x _)
    (Integrate-UContinuousℙ
    0
    x
    0≤x
    (λ x' x'∈ → arcSin' x' ((fst x'∈) , isTrans≤<ᵣ _ _ _ (snd x'∈) x<1)))
    (arcSin'-UC x x∈)



arcSin : ∀ x → (x∈ : x ∈ pred≤< 0 1) → ℝ
arcSin x x∈ = fst (arcSinDef x x∈)

emptyIntegral : ∀ x f → (on[ x , x ]IntegralOf f is 0 )
emptyIntegral x f ε = ∣ 1 ,
  (λ (_ , tp) _ → isTrans≡<ᵣ _ _ _
    (cong absᵣ (𝐑'.+InvR' _ _ (sym (riemannSum-empty tp (uncurry ∘ f) refl)) )
     ∙ absᵣ0)
    (snd (ℚ₊→ℝ₊ ε))) ∣₁

arcSin[0]≡0 : (0∈ : 0 ∈ pred≤< 0 1) → arcSin 0 0∈ ≡ 0
arcSin[0]≡0 0∈ = IntegralUniq 0 0 (fst 0∈) _ _ _
  (snd (arcSinDef 0 0∈)) (emptyIntegral 0 _)

arcSinInj : ∀ x y x∈ y∈ → arcSin x x∈ ≡ arcSin y y∈ → x ≡ y
arcSinInj x y x∈@(0≤x , x<1) y∈@(0≤y , y<1) p =
  ≡-byContracdition _ _ w


  where
  w : (ε : ℚ₊) → rat (fst ε) <ᵣ absᵣ (x -ᵣ y) → ⊥
  w ε ε< =
    ⊎.rec
           (w' y x y∈ x∈ (sym p))
           (w' x y x∈ y∈ p)
      cases<
   where
     -- TODO : lemma somwhere in order
     cases< :  (y +ᵣ rat (fst ε) <ᵣ x) ⊎ (x +ᵣ rat (fst ε) <ᵣ y)
     cases< = ⊎.map
         (λ 0<x-y →
            let z = isTrans<≡ᵣ _ _ _ ε< (absᵣPos _ 0<x-y)
            in isTrans≡<ᵣ _ _ _ (+ᵣComm _ _) (a<b-c⇒a+c<b _ _ _ z))
         (λ 0<y-x →
            let z = isTrans<≡ᵣ _ _ _ ε< (absᵣNeg _ 0<y-x ∙ -[x-y]≡y-x _ _)
            in isTrans≡<ᵣ _ _ _ (+ᵣComm _ _) (a<b-c⇒a+c<b _ _ _ z))
       (decCut _ (isTrans<ᵣ _ _ _ (snd (ℚ₊→ℝ₊ ε)) ε<))

     w' : ∀ x y x∈ y∈ → arcSin x x∈ ≡ arcSin y y∈ →
          x +ᵣ rat (fst ε) <ᵣ y → ⊥
     w' x y x∈@(0≤x , x<1) y∈@(0≤y , y<1) p x+ε<y =
       ≤ᵣ→≯ᵣ (fst Δ) 0
         (≤-o+-cancel _ _ _ (≡ᵣWeaken≤ᵣ _ _ (cc ∙ sym p ∙ sym (+IdR _))))
         0<Δ

      where
       x<y : x <ᵣ y
       x<y = isTrans<ᵣ _ _ _
         (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
          (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ ε)))) x+ε<y

       x≤y : x ≤ᵣ y
       x≤y = <ᵣWeaken≤ᵣ _ _ x<y

       Δ : Σ ℝ (on[_,_]IntegralOf_is_ x y (curry ∘ (λ x' x'∈ → arcSin' x' _)))
       Δ = PT.rec
           (IntegratedℙPropℙ _ _ x≤y
             (curry ∘ (λ x' x'∈ → arcSin' x' _)))
               (Integrate-UContinuousℙ
                x
                y
                x≤y
                (λ x' x'∈ → arcSin' x' _) ∘
                IsUContinuousℙ-restr (intervalℙ 0 y) (intervalℙ x y) _
                  λ _ → map-fst λ x∈ → isTrans≤ᵣ _ _ _ 0≤x x∈)
                (arcSin'-UC y y∈)

       0<Δ : 0 <ᵣ fst Δ
       0<Δ = isTrans<≤ᵣ 0 _ _
          (isTrans<≡ᵣ _ _ _ (x<y→0<y-x _ _ x<y) (sym (·IdL _)))
          (Integral-≤ x y x≤y (λ _ _ _ → 1)
            _
            _
            _
            (λ x' ≤x' x'≤ → (isTrans≡≤ᵣ _ _ _ 1≡arcSin'0
              (arcSin'-Monotone _ _ _ _ (isTrans≤ᵣ _ _ _ 0≤x ≤x'))))
            (IntegralConstℙ x y x≤y 1)
            (snd Δ))

       arcSin-x : _
       arcSin-x = subst (λ f → on[ 0 , x ]IntegralOf
            f is
            arcSinDef x (0≤x , x<1) .fst)
              (funExt₃ λ x' _ _ →
                cong (arcSin' x') (∈-isProp (pred≤< 0 1) _ _ _))
              (snd (arcSinDef x x∈))

       cc : arcSin x (0≤x , x<1) +ᵣ Δ .fst ≡ arcSin y (0≤y , y<1)
       cc = Integral-additive 0 x y
              0≤x x≤y
                (λ r z z₁ → arcSin' r (z , isTrans≤<ᵣ r y 1 z₁ y<1))
                ((arcSin x x∈))
               (Δ .fst)
               (arcSin y y∈)
               arcSin-x (snd Δ) (snd (arcSinDef y y∈))


arcSinDer : ∀ x → (x∈ : x ∈ ointervalℙ 0 1) →
 uDerivativeOfℙ intervalℙ 0 x ,
  (λ x' (≤x , x≤) → arcSin x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈))) is
    (λ x' (≤x , x≤) → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈)))
arcSinDer x x∈ =
   PT.rec (isProp-uDerivativeOfℙ (intervalℙ 0 x) _ _)
        (FTOC⇒* 0 x (<ᵣWeaken≤ᵣ _ _ (fst x∈))
          _
          _
            (λ x₁ x∈₁ y y∈ →
              (fst y∈ , isTrans≤ᵣ _ _ _ (snd y∈) (snd x∈₁)))
            λ y y∈ →
              subst (λ f → on[ 0 , y ]IntegralOf
                f
                is (arcSinDef y (y∈ .fst ,
                 isTrans≤<ᵣ y x 1 (y∈ .snd) (snd x∈)) .fst))
                (funExt₃ λ x' _ _ →
                 cong (arcSin' x') (∈-isProp (pred≤< 0 1) _ _ _) )
                  ((snd (arcSinDef y
                         (y∈ .fst , isTrans≤<ᵣ y x 1 (y∈ .snd) (snd x∈))))))
        (arcSin'-UC x (<ᵣWeaken≤ᵣ _ _ (fst x∈) , snd x∈))



x∈[0,π/2⟩→sin[x]∈[0,1⟩ : ∀ x → x ∈ pred≤< 0 π-number/2 → sin x ∈ pred≤< 0 1
x∈[0,π/2⟩→sin[x]∈[0,1⟩ x x∈ =
 isTrans≡≤ᵣ _ _ _ (sym sin0=0)
  (sin-firstQuarter-Monotone 0 x
   (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ 0<π-number/2)
    (map-snd (<ᵣWeaken≤ᵣ _ _) x∈)
    (fst x∈))
  ,
  (isTrans<≡ᵣ _ _ _
   (sin-firstQuarter-strictMonotone _ _
    (fst x∈ , <ᵣWeaken≤ᵣ _ _ (snd x∈))
     (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) (snd x∈))
   sin[π/2]≡1)

x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ : ∀ x → x ∈ ointervalℙ 0 π-number/2 → sin x ∈ ointervalℙ 0 1
x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈ =
  isTrans≡<ᵣ _ _ _ (sym sin0=0)
  (sin-firstQuarter-strictMonotone 0 x
   ((≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ 0<π-number/2))
    (ointervalℙ⊆intervalℙ _ _ _ x∈)
    (fst x∈))
  ,
  (isTrans<≡ᵣ _ _ _
   (sin-firstQuarter-strictMonotone _ _
    (ointervalℙ⊆intervalℙ _ _ _ x∈ )
     (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) (snd x∈))
   sin[π/2]≡1)


bounded-arcSin' : ∀ x → (x∈ : x ∈ ointervalℙ 0 1) →
  ∥ Bounded (intervalℙ 0 x)
    (λ x' (≤x , x≤) → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈)))
    ∥₁
bounded-arcSin' x x∈ =
  PT.map
   (map-snd (λ {q} X x' x'∈ →
     isTrans≡≤ᵣ _ _ _ (absᵣPos _ (snd (arcSin'₊ x'
        (map-snd (flip (isTrans≤<ᵣ _ _ _) (snd x∈)) x'∈ ))))
      (isTrans≤ᵣ _ _ _
       (arcSin'-Monotone x' x _ _ (snd x'∈))
       (<ᵣWeaken≤ᵣ _ _ X))))
   (∃ℚ₊LargerThanℝ₊
    (arcSin'₊ x (map-fst (<ᵣWeaken≤ᵣ _ _) x∈)))


sin＃-firstQuarter : (x y : ℝ) (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2) →
      x ＃ y → sin x ＃ sin y
sin＃-firstQuarter x y x∈ y∈ =
 ⊎.map (sin-firstQuarter-strictMonotone x y x∈ y∈)
       (sin-firstQuarter-strictMonotone y x y∈ x∈)

[arcSin∘Sin]'=1 : ∀ x → (x∈ : x ∈ ointervalℙ 0 π-number/2) →
  uDerivativeOfℙ (intervalℙ 0 x) ,
     (λ x' x'∈ → arcSin (sin x')
      ((x∈[0,π/2⟩→sin[x]∈[0,1⟩ x'
       (map-snd (flip (isTrans≤<ᵣ _ _ _) (snd x∈)) x'∈)))) is λ _ _ → 1
[arcSin∘Sin]'=1 x x∈ =
  subst2 (uDerivativeOfℙ (intervalℙ 0 x) ,_is_)
      (funExt₂ λ _ _ → cong (uncurry arcSin)
       (Σ≡Prop (∈-isProp (pred≤< 0 1)) refl))
      (funExt₂ w=)
      w
 where
 w : uDerivativeOfℙ intervalℙ 0 x , _ is _

 w = chainRule-uDℙ (intervalℙ 0 x) (intervalℙ 0 (sin x))
        (λ x _ → sin x) (λ x _ → cos x) _ _
        (bounded-cos (intervalℙ 0 x))
        (bounded-arcSin' (sin x) (x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈)) --bounded-arcSin'
        (λ y y∈ → fst (x∈[0,π/2⟩→sin[x]∈[0,1⟩ y
          ((map-snd (flip (isTrans≤<ᵣ y x π-number/2) (snd x∈)) y∈))) ,
         sin-firstQuarter-Monotone y x
           (map-snd (flip (isTrans≤ᵣ _ _ _) (<ᵣWeaken≤ᵣ _ _ (snd x∈))) y∈)
           (ointervalℙ⊆intervalℙ _ _ _ x∈) (snd y∈))
        (uContSin (intervalℙ 0 x))
        (λ x' y x'∈ y∈ →
          sin＃-firstQuarter x' y
            (map-snd (flip (isTrans≤ᵣ _ _ _) (<ᵣWeaken≤ᵣ _ _ (snd x∈))) x'∈)
            (map-snd (flip (isTrans≤ᵣ _ _ _) (<ᵣWeaken≤ᵣ _ _ (snd x∈))) y∈))
        (arcSinDer (sin x) (x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈))
        (sin'=cos-uder' 0 x (fst x∈))



 w= : ∀ (x' : ℝ) x'∈ →
      _ ≡ 1
 w= x' x'∈ =
   cong (_·ᵣ fst cosx₊)
    (cong (fst ∘ invℝ₊)
      (ℝ₊≡ (cong fst (sym
       (invEq (equivAdjointEquiv
         (_ , isEquiv-₊^ⁿ 2) {_ , snd cosx₊})
        (ℝ₊≡
         (sym (𝐑'.plusMinus _ _)
         ∙ cong (_-ᵣ (sin x' ^ⁿ 2))
         (+ᵣComm _ _ ∙ sin²+cos²=1 x'))))))))
    ∙ ·ᵣComm _ _ ∙ x·invℝ₊[x] cosx₊
  where
   cosx₊ : ℝ₊
   cosx₊ = (cos x' , 0≤x<π/2→0<cos[x] x' (fst x'∈)
     (isTrans≤<ᵣ _ _ _ (snd x'∈) (snd x∈)))


module as-mon x y (x∈@(0≤x , _) : x ∈ pred≤< 0 1)
             (y∈@(_ , y<1) : y ∈ pred≤< 0 1)
             (x≤y : x ≤ᵣ y) where



 Δ : Σ ℝ (on[_,_]IntegralOf_is_ x y (curry ∘ (λ x' x'∈ → arcSin' x' _)))
 Δ = PT.rec
     (IntegratedℙPropℙ _ _ x≤y
       (curry ∘ (λ x' x'∈ → arcSin' x' _)))
         (Integrate-UContinuousℙ
          x
          y
          x≤y
          (λ x' x'∈ → arcSin' x' _) ∘
          IsUContinuousℙ-restr (intervalℙ 0 y) (intervalℙ x y) _
            λ _ → map-fst λ x∈ → isTrans≤ᵣ _ _ _ 0≤x x∈)
          (arcSin'-UC y y∈)

 z : arcSin x x∈ +ᵣ fst Δ ≡ arcSin y y∈
 z = Integral-additive 0 x y
              0≤x x≤y
                (λ r z z₁ → arcSin' r (z , isTrans≤<ᵣ r y 1 z₁ y<1))
                ((arcSin x x∈))
               (fst Δ)
               (arcSin y y∈)
               (subst (λ f → on[ 0 , x ]IntegralOf
                 f is
                 arcSinDef x x∈ .fst)
                   (funExt₃ λ x' _ _ →
                     cong (arcSin' x') (∈-isProp (pred≤< 0 1) _ _ _))
                   (snd (arcSinDef x x∈)))
               (snd Δ) (snd (arcSinDef y y∈))

 0≤Δ : 0 ≤ᵣ fst Δ
 0≤Δ = isTrans≤ᵣ 0 _ _
          (isTrans≤≡ᵣ _ _ _ (x≤y→0≤y-x _ _ x≤y) (sym (·IdL (y +ᵣ -ᵣ x))))
          (Integral-≤ x y x≤y (λ _ _ _ → 1)
            _
            _
            _
            (λ x' ≤x' x'≤ → (isTrans≡≤ᵣ _ _ _ 1≡arcSin'0
              (arcSin'-Monotone _ _ _ _ (isTrans≤ᵣ _ _ _ 0≤x ≤x'))))
            (IntegralConstℙ x y x≤y 1)
            (snd Δ))



 arcSin-Monotone : arcSin x x∈ ≤ᵣ arcSin y y∈
 arcSin-Monotone =
     isTrans≤≡ᵣ _ _ _
       (isTrans≡≤ᵣ _ _ _
         (sym (+IdR _))
         (≤ᵣ-o+ _ _ _ 0≤Δ))
      z


 arcSin-MonotoneStrict : x <ᵣ y → arcSin x x∈ <ᵣ arcSin y y∈
 arcSin-MonotoneStrict x<y =
    isTrans<≡ᵣ _ _ _
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _))
         (<ᵣ-o+ _ _ _ 0<Δ))
      z
  where
  0<Δ : 0 <ᵣ fst Δ
  0<Δ = isTrans<≤ᵣ 0 _ _
          (isTrans<≡ᵣ _ _ _ (x<y→0<y-x _ _ x<y) (sym (·IdL (y +ᵣ -ᵣ x))))
          (Integral-≤ x y x≤y (λ _ _ _ → 1)
            _
            _
            _
            (λ x' ≤x' x'≤ → (isTrans≡≤ᵣ _ _ _ 1≡arcSin'0
              (arcSin'-Monotone _ _ _ _ (isTrans≤ᵣ _ _ _ 0≤x ≤x'))))
            (IntegralConstℙ x y x≤y 1)
            (snd Δ))


open as-mon public using (arcSin-Monotone)

arcSin-MonotoneStrict : ∀ x y x∈ y∈ → x <ᵣ y → arcSin x x∈ <ᵣ arcSin y y∈
arcSin-MonotoneStrict x y x∈ y∈ x<y =
 as-mon.arcSin-MonotoneStrict x y x∈ y∈ (<ᵣWeaken≤ᵣ _ _ x<y) x<y


secArcSin : ∀ x sinx∈ (x∈ : x ∈ pred≤< 0 π-number/2) → arcSin (sin x) sinx∈ ≡ x
secArcSin x sinx∈ x∈@(0≤x , _) =
 let (x' , x<x' , x'<π/2) = (denseℝ x π-number/2 (snd x∈))
     0<x' = (isTrans≤<ᵣ _ _ _ (fst x∈) x<x')
     z = FTOC⇐'' 0 x' 0<x'
           _ _ (IsUContinuousℙ-const (intervalℙ 0 x') _) ([arcSin∘Sin]'=1 x'
             (isTrans≤<ᵣ _ _ _ (fst x∈) x<x' , x'<π/2))
          x ((fst x∈) , (<ᵣWeaken≤ᵣ _ _ x<x'))
 in (cong (arcSin (sin x)) (∈-isProp (pred≤< 0 1) _ _ _)
       ∙ sym (𝐑'.+IdR' _ _
         (cong -ᵣ_ (cong (uncurry arcSin)
           (Σ≡Prop (∈-isProp (pred≤< 0 1)) {v = _ , ≤ᵣ-refl 0 , decℚ<ᵣ? {0} {1}}
            sin0=0) ∙ arcSin[0]≡0 _)  ∙ -ᵣ-rat 0))) ∙∙ IntegralUniq 0 x 0≤x (λ r _ _ → 1) _ _
     z (IntegralConstℙ 0 x 0≤x 1)
     ∙∙ (·IdL _ ∙ 𝐑'.+IdR' _ _ (-ᵣ-rat 0))

arcSin∈[0,1⟩ : ∀ x x∈ → arcSin x x∈ ∈ pred≤< 0 π-number/2
arcSin∈[0,1⟩ x x∈ =

  PT.rec (∈-isProp (pred≤< 0 π-number/2) _)
   (λ (q , x<q , q<1) →
     let z = ≤ᵣ-ᵣ _ _ (≤-o+-cancel _ _ _ (subst2 _≤ᵣ_
             (cong absᵣ (cong₂ _-ᵣ_ sin[π/2]≡1 refl)
               ∙ absᵣNonNeg _ (x≤y→0≤y-x _ _ (sin≤1 _)))
             (cong absᵣ L𝐑.lem--079
               ∙ absᵣPos _ (x<y→0<y-x _ _  q<1))
             (sinDiffBound π-number/2
            (π-number/2 -ᵣ (1 -ᵣ rat q)))))
         zz = (isTrans<≡ᵣ _ _ _
                   (<ᵣ-o+ _ _ _ (-ᵣ<ᵣ _ _ ((x<y→0<y-x _ _  q<1))))
                   (𝐑'.+IdR' _ _ (-ᵣ-rat 0)))
         zzz = (x≤y→0≤y-x _ _
                 (isTrans≤ᵣ _ _ _

                    (isTrans≤≡ᵣ _ _ _
                      (≤ᵣ-o+ _ _ _
                       (-ᵣ≤ᵣ _ _ (isTrans≤ᵣ _ _ _
                        (fst x∈) (<ᵣWeaken≤ᵣ _ _ x<q))))
                      (𝐑'.+IdR' _ _ (-ᵣ-rat 0)))
                    (<ᵣWeaken≤ᵣ _ _ 1<π-number/2)))
     in isTrans≡≤ᵣ _ _ _
          (sym (arcSin[0]≡0 _))
          (arcSin-Monotone 0 x (≤ᵣ-refl 0 , decℚ<ᵣ? {0} {1})
            x∈ (fst x∈)) ,
         isTrans<ᵣ _ _ _
           (arcSin-MonotoneStrict x (sin (π-number/2 -ᵣ (1 -ᵣ rat q)))
             x∈ (isTrans≡≤ᵣ _ _ _
                  (sym sin0=0)
                  (sin-firstQuarter-Monotone 0
                    _ (≤ᵣ-refl _ , (<ᵣWeaken≤ᵣ _ _ 0<π-number/2))
                    (zzz , <ᵣWeaken≤ᵣ _ _ zz)
                 zzz) ,
              isTrans<≡ᵣ _ _ _
               (sin-firstQuarter-strictMonotone _ _
                (zzz
                  , (<ᵣWeaken≤ᵣ _ _ zz))
                (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) zz)
                sin[π/2]≡1)
            (isTrans<≤ᵣ _ _ _ x<q
               z)) (isTrans≡<ᵣ _ _ _
                 (secArcSin _ _
                  (zzz , zz)) zz))
   (denseℚinℝ _ _ (snd x∈))


retArcSin : ∀ x x∈ → sin (arcSin x x∈) ≡ x
retArcSin x x∈ =
  let y = sin (arcSin x x∈)
      y∈ = x∈[0,π/2⟩→sin[x]∈[0,1⟩ (arcSin x x∈)
        (arcSin∈[0,1⟩ x x∈)
  in arcSinInj _ _ y∈ x∈
      (secArcSin _ y∈ (arcSin∈[0,1⟩ x x∈))



-ℝ₊<ℝ₊ : (x y : ℝ₊) → -ᵣ (fst x) <ᵣ fst y
-ℝ₊<ℝ₊ (x , 0<x) (y , 0<y) = isTrans<ᵣ _ _ _
  (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ 0<x) (-ᵣ-rat 0)) 0<y

intervalℙ⊆ointervalℙ : ∀ a' b' a b → a <ᵣ a' → b' <ᵣ b
  → intervalℙ a' b' ⊆ ointervalℙ a b
intervalℙ⊆ointervalℙ a' b' a b a<a' b'<b x (a'≤x , x≤b') =
  isTrans<≤ᵣ _ _ _ a<a' a'≤x ,
   isTrans≤<ᵣ _ _ _ x≤b' b'<b

sym-intervalℙ⊆ointervalℙ : ∀ a b → a <ᵣ b →
  intervalℙ (-ᵣ a) a ⊆ ointervalℙ (-ᵣ b) b
sym-intervalℙ⊆ointervalℙ a b a<b =
 intervalℙ⊆ointervalℙ _ _ _ _ (-ᵣ<ᵣ _ _ a<b) a<b


IsContinuousWithPred-ᵣ : ∀ P f → IsContinuousWithPred P f →
  IsContinuousWithPred P λ x x∈ → -ᵣ (f x x∈)
IsContinuousWithPred-ᵣ P f fc =
  IsContinuousWP∘' P _ _ IsContinuous-ᵣ fc


Integral-additive* : ∀ (P : ℙ ℝ ) a b c → a ≤ᵣ b →  b ≤ᵣ c
  → ∀ (f : ∀ x → x ∈ P → ℝ)
  → {ab⊂P : intervalℙ a b ⊆ P}
  → {bc⊂P : intervalℙ b c ⊆ P}
  → {ac⊂P : intervalℙ a c ⊆ P}
  → ∀ {s s' s+s'} →
  on[ a , b ]IntegralOf (λ x ≤x x≤ → f x (ab⊂P x (≤x , x≤))) is s →
  on[ b , c ]IntegralOf (λ x ≤x x≤ → f x (bc⊂P x (≤x , x≤))) is s' →
  on[ a , c ]IntegralOf (λ x ≤x x≤ → f x (ac⊂P x (≤x , x≤))) is s+s' →
  s +ᵣ s' ≡ s+s'
Integral-additive* P a b c a≤b b≤c f {s = s} {s'} s∫ s'∫ s+s'∫ =
 Integral-additive a b c a≤b b≤c _ _ _ _
   (subst (on[ a , b ]IntegralOf_is s)
    (funExt₃ λ x _ _ → cong (f x) (snd (P _) _ _)) s∫)
   (subst (on[ b , c ]IntegralOf_is s')
    (funExt₃ λ x _ _ → cong (f x) (snd (P _) _ _)) s'∫)
   s+s'∫

IntegralNonNeg : ∀ a b → a ≤ᵣ b → ∀ f s →  on[ a , b ]IntegralOf f is s →
               (∀ x ≤x x≤ → 0 ≤ᵣ f x ≤x x≤ ) → 0 ≤ᵣ s
IntegralNonNeg a b a≤b f _ s∫ 0≤f =
 isTrans≡≤ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
  (Integral-≤ a b a≤b (λ _ _ _ → 0) _ _ _
  0≤f (IntegralConstℙ a b a≤b  0) s∫)


arcSinDiff-Help : ∀ U → 0 ≤ᵣ U → U <ᵣ 1 → Σ[ L ∈ ℝ₊ ]
 (∀ u u' u∈ u'∈ →  u ≤ᵣ U → u' ≤ᵣ U
               →  absᵣ (arcSin u u∈ -ᵣ arcSin u' u'∈) ≤ᵣ

                  absᵣ (u -ᵣ u') ·ᵣ fst L )
arcSinDiff-Help U 0≤U U<1 =
   2 ₊·ᵣ L , w

 where

  U∈ = (0≤U , U<1)

  L : ℝ₊
  L = arcSin'₊ U U∈


  w : _
  w u u' u∈@(0≤u , u<1) u'∈@(0≤u' , u'<1) u≤U u'≤U =
   isTrans≤ᵣ _ _ _
   (isTrans≡≤ᵣ _ _ _
    (cong absᵣ (cong₂ _-ᵣ_ h h' ∙ L𝐑.lem--081))
      (isTrans≤≡ᵣ _ _ _
        (absᵣ-triangle _ _)
        (cong₂ _+ᵣ_ (absᵣNonNeg _
           (IntegralNonNeg _ _ (min≤ᵣ u u') _ _ (snd u∫ )
            λ x ≤x x< →
              <ᵣWeaken≤ᵣ _ _ (snd (arcSin'₊ _ (_ , isTrans≤<ᵣ _ _ _ x< _)))))
         (sym (-absᵣ _)  ∙ absᵣNonNeg _
           ((IntegralNonNeg _ _ (min≤ᵣ' u u') _ _ (snd u'∫)
             λ x ≤x x< →
              <ᵣWeaken≤ᵣ _ _ (snd (arcSin'₊ _ (_ , isTrans≤<ᵣ _ _ _ x< _)))))))))
    (isTrans≤ᵣ _ _ _
      (≤ᵣMonotone+ᵣ _ _ _ _
        (Integral-≤ _ _ (min≤ᵣ u u') _ _ _ _
          (λ x ≤x x≤ →
            arcSin'-Monotone _ _ _ U∈
              (isTrans≤ᵣ _ _ _ x≤ (u≤U)) )
          (snd u∫) (IntegralConstℙ _ _ (min≤ᵣ u u') (fst L)))
        (Integral-≤ _ _ (min≤ᵣ' u u') _ _ _ _
          (λ x ≤x x≤ →
            arcSin'-Monotone _ _ _ U∈
               (isTrans≤ᵣ _ _ _ x≤ u'≤U))
          (snd u'∫) (IntegralConstℙ _ _ (min≤ᵣ' u u') (fst L))))
      (isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _
        (sym (·DistL+ _ _ _) ∙ ·ᵣComm _ _ )

        (≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd L))
         (isTrans≤≡ᵣ _ _ _
           (≤ᵣMonotone+ᵣ _ _ _ _
             (≤ᵣ-+o _ _ _ (≤maxᵣ u u'))
             (≤ᵣ-+o _ _ _ (isTrans≤≡ᵣ _ _ _ (≤maxᵣ u' u) (maxᵣComm u' u))))
           (x+x≡2x _ ∙ (·ᵣComm _ _ ))))
         ) (sym (·ᵣAssoc _ 2 (fst L)) ∙ cong₂ _·ᵣ_ (sym (absᵣNonNeg _
         (fst (x≤y≃0≤y-x _ _)
         (isTrans≤ᵣ _ _ _ (min≤ᵣ u u' ) (≤maxᵣ u u'))))
         ∙ absᵣ-min-max u u') refl) ) )
    where


       u⊓u' : ℝ₀₊
       u⊓u' = minᵣ₀₊ (_ ,  0≤u) (_ , 0≤u')

       u⊓u'∈ : fst u⊓u' ∈ pred≤< 0 1
       u⊓u'∈ = snd u⊓u' , isTrans≤<ᵣ _ _ _ (min≤ᵣ _ _) u<1

       u∫ = (PT.rec
                  (IntegratedℙPropℙ _ _ (min≤ᵣ u u') _)
                   ((Integrate-UContinuousℙ
                   (fst u⊓u')
                   u
                   (min≤ᵣ u u')
                   (λ x' x'∈ → arcSin' _ _))
                   ∘ IsUContinuousℙ-restr (intervalℙ 0 u)
                      (intervalℙ _ _) _
                      λ x → map-fst (isTrans≤ᵣ _ _ _ (snd u⊓u') ))
                   ((arcSin'-UC u u∈)))

       u'∫ = (PT.rec
                  (IntegratedℙPropℙ _ _ (min≤ᵣ' u u') _)
                   ((Integrate-UContinuousℙ
                   (fst u⊓u')
                   u'
                   (min≤ᵣ' u u')
                   (λ x' x'∈ → arcSin' _ _))
                   ∘ IsUContinuousℙ-restr (intervalℙ 0 u')
                      (intervalℙ _ _) _
                      λ x → map-fst (isTrans≤ᵣ _ _ _ (snd u⊓u') ))
                   ((arcSin'-UC u' u'∈)))

       h : _
       h = sym (Integral-additive* (pred≤< 0 1)
               0 (fst u⊓u') u (snd u⊓u') (min≤ᵣ u u') arcSin'
               (snd (arcSinDef _ u⊓u'∈))
                (snd u∫)
                (snd (arcSinDef _ _)))


       h' : _
       h' = sym (Integral-additive* (pred≤< 0 1)
               0 (fst u⊓u') u' (snd u⊓u') (min≤ᵣ' u u') arcSin'
               (snd (arcSinDef _ u⊓u'∈))
                (snd u'∫)
                (snd (arcSinDef _ _)))

IsContinuousWithPredArcSin : IsContinuousWithPred (pred≤< 0 1) arcSin
IsContinuousWithPredArcSin u ε u∈@(0≤u , u<1) = do
  let (b , u<b , b<1) = denseℝ _ _ u<1
  (η , 0<η , η<b-u) ← denseℚinℝ _ _ (x<y→0<y-x _ _ u<b)
  let L , ≤L = arcSinDiff-Help b
            (isTrans≤ᵣ _ _ _ 0≤u (<ᵣWeaken≤ᵣ _ _ u<b)) b<1
  (υ , L<υ) ← ∃ℚ₊LargerThanℝ₊ L
  let η₊ = η , ℚ.<→0< η (<ᵣ→<ℚ 0 η 0<η)
      δ = ℚ.min₊ η₊ (invℚ₊ υ  ℚ₊· ε)
  ∣ δ , (λ v v∈ u∼v →
      invEq (∼≃abs<ε _ _ _)
       let z = fst (∼≃abs<ε _ _ _) u∼v
           zz = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) (isTrans<≤ᵣ _ _ _ z
                 (≤ℚ→≤ᵣ _ _ (ℚ.min≤ η _))))
       in isTrans≤<ᵣ _ _ _  (≤L u v u∈ v∈ (<ᵣWeaken≤ᵣ _ _ u<b)
                       (<ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ _ _ _
                         (a-b<c⇒a<c+b _ _ _ zz)
                         (a<b-c⇒a+c<b _ _ _ η<b-u))))
           (isTrans<≡ᵣ _ _ _
             (<ᵣ₊Monotone·ᵣ _ _ _ _
               (0≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (snd L))
               (isTrans<≤ᵣ _ _ _
                 z
                 (≤ℚ→≤ᵣ _ _ (ℚ.min≤' η _))) L<υ)

                  ((·ᵣComm _ _ ∙ sym (rat·ᵣrat _ _) ∙
                 cong rat (ℚ.y·[x/y] υ _))))) ∣₁

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

 -- IsContinuousWPArcSin⟨⟩ : IsContinuousWithPred (ointervalℙ -1 1) arcSin⟨⟩
 -- IsContinuousWPArcSin⟨⟩ = {!!}

 opaque
  unfolding minᵣ maxᵣ
  arcSin⟨⟩[0]≡0 : arcSin⟨⟩ 0 (decℚ<ᵣ? { -1} {0} , decℚ<ᵣ? {0} {1}) ≡ 0
  arcSin⟨⟩[0]≡0 =
     cong₂ _+ᵣ_
       (cong -ᵣ_ (cong (uncurry arcSin)
        (Σ≡Prop (∈-isProp (pred≤< 0 1))
          {u = clampᵣ 0 1 (-ᵣ 0) , _}
          {rat [ pos 0 / 1 ] , ≤ᵣ-refl 0 , decℚ<ᵣ?}
          (cong (clampᵣ 0 1) (-ᵣ-rat 0)))
         ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , (decℚ<ᵣ? {0} {1})))
         ∙ -ᵣ-rat 0)
       (cong (uncurry arcSin)
        (Σ≡Prop (∈-isProp (pred≤< 0 1)) refl) ∙
    arcSin[0]≡0 (≤ᵣ-refl 0 , (decℚ<ᵣ? {0} {1})))
    ∙ +ᵣ-rat 0 0

 arcSin⟨⟩∘sin-ℚ : ∀ (Q : ℚ₊) → (Q<π/2 : rat (fst Q) <ᵣ π-number/2)
  → ∀ q → (0 ℚ.≤ q) ⊎ (q ℚ.≤ 0)
  →  (q∈ : rat q ∈ intervalℙ (-ᵣ (rat (fst Q))) (rat (fst Q)))
  → ∀ sinq∈
   → arcSin⟨⟩ (sin (rat q)) sinq∈

   ≡ (rat q)
 arcSin⟨⟩∘sin-ℚ Q Q<π/2 q (inl 0≤q') (_ , q<Q) sinq∈@(_ , sinq<1) =
  let 0≤q : 0 ≤ᵣ (rat q)
      0≤q = ≤ℚ→≤ᵣ _ _ 0≤q'
      q<π/2 : (rat q) <ᵣ π-number/2
      q<π/2 = isTrans≤<ᵣ _ _ _ q<Q Q<π/2
      0≤sinq : 0 ≤ᵣ sin (rat q)
      0≤sinq = fst $ x∈[0,π/2⟩→sin[x]∈[0,1⟩ (rat q)
          (0≤q , q<π/2)

  in 𝐑'.+IdL' _ _ (
       cong -ᵣ_
         (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (-ᵣ (sin (rat q)))
              decℚ≤ᵣ?
              (isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _  0≤sinq)
               (-ᵣ-rat 0)  )))
           ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
       ∙ -ᵣ-rat 0)
     ∙ cong (uncurry arcSin)
         ((Σ≡Prop (∈-isProp (pred≤< 0 1))
          (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ ( 0≤sinq , sin≤1 _)))))
          ∙ secArcSin _ (0≤sinq , sinq<1) (0≤q , q<π/2)
 arcSin⟨⟩∘sin-ℚ Q Q<π/2 q (inr q'≤0) (-Q<-q , _) sinq∈@(-1<sinq , _) =
  let 0≤-q : 0 ≤ᵣ -ᵣ rat q
      0≤-q = isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0))
              (-ᵣ≤ᵣ _ _ (≤ℚ→≤ᵣ _ _ q'≤0))

      sin-q<1 : sin (-ᵣ rat q) <ᵣ 1
      sin-q<1 = subst2 _<ᵣ_ (sin-odd (rat q)) (-ᵣ-rat -1)
          (-ᵣ<ᵣ _ _ -1<sinq)

      -q<π/2 : -ᵣ rat q <ᵣ π-number/2
      -q<π/2 = isTrans≤<ᵣ _ _ _ (-ᵣ≤ᵣ _ _ -Q<-q)
                (isTrans≡<ᵣ _ _ _ (-ᵣInvol _) Q<π/2)

      sinq≤0 : sin (rat q) ≤ᵣ 0
      sinq≤0 = ≤ᵣ-ᵣ _ _
        (subst2 _≤ᵣ_ (sym (-ᵣ-rat 0)) (sym (sin-odd (rat q)))
         (fst (x∈[0,π/2⟩→sin[x]∈[0,1⟩ (-ᵣ (rat q))
          (0≤-q , -q<π/2))))

  in 𝐑'.+IdR' _ _
      (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (sin (rat q))
              decℚ≤ᵣ? sinq≤0))
           ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
     ∙ cong -ᵣ_
       (cong (uncurry arcSin)
         (Σ≡Prop (∈-isProp (pred≤< 0 1)) {clampᵣ 0 1 (-ᵣ sin (rat q)) , _}
           (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _
             (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _ sinq≤0) ,
              (isTrans≤ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _
               (≤absᵣ _) (sym (-absᵣ _))) (∣sin∣≤1 (rat q))))) ∙ sin-odd _))
         ∙ secArcSin _ (subst2 _≤ᵣ_
           (-ᵣ-rat 0) (sin-odd _) (-ᵣ≤ᵣ _ _ sinq≤0) , sin-q<1)
           (0≤-q , -q<π/2))
     ∙ -ᵣInvol (rat q)



 ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ : ∀ x → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
       → sin x ∈ ointervalℙ -1 1
 ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ x x∈@(<x , x<) =
  isTrans≡<ᵣ _ _ _ ((sym (-ᵣ-rat 1) ∙ cong -ᵣ_ (sym (sin[π/2]≡1)))
   ∙ sin-odd π-number/2)
   (sin-strictMonotone (-ᵣ π-number/2) x
     (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ π-number/2₊ π-number/2₊)) (ointervalℙ⊆intervalℙ _ _ x x∈) <x) ,
   isTrans<≡ᵣ _ _ _
     (sin-strictMonotone x (π-number/2)
      (ointervalℙ⊆intervalℙ _ _ x x∈)
       (<ᵣWeaken≤ᵣ _ _ ((-ℝ₊<ℝ₊ π-number/2₊ π-number/2₊)) , ≤ᵣ-refl _) x<)
     sin[π/2]≡1

 sin∘arcSin⟨⟩ℚ :
      ∀ q q∈ → (0 ℚ.≤ q) ⊎ (q ℚ.≤ 0)
    → sin (arcSin⟨⟩ (rat q) q∈) ≡ (rat q)
 sin∘arcSin⟨⟩ℚ q (-1<q , q<1) (inl 0≤q') =
   let 0≤q = ≤ℚ→≤ᵣ 0 q 0≤q'

   in cong sin (𝐑'.+IdL' _ _
        (cong -ᵣ_
          (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (-ᵣ rat q)
              decℚ≤ᵣ?
              (isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _  0≤q)
               (-ᵣ-rat 0)  )))
           ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))  ∙
          -ᵣ-rat 0)
          ∙ cong (uncurry arcSin)
              (Σ≡Prop (∈-isProp (pred≤< 0 1))
                (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _
                 (0≤q , <ᵣWeaken≤ᵣ _ _ q<1)))))
         ∙ retArcSin _ (0≤q , q<1)
 sin∘arcSin⟨⟩ℚ q (-1<q , _) (inr q≤0') =
   let q≤0 = ≤ℚ→≤ᵣ q 0 q≤0'
       0≤-q : 0 ≤ᵣ -ᵣ rat q
       0≤-q = isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _ q≤0)
       -q<1 : -ᵣ rat q <ᵣ 1
       -q<1 = isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ -1<q)
                (-ᵣ-rat -1)
   in cong sin (𝐑'.+IdR' _ _ (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (rat q)
              decℚ≤ᵣ? q≤0))
              ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
      ∙ cong -ᵣ_ (cong (uncurry arcSin)
         (Σ≡Prop (∈-isProp (pred≤< 0 1))
           (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _ (0≤-q , (<ᵣWeaken≤ᵣ _ _ -q<1)))))))
     ∙ sym (sin-odd _)
     ∙ cong -ᵣ_ (retArcSin _ (0≤-q , -q<1))
     ∙ -ᵣInvol _




 opaque
  unfolding _+ᵣ_
  IsContinuousWPArcSin⟨⟩ : IsContinuousWithPred (ointervalℙ -1 1) arcSin⟨⟩
  IsContinuousWPArcSin⟨⟩ =
    contDiagNE₂WP sumR (ointervalℙ -1 1)
             (λ x x∈ → -ᵣ (arcSin (clampᵣ 0 1 (-ᵣ x))
             ((≤clampᵣ 0 1 (-ᵣ x) decℚ≤ᵣ?) ,
              isTrans≤<ᵣ _ (maxᵣ 0 (-ᵣ x)) _
                  (min≤ᵣ (maxᵣ 0 (-ᵣ x)) 1 )
                  (max<-lem 0 (-ᵣ x) 1 (decℚ<ᵣ? {0} {1})
                    ((isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (fst x∈))
                     (-ᵣ-rat -1)))))))
           (λ x x∈ →
             arcSin (clampᵣ 0 1 x)
              ((≤clampᵣ 0 1 x decℚ≤ᵣ?)
               , isTrans≤<ᵣ _ (maxᵣ 0 x) _
                  (min≤ᵣ (maxᵣ 0 x) 1 )
                  (max<-lem 0 x 1 (decℚ<ᵣ? {0} {1}) (snd x∈))))
            (IsContinuousWithPred-ᵣ (ointervalℙ -1 1)
              _
              (IsContinuousWP∘ (pred≤< 0 1) (ointervalℙ -1 1)
             _
             _ _
             IsContinuousWithPredArcSin
             (IsContinuousWP∘ (ointervalℙ -1 1) (ointervalℙ -1 1)
              _
              _
              (λ x (<x , x<) → (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 1))
                (-ᵣ<ᵣ _ _ x<)) ,
               (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ <x) (-ᵣ-rat -1)))
              (AsContinuousWithPred (ointervalℙ -1 1)
                _ (IsContinuousClamp 0 1))
              ((AsContinuousWithPred (ointervalℙ -1 1)
                _ IsContinuous-ᵣ)))))
            (IsContinuousWP∘ (pred≤< 0 1) (ointervalℙ -1 1)
             arcSin
             _ _
             IsContinuousWithPredArcSin
             (((AsContinuousWithPred (ointervalℙ -1 1)
              (clampᵣ 0 1 ) (IsContinuousClamp 0 1)))))


arcSin⟨⟩∘sin : ∀ x sinx∈
 → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
 → arcSin⟨⟩ (sin x) sinx∈ ≡ x
arcSin⟨⟩∘sin x sinx∈@(<negx , x<) x∈ =
  PT.rec (isSetℝ _ _)
    (λ (Q , ∣x∣<Q , Q<π/2) →
      let Q₊ = (Q , (ℚ.<→0< Q (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) ∣x∣<Q))))
          x∈Q : x ∈ intervalℙ (rat (ℚ.- Q)) (rat Q)
          x∈Q = isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat Q))
                 (-ᵣ≤ᵣ _ _
                  (isTrans≤ᵣ _ _ _ (≤absᵣ _)
                    (isTrans≡≤ᵣ _ _ _ (sym (-absᵣ _)) (<ᵣWeaken≤ᵣ _ _ ∣x∣<Q) ))))
                    (-ᵣInvol _ ) ,
                 isTrans≤ᵣ _ _ _ (≤absᵣ _)
                 (<ᵣWeaken≤ᵣ _ _ ∣x∣<Q )

          zzz = cong (uncurry arcSin⟨⟩)
                (Σ≡Prop (∈-isProp (ointervalℙ (-1) 1))
                  {u = _ , (<negx , x<)}
                  {v = _ , _}
                      (cong sin
                       ((∈ℚintervalℙ→clampᵣ≡ (rat ((ℚ.- Q))) (rat Q)
                 x x∈Q))))

      in zzz ∙∙
         ≡Continuous
           (λ x → arcSin⟨⟩ (sin (clampᵣ (rat (ℚ.- Q)) (rat Q) x))
                     (⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ _ (sym-intervalℙ⊆ointervalℙ _ _ Q<π/2
                      _ (
                        subst (λ -Q → clampᵣ (rat (ℚ.- Q)) (rat Q) x ∈
                          intervalℙ -Q (rat Q))
                          (sym (-ᵣ-rat Q))
                           ((clampᵣ∈ℚintervalℙ (rat (ℚ.- Q)) (rat Q)
                             (isTrans≡≤ᵣ _ _ _
                               (sym (-ᵣ-rat Q))
                               (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ Q₊) (ℚ₊→ℝ₊ Q₊)))) x))))))
           (λ x → clampᵣ (rat ((ℚ.- Q))) (rat Q) x)
           (IsContinuousWithPred∘IsContinuous
              (ointervalℙ -1 1)
               arcSin⟨⟩ _ _
               IsContinuousWPArcSin⟨⟩
                (IsContinuous∘ _ _
                  (isContinuousSin)
                  (IsContinuousClamp (rat ((ℚ.- Q))) (rat Q))))
           (IsContinuousClamp (rat ((ℚ.- Q))) (rat Q))

           (λ q →
            let z = sym (clampᵣ-rat (ℚ.- Q) Q q)
                q∈ = (subst-∈ (intervalℙ (-ᵣ rat Q) (rat Q))
                     ((cong clampᵣ (-ᵣ-rat Q) ≡$ rat Q ≡$ rat q) ∙ sym z)
                     (clampᵣ∈ℚintervalℙ _ (rat Q)
                       (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ Q₊) (ℚ₊→ℝ₊ Q₊))) (rat q)))
                sinq∈ : sin (rat (ℚ.clamp (ℚ.- Q) Q q)) ∈ ointervalℙ -1 1
                sinq∈ = ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ _
                  (sym-intervalℙ⊆ointervalℙ (rat Q) π-number/2
                    Q<π/2 (rat (ℚ.clamp (ℚ.- Q) Q q)) q∈)
            in cong (uncurry arcSin⟨⟩)
                (Σ≡Prop (∈-isProp (ointervalℙ (-1) 1))
                      (cong sin (sym z)))
                  ∙∙ arcSin⟨⟩∘sin-ℚ Q₊ Q<π/2
                   (ℚ.clamp (ℚ.- Q) Q q)
                    (ℚ.≤cases 0 (ℚ.clamp (ℚ.- Q) Q q)) q∈ sinq∈ ∙∙ z)
               x
         ∙∙ (sym (∈ℚintervalℙ→clampᵣ≡ (rat ((ℚ.- Q))) (rat Q)
                 x x∈Q)))
    (denseℚinℝ (absᵣ x) π-number/2  (
     ointerval→abs< x π-number/2 x∈))

sym-clamp-rat : ∀ q (Q : ℚ₊) →
                     clampᵣ (-ᵣ rat (fst Q)) (rat (fst Q)) (rat q) ≡
                    rat (ℚ.clamp (ℚ.- (fst Q)) (fst Q) q)
sym-clamp-rat q Q = (cong clampᵣ (-ᵣ-rat (fst Q))
  ≡$ (rat (fst Q)) ≡$ rat q) ∙ clampᵣ-rat (ℚ.- (fst Q)) (fst Q) q



sin∘arcSin⟨⟩ : ∀ x x∈ → sin (arcSin⟨⟩ x x∈) ≡ x
sin∘arcSin⟨⟩ x x∈ = fst (propTruncIdempotent≃ (isSetℝ _ _)) $ do
  let h = λ (x : ℝ) → substEquiv (λ X → x ∈
          ointervalℙ X (rat [ pos 1 / 1+ 0 ]))
         (sym (-ᵣ-rat 1))
  (q , ∣x∣<q , q<1) ← denseℚinℝ (absᵣ x) 1 (ointerval→abs< x 1
        (fst (h x) x∈))
  let q₊ : ℚ₊
      q₊ = q , ℚ.<→0< q (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) ∣x∣<q))
      p = ∈ℚintervalℙ→clampᵣ≡ (-ᵣ (rat q)) (rat q) x
            (abs≤→interval x (rat q) (<ᵣWeaken≤ᵣ _ _ ∣x∣<q))
      hh = clampᵣ∈ℚintervalℙ _ _
                (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ q₊) (ℚ₊→ℝ₊ q₊)))
  ∣ cong sin (cong (uncurry arcSin⟨⟩)
       (Σ≡Prop (∈-isProp (ointervalℙ _ _))
         p))
    ∙∙ ≡Continuous
        (λ x → sin (arcSin⟨⟩
          (clampᵣ (-ᵣ (rat q)) (rat q) x)
            (invEq (h _) (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _
               (hh x)))))
        (clampᵣ (-ᵣ (rat q)) (rat q))
        (IsContinuous∘ _ _ isContinuousSin
           (IsContinuousWithPred∘IsContinuous
             (ointervalℙ -1 1)
             _
             _
             (λ x → invEq (h _)
                (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _ _))
             IsContinuousWPArcSin⟨⟩
             (IsContinuousClamp (-ᵣ (rat q)) (rat q))))
        (IsContinuousClamp (-ᵣ (rat q)) (rat q))
         (λ y →
         let p' = sym (sym-clamp-rat y q₊)
         in cong sin (cong (uncurry arcSin⟨⟩)
              (Σ≡Prop (∈-isProp (ointervalℙ -1 1))
                (sym p'))) ∙
             sin∘arcSin⟨⟩ℚ
             (ℚ.clamp (ℚ.- q) q y)
             (invEq (h _) (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _
                  ((subst-∈ (intervalℙ (-ᵣ rat q) (rat q))
                     (sym-clamp-rat y q₊)
                    (hh (rat y)) ))))
              (ℚ.≤cases 0 (ℚ.clamp (ℚ.- q) q y))
                 ∙ p')
         x
    ∙∙ sym p ∣₁


sinIso⟨-π/2,π2⟩ : Iso (Σ _ (_∈ ointervalℙ (-ᵣ π-number/2) π-number/2))
                      (Σ _ (_∈ ointervalℙ -1 1))
sinIso⟨-π/2,π2⟩ .Iso.fun (x , x∈) = sin x , ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ x x∈
sinIso⟨-π/2,π2⟩ .Iso.inv (x , x∈) = arcSin⟨⟩ x x∈ , arcSin⟨⟩∈ x x∈
sinIso⟨-π/2,π2⟩ .Iso.rightInv (x , x∈) =
 Σ≡Prop (∈-isProp (ointervalℙ -1 1))
  (sin∘arcSin⟨⟩ _ _)
sinIso⟨-π/2,π2⟩ .Iso.leftInv (x , x∈) =
 Σ≡Prop (∈-isProp (ointervalℙ (-ᵣ π-number/2) π-number/2))
  (arcSin⟨⟩∘sin _ _ x∈)


equivSin⟨⟩ : (Σ _ (_∈ ointervalℙ (-ᵣ π-number/2) π-number/2))
             ≃ (Σ _ (_∈ ointervalℙ -1 1))
equivSin⟨⟩ = isoToEquiv sinIso⟨-π/2,π2⟩
