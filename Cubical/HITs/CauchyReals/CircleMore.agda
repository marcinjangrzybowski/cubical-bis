module Cubical.HITs.CauchyReals.CircleMore where

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
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_;_choose_)
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
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
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
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
open import Cubical.HITs.CauchyReals.Metric
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

cDistInj : ∀ x y → cDist x y ≡ 0 → x ≡ y
cDistInj = SQ.ElimProp2.go w
 where
 w : ElimProp2 (λ z z₁ → cDist z z₁ ≡ 0 → z ≡ z₁)
 w .ElimProp2.isPropB _ _ = isPropΠ λ _ → isSetCircle _ _
 w .ElimProp2.f a a' 1-cosΔ=0 =
   let w = cos=1⇒ (a -ᵣ a') (cong cos (·ᵣAssoc _ _ _)
            ∙ sym (𝐑'.equalByDifference _ _ 1-cosΔ=0))
    in eq/ a a' (map-snd
         (λ p → ℝ! ∙ p) w)


cDist≡ℝ²-dist : ∀ x y → 2 ·ᵣ cDist x y ≡
      (sinFromCircle x -ᵣ sinFromCircle y) ^ⁿ 2
   +ᵣ ((cosFromCircle x -ᵣ cosFromCircle y) ^ⁿ 2)
cDist≡ℝ²-dist = SQ.ElimProp2.go w
 where
 w : ElimProp2 _
 w .ElimProp2.isPropB _ _ = isSetℝ _ _
 w .ElimProp2.f x y =
     𝐑'.·DistR- _ _ _
   ∙ cong₂ _-ᵣ_
     (sym (x+x≡2x _)
      ∙ cong₂ _+ᵣ_ (sym (sin·sin+cos·cos=1 (x CRℝ.· (2 ·ᵣ π-number))))
                   (sym (sin·sin+cos·cos=1 (y CRℝ.· (2 ·ᵣ π-number)))))
     (cong (2 ·ᵣ_) (cong cos (sym (·ᵣAssoc _ _ _)
          ∙ 𝐑'.·DistL- _ _ _) ∙
           cosOfSum _ _ ∙ cong₂ _-ᵣ_
             (cong₂ _·ᵣ_ refl (sym (cos-even _)) )
             (cong₂ _·ᵣ_ refl (sym (sin-odd _))))
       ∙ sym (x+x≡2x _))
   ∙ ℝ!
   ∙ cong₂ _+ᵣ_
    (cong₂ _·ᵣ_ (sym (Rℝ.·IdL _)) refl)
    (cong₂ _·ᵣ_ (sym (Rℝ.·IdL _)) refl)

Circle→[cos,sin]-inj : ∀ x y →
                ((cosFromCircle x ≡ cosFromCircle y)
                × (sinFromCircle x ≡ sinFromCircle y))
                 → x ≡ y
Circle→[cos,sin]-inj x y (cosx≡cosy , sinx≡siny) =
  cDistInj x y (
       (sym (𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _)
        ∙ decℚ≡ᵣ?)) ∙ sym (·ᵣAssoc _ _ _))
    ∙∙ cong (rat [ 1 / 2 ] ·ᵣ_) (cDist≡ℝ²-dist x y ∙
   cong₂ _+ᵣ_
    (cong (_^ⁿ 2) (𝐑'.+InvR' _ _ sinx≡siny) ∙ 0^ⁿ 1)
    (cong (_^ⁿ 2) (𝐑'.+InvR' _ _ cosx≡cosy) ∙ 0^ⁿ 1)
   ∙ +ᵣ-rat 0 0) ∙∙ (sym (rat·ᵣrat _ _)
        ∙ decℚ≡ᵣ?))


isEquivCircle→distCircle : isEquiv Circle→distCircle
isEquivCircle→distCircle =
  isEmbedding×isSurjection→isEquiv
    (injEmbedding isSetDistCircle
      (λ {x} {y} p →
         Circle→[cos,sin]-inj x y
           (PathPΣ (cong fst p)))
    , Circle→[cos,sin]-surj)


Circle≃distCircle : Circle ≃ distCircle
Circle≃distCircle = Circle→distCircle , isEquivCircle→distCircle


module Stiching {ℓ} (A : Type ℓ) (a b : ℝ) (a<b : a <ᵣ b)
           (f : ∀ x → x <ᵣ b → A)
           (g : ∀ x → a <ᵣ x → A)
            where


 w₂ : (∀ x x< <x → f x x< ≡ g x <x) → ∀ x → 2-Constant (⊎.rec (f x) (g x))
 w₂ f=g x (inl u) (inl v)  = cong (f x) (isProp<ᵣ _ _ u v)
 w₂ f=g x (inl u) (inr v) = f=g x u v
 w₂ f=g x (inr u) (inl v) = sym (f=g x v u)
 w₂ f=g x (inr u) (inr v) = cong (g x) (isProp<ᵣ _ _ u v)

 module hLev2 (isSetA : isSet A) (f=g : ∀ x x< <x → f x x< ≡ g x <x) where
    preStichSetFns : ∀ x → ∥ (x <ᵣ b) ⊎ (a <ᵣ x) ∥₁  → A
    preStichSetFns x = PT.rec→Set isSetA
        (⊎.rec (f x) (g x))
        (w₂ f=g x)


    stichSetFns : ℝ → A
    stichSetFns x = preStichSetFns x (Dichotomyℝ' a x b a<b)

    stichSetFns-x< : ∀ x x<b → stichSetFns x ≡ f x x<b
    stichSetFns-x< x x<b =
       cong (preStichSetFns x) (squash₁ (Dichotomyℝ' a x b a<b)
         ∣ inl x<b ∣₁)

    stichSetFns-<x : ∀ x a<x → stichSetFns x ≡ g x a<x
    stichSetFns-<x x a<x =
       cong (preStichSetFns x) (squash₁ (Dichotomyℝ' a x b a<b)
         ∣ inr a<x ∣₁)

CircleOverlap→Circle-inj : ∀ ε → ∀ x y →
   CircleOverlap[ ε ]→Circle x ≡  CircleOverlap[ ε ]→Circle y
   → x ≡ y
CircleOverlap→Circle-inj ε = SQ.ElimProp2.go w
 where
 w : ElimProp2
      (λ z z₁ →
         CircleOverlap[ ε ]→Circle z ≡ CircleOverlap[ ε ]→Circle z₁ →
         z ≡ z₁)
 w .ElimProp2.isPropB _ _ = isPropΠ λ _ → squash/ _ _
 w .ElimProp2.f x y x₁ = eq/ _ _
   (SQ.effective isPropCircle-rel isEquivRelCircleRel _ _ x₁)

opaque
 CircleOverlap→[cos,sin]-surj : ∀ ε → isSurjection
   (Circle→distCircle ∘ CircleOverlap[ ε ]→Circle)
 CircleOverlap→[cos,sin]-surj ε ((x , y) , x²+y²≡1) =
   PT.map (λ (φ , φ∈ , cosφ≡x , sinφ≡y) →
     [ (φ ／ᵣ₊ (2 ₊·ᵣ π-number₊) +ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ 2))) ,
       subst2 _<ᵣ_
         (cong₂ _+ᵣ_ (-ᵣ· _ _ ∙ cong -ᵣ_
          (·ᵣComm _ _ ∙ [x/₊y]·yᵣ _ _))
           refl ∙ 𝐑'.+InvL' _ _ refl)
         (cong₂ _+ᵣ_ (cong₂ _·ᵣ_ refl (cong fst (sym (invℝ₊· _ _)))) refl
           )
         (<ᵣ-+o _ _ (fst (invℝ₊ (ℚ₊→ℝ₊ 2)))
           (<ᵣ-·ᵣo _ _ (invℝ₊ 2 ₊·ᵣ invℝ₊ π-number₊) (fst φ∈)))
      , isTrans<≡ᵣ _ _ _
         (<ᵣ-+o _ _ (fst (invℝ₊ (ℚ₊→ℝ₊ 2)))
           (<ᵣ-·ᵣo _ _ (invℝ₊ (2 ₊·ᵣ π-number₊)) (snd φ∈)))
           (cong₂ _+ᵣ_ (·DistR+ _ _ _ ∙ +ᵣComm _ _) refl  ∙
            sym (+ᵣAssoc _ _ _)
             ∙
             cong₂ _+ᵣ_ ([x·yᵣ]/₊y _ _)
              (cong₂ _+ᵣ_ (·ᵣComm _ _ ∙
                cong₂ _·ᵣ_ (cong fst (invℝ₊· 2 π-number₊)) refl
                ∙ [x/₊y]·yᵣ _ _ ∙ invℝ₊-rat 2) (invℝ₊-rat 2)
                ∙ +ᵣ-rat _ _ ∙ decℚ≡ᵣ?)
             ∙ +ᵣComm _ _)
           ]/
     ,
       Σ≡Prop (λ _ → isSetℝ _ _)
       (cong₂ _,_

        ((cong cos (·DistR+ _ _ _ ∙
          cong₂ _+ᵣ_ ([x/₊y]·yᵣ _ _) (cong₂ _·ᵣ_ refl (·ᵣComm _ _)
            ∙ ·ᵣComm _ _ ∙ [x·yᵣ]/₊y _ _)) ∙ cos[x]=-cos[x+π] _)
         ∙ cong -ᵣ_ cosφ≡x ∙ -ᵣInvol _)
        ((cong sin (·DistR+ _ _ _ ∙
          cong₂ _+ᵣ_ ([x/₊y]·yᵣ _ _) (cong₂ _·ᵣ_ refl (·ᵣComm _ _)
            ∙ ·ᵣComm _ _ ∙ [x·yᵣ]/₊y _ _)) ∙ sin[x]=-sin[x+π] _)
         ∙ cong -ᵣ_ sinφ≡y ∙ -ᵣInvol _)
        ))
     (distCircle→angle (ε ₊·ᵣ (2 ₊·ᵣ π-number₊)) (-ᵣ x) (-ᵣ y)
     (cong₂ _+ᵣ_ (sym (^ⁿ-even 1 x)) (sym (^ⁿ-even 1 y))  ∙
       cong₂ _+ᵣ_ (x^²=x·x _) (x^²=x·x _) ∙ x²+y²≡1))

 isEquiv[Circle→distCircle∘CircleOverlap[ε]→Circle] : ∀ ε
     → isEquiv (Circle→distCircle ∘ CircleOverlap[ ε ]→Circle)
 isEquiv[Circle→distCircle∘CircleOverlap[ε]→Circle] ε =
   isEmbedding×isSurjection→isEquiv
   (snd (compEmbedding (Circle→distCircle , injEmbedding isSetDistCircle
      (λ {x} {y} p →
         Circle→[cos,sin]-inj x y
           (PathPΣ (cong fst p))))
           (_ , injEmbedding squash/
            (CircleOverlap→Circle-inj ε _ _)))
     , CircleOverlap→[cos,sin]-surj ε)


CircleOverlap≃distCircle : ∀ ε → CircleOverlap[ ε ] ≃ distCircle
CircleOverlap≃distCircle ε = Circle→distCircle ∘ CircleOverlap[ ε ]→Circle
  , isEquiv[Circle→distCircle∘CircleOverlap[ε]→Circle] ε


fromWeldedInterval : ∀ {ℓ} (A : Type ℓ) → Type ℓ
fromWeldedInterval A =
 Σ (∀ x → x ∈ intervalℙ 0 1 → A)
   λ f → f 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ f 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)

circle0 : distCircle
circle0  = (1 , 0) ,
  cong₂ _+ᵣ_ (sym (rat·ᵣrat _ _)) (sym (rat·ᵣrat _ _))
                                    ∙ +ᵣ-rat _ _


opaque

 injCircle0≡circle0 : Circle→distCircle (injCircle 0) ≡ circle0
 injCircle0≡circle0 = distCircle≡
   (cong cos (𝐑'.0LeftAnnihilates _) ∙ cos0=1)
   (cong sin (𝐑'.0LeftAnnihilates _) ∙ sin0=0)

 circle+ : distCircle → distCircle → distCircle
 circle+ ((a , b) , p) ((c , d) , q) =
   ((a ·ᵣ c -ᵣ b ·ᵣ d) , a ·ᵣ d +ᵣ b ·ᵣ c) ,
     ℝ!
       ∙ cong₂ _·ᵣ_
       (p)
       (q) ∙ sym (rat·ᵣrat 1 1)

 circle+-X : ∀ x y →
  fst (fst (circle+ x y))
   ≡ (x .fst .fst ·ᵣ y .fst .fst -ᵣ x .fst .snd ·ᵣ y .fst .snd)
 circle+-X x y = refl

 circle+-Y : ∀ x y →
  snd (fst (circle+ x y))
   ≡ (x .fst .fst ·ᵣ y .fst .snd +ᵣ x .fst .snd ·ᵣ y .fst .fst)
 circle+-Y x y = refl

 circleNeg : distCircle → distCircle
 circleNeg ((x , y) , p) =
  (x , -ᵣ y) , cong₂ _+ᵣ_ refl (-ᵣ·-ᵣ _ _) ∙ p

ℝS¹AbGroupStr : AbGroupStr distCircle
ℝS¹AbGroupStr .AbGroupStr.0g = circle0
ℝS¹AbGroupStr .AbGroupStr._+_  = circle+
ℝS¹AbGroupStr .AbGroupStr.-_  = circleNeg
ℝS¹AbGroupStr .AbGroupStr.isAbGroup = IsAbGroupℝS¹
  where
  opaque
   unfolding circle+ circleNeg
   IsAbGroupℝS¹ : IsAbGroup
     circle0
     circle+
     circleNeg
   IsAbGroupℝS¹ =
      makeIsAbGroup isSetDistCircle
      (λ _ _ _ → distCircle≡ ℝ! ℝ!)
      (λ _ → distCircle≡ (cong₂ _+ᵣ_ (·IdR _) (cong -ᵣ_ (𝐑'.0RightAnnihilates _))
          ∙ 𝐑'.+IdR' _ _ (-ᵣ-rat 0))
        (cong₂ _+ᵣ_ (𝐑'.0RightAnnihilates _ ) (·IdR _)
          ∙ +IdL _))
      (λ (_ , p) → distCircle≡ (ℝ! ∙ p) ℝ!)
      λ _ _ → distCircle≡ ℝ! ℝ!


ℝS¹AbGroup : AbGroup ℓ-zero
ℝS¹AbGroup = _ , ℝS¹AbGroupStr


interpℝ0 : ∀ a b → interpℝ a b 0 ≡ a
interpℝ0 a b = ℝ!

interpℝ1 : ∀ a b → interpℝ a b 1 ≡ b
interpℝ1 a b = cong₂ _+ᵣ_ refl (Rℝ.·IdL _) ∙ ℝ!

pathFromToCircle∃ : (x₀ x₁ : Circle) →
              ∃[ p ∈ (∀ x → x ∈ intervalℙ 0 1 → Circle) ]
                (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₀)
                 × (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₁)
pathFromToCircle∃ = SQ.ElimProp2.go w
 where
 w : ElimProp2 _
 w .ElimProp2.isPropB _ _ = squash₁
 w .ElimProp2.f x y = ∣ (λ t _ → injCircle (interpℝ x y t)) ,
   cong injCircle (interpℝ0 x y) , cong injCircle (interpℝ1 x y) ∣₁


module ℝS¹ where
 open AbGroupStr ℝS¹AbGroupStr public
 open GroupTheory (AbGroup→Group ℝS¹AbGroup) public


rotationIso : distCircle → Iso distCircle distCircle
rotationIso x .Iso.fun = ℝS¹._+ x
rotationIso x .Iso.inv = ℝS¹._- x
rotationIso x .Iso.sec a =
  sym (ℝS¹.+Assoc _ _ _) ∙ cong (a ℝS¹.+_) (ℝS¹.+InvL _) ∙ ℝS¹.+IdR _
rotationIso x .Iso.ret a =
  sym (ℝS¹.+Assoc _ _ _) ∙ cong (a ℝS¹.+_) (ℝS¹.+InvR _) ∙ ℝS¹.+IdR _

rotationEquiv : distCircle → distCircle ≃ distCircle
rotationEquiv x = isoToEquiv (rotationIso x)

opaque
 unfolding circle+ circleNeg
 rotationEquivPresDist : ∀ x y z →
    cartDist² (fst x) (fst y) ≡ cartDist² (fst (x ℝS¹.+ z)) (fst (y ℝS¹.+ z))
 rotationEquivPresDist x y z =
    sym (𝐑'.·IdR' _ _ (snd z)) ∙ ℝ!


fromInterval→ℝ-uC : Type
fromInterval→ℝ-uC = Σ _ (IsUContinuousℙ (intervalℙ 0 1))


rotateToOrigin : ∀ D (x : distCircle) → Iso
       (Σ distCircle λ x' → cartDist² (fst x) (fst x') <ᵣ D)
       (Σ distCircle λ x' → cartDist² (fst circle0) (fst x') <ᵣ D)
rotateToOrigin D x@((X , Y) , _) = w
 where


 w : Iso (Σ distCircle (λ x' → cartDist² (fst x) (fst x') <ᵣ D))
         (Σ distCircle (λ x' → cartDist² (fst circle0) (fst x') <ᵣ D))
 w .Iso.fun (p@((X' , Y') , _) , d) = p ℝS¹.- x ,
  isTrans≡<ᵣ _ _ _ (cong₂ cartDist² (cong fst (sym (ℝS¹.+InvR x)) ) refl
    ∙ sym (rotationEquivPresDist x p (ℝS¹.- x))) d

 w .Iso.inv (p@((X' , Y') , _) , d) = p ℝS¹.+ x ,
   isTrans≡<ᵣ _ _ _ ((cong₂ cartDist² (cong fst (sym (ℝS¹.+IdL _)) ) refl
    ∙ sym (rotationEquivPresDist circle0 p x))) d
 w .Iso.sec _ = Σ≡Prop (λ _ → isProp<ᵣ _ _)
                 (sym (ℝS¹.+Assoc _ x (ℝS¹.- x))
                   ∙ cong (_ ℝS¹.+_) (ℝS¹.+InvR _) ∙ ℝS¹.+IdR _)
 w .Iso.ret _ = Σ≡Prop (λ _ → isProp<ᵣ _ _)
                 (sym (ℝS¹.+Assoc _ (ℝS¹.- x) x)
                   ∙ cong (_ ℝS¹.+_) (ℝS¹.+InvL _) ∙ ℝS¹.+IdR _)


openHalfCircleIso : Iso
                     (Σ _ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))
                     (Σ distCircle λ ((x , _) , _) → 0 <ᵣ x)
openHalfCircleIso = w
 where
 f : ∀ x →  x ∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ]) →
      rat [ pos 0 / 1+ 0 ] <ᵣ
      cos
       (x ·ᵣ (rat [ pos 2 , (1+ 0) ]/ ·ᵣ
        (rat [ pos 2 , (1+ 0) ]/ ·ᵣ π-number/2)))
 f x x∈ = ∣x∣<π/2→0<cos[x] _
    (subst2 (λ a b →
      x ·ᵣ a
      ∈ ointervalℙ (-ᵣ b) b )
      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _) )
      ( (·ᵣAssoc _ _ _) ∙ 𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
      (scale-sym-ointervalℙ (rat [ 1 / 4  ]) (4 ₊·ᵣ π-number/2₊) x x∈))

 inv∈ : ∀ x y → cartNorm² (x , y) ≡ rat [ pos 1 / 1+ 0 ]
       → 0 <ᵣ x → ∀ y∈ →  arcSin⟨⟩ y y∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4)) ∈
      ointervalℙ (-ᵣ rat [ 1 / 4 ]) (rat [ 1 / 4 ])
 inv∈ x y p 0<y y∈ =
   subst {x = fst π-number/2₊ ·ᵣ
                 fst
                 (invℝ₊
                  ((π-number/2 , π-number/2₊ .snd) ₊·ᵣ
                   (rat (4 .fst) , ℚ₊→ℝ₊ 4 .snd)))}
      {y = fst (ℚ₊→ℝ₊ (invℚ₊ 4))}
      (λ b →
      arcSin⟨⟩ y y∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4))
      ∈ ointervalℙ (-ᵣ b) b )
        (cong₂ _·ᵣ_ refl (·invℝ₊ _ _)
        ∙ ·ᵣAssoc _ _ _ ∙
         cong₂ _·ᵣ_ (x·invℝ₊[x] π-number/2₊ ) (invℝ₊-rat 4) ∙ Rℝ.·IdL _)
         (scale-sym-ointervalℙ (fst π-number/2₊) (invℝ₊ (π-number/2₊ ₊·ᵣ 4 ))
         (arcSin⟨⟩ y y∈) (arcSin⟨⟩∈ y y∈))

 w : Iso _ _
 w .Iso.fun (t , t∈) = Circle→distCircle (injCircle t) , f t t∈
 w .Iso.inv (((x , y) , p) , 0<x) =
  arcSin⟨⟩ y y∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4)) ,
    inv∈ x y p 0<x y∈
  where
   y∈ : y ∈ ointervalℙ -1 1
   y∈ = subst (λ b → y ∈ ointervalℙ b 1)
     (-ᵣ-rat 1)
      (abs<→ointerval y 1
        (x²<1→∣x∣<1 _ (isTrans<≡ᵣ _ _ _
          (isTrans≡<ᵣ _ _ _
            (x^²=x·x y ∙ sym (+IdR _))
            (<ᵣ-o+ _ _ (y ·ᵣ y) (snd ((x , 0<x) ₊·ᵣ (x , 0<x))))
            )
          (+ᵣComm _ _ ∙ p))))


 w .Iso.sec (((x , y) , p) , 0<x) = Σ≡Prop (λ _ → isProp<ᵣ _ _)
   (distCircle≡ (
      cong fst (invEq (congEquiv {x = _ , f _ (inv∈ x y p 0<x _)}
       {_ , 0<x} (_ , isEquiv-₊^ⁿ 2))
       (ℝ₊≡ $ (x^²=x·x _ ∙
         cos·cos=1-sin·sin φ) ∙∙  cong (_-ᵣ_ 1)
        (cong₂ _·ᵣ_ p-sin p-sin)

        ∙ sym (cong (_-ᵣ (y ·ᵣ y))
         ( (p))) ∙  (𝐑'.plusMinus _ _)
         ∙∙ sym (x^²=x·x x) ))) p-sin)
  where
   φ = _
   p-sin : sin φ ≡ _
   p-sin = (cong sin (cong₂ _·ᵣ_ refl (
     (·ᵣAssoc _ _ _ ∙ cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _)) refl)
    ∙ ·ᵣComm _ _ )
     ∙ [x/₊y]·yᵣ _ (π-number/2₊ ₊·ᵣ 4)) ∙
           sin∘arcSin⟨⟩ _ _)
 w .Iso.ret (t , t∈) =
  Σ≡Prop
      (∈-isProp (ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))

       (cong₂ _·ᵣ_ (arcSin⟨⟩∘sin _ _
        ((subst2 (λ a b →
      t ·ᵣ a
      ∈ ointervalℙ (-ᵣ b) b )
      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _) )
      ( (·ᵣAssoc _ _ _) ∙ 𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
      (scale-sym-ointervalℙ (rat [ 1 / 4  ]) (4 ₊·ᵣ π-number/2₊) t t∈))))
        (cong (fst ∘ invℝ₊) (ℝ₊≡ {y = 2 ₊·ᵣ (2 ₊·ᵣ π-number/2₊)}
         (·ᵣComm _ _
         ∙ cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _))))
         ∙ [x·yᵣ]/₊y _ _)


isEquivInjCircleRestr : isEquiv
 {A = (Σ _ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))}
 {B = Σ (ℝ / circle-rel) λ x → 0 <ᵣ (
                          fst (fst (equivFun Circle≃distCircle x)))}
  (λ (x , x∈) → injCircle x , _)
isEquivInjCircleRestr =
  isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ (x , x∈) → injCircle x , _)
    (Σ-cong-equiv-fst Circle≃distCircle)
     (isoToIsEquiv openHalfCircleIso)


distCircleMetricSpaceStr : MetricSpaceStr distCircle
distCircleMetricSpaceStr =
 MetricSubSpaceStr (ℝ × ℝ)
  (λ z → (cartNorm² z ≡ 1) , isSetℝ _ _)
  𝐑²MetricSpaceStr

distCircleMetricSpace : MetricSpace₀
distCircleMetricSpace = _ , distCircleMetricSpaceStr


[x-y][x-y]≡xx-2xy+yy : ∀ x y →
  (x -ᵣ y) ·ᵣ (x -ᵣ y) ≡
    x ·ᵣ x +ᵣ (-ᵣ (2 ·ᵣ (x ·ᵣ y) )) +ᵣ y ·ᵣ y
[x-y][x-y]≡xx-2xy+yy x y =
  ℝ! ∙ cong₂ _+ᵣ_
   (cong₂ _-ᵣ_  refl (x+x≡2x _) )
    refl
opaque

 cartDist≃upperHalf :  (p : distCircle) →
    (cartDist² (fst circle0) (fst p) <ᵣ 2)
     ≃ (0 <ᵣ fst (fst p))
 cartDist≃upperHalf ((x , y) , p) =
        subst2Equiv _<ᵣ_
          ( (cong cartNorm²
             (cong₂ _,_
               refl
               (+IdL _))
           ∙ (cong₂ _+ᵣ_
              ([x-y][x-y]≡xx-2xy+yy 1 x)
              (-ᵣ·-ᵣ y y)
           ∙ sym (+ᵣAssoc _ _ _))
           ∙ sym (+ᵣAssoc _ _ _)
           ∙ cong₂ _+ᵣ_ refl (+ᵣComm _ _)
           ∙ +ᵣAssoc _ _ _ )
           ∙ cong₂ (_-ᵣ_)
              ( cong₂ (_+ᵣ_) (·IdR _) p ∙  (+ᵣ-rat 1 1)  )
               (cong (2 ·ᵣ_) (Rℝ.·IdL x)))
          (sym (-ᵣ-rat₂ _ _) ∙
            cong₂ _-ᵣ_ refl (rat·ᵣrat _ _))
     ∙ₑ x+y<x+z≃y<z 2 _ _
     ∙ₑ invEquiv (x<y≃-y<-x _ _)
     ∙ₑ invEquiv (z<x≃y₊·z<y₊·x x 0 2)

unwindDistCirclePathStep : ∀ a b a≤b →
   (f : Interval[ a , b ]MetricSpace .fst → distCircle)
 → (∀ x → cartDist² (fst (f (a , (≤ᵣ-refl a , a≤b)))) (fst (f x) ) <ᵣ 2)
 → Σ ((fst (Interval[ a , b ]MetricSpace)) → ℝ)
   λ g → ∀ x → f x ≡ f (a , (≤ᵣ-refl a , a≤b)) ℝS¹.+
     Circle→distCircle (injCircle (g x))
unwindDistCirclePathStep a b a≤b f fDist =
  g , g-eq

 where

 g : fst Interval[ a , b ]MetricSpace → ℝ
 g x =
  let yyy = Iso.fun (rotateToOrigin 2 ((f (a , ≤ᵣ-refl a , a≤b)))) (f x , fDist x)
      yy = fst (cartDist≃upperHalf (fst yyy)) (snd yyy)
  in fst (invEq (_ , isEquivInjCircleRestr)
   (invEq Circle≃distCircle ((f x) ℝS¹.+ (ℝS¹.- f (a , ≤ᵣ-refl a , a≤b)))
    , isTrans<≡ᵣ _ _ _ yy
       (cong
         {x = (fst
        (Iso.fun (rotateToOrigin 2 (f (a , ≤ᵣ-refl a , a≤b)))
         (f x , fDist x)))}
         {y = (equivFun Circle≃distCircle
            (invEq Circle≃distCircle
             (f x ℝS¹.+ ℝS¹.- f (a , ≤ᵣ-refl a , a≤b))))}
         (fst ∘ fst)
         (sym (secEq Circle≃distCircle
              (f x ℝS¹.+ ℝS¹.- f (a , ≤ᵣ-refl a , a≤b)))))))

 g-eq : (x : Interval[ a , b ]MetricSpace .fst) →
         f x ≡
         f (a , ≤ᵣ-refl a , a≤b) ℝS¹.+ Circle→distCircle (injCircle (g x))
 g-eq x =
    ((  sym (ℝS¹.+IdR _)
      ∙ cong ((f x) ℝS¹.+_) (sym (ℝS¹.+InvL _))
      ∙ (ℝS¹.+Assoc _ (ℝS¹.- (f (a , ≤ᵣ-refl a , a≤b))) _ ))
     ∙ cong (ℝS¹._+ (f (a , ≤ᵣ-refl a , a≤b)))
        (sym (fst (equivAdjointEquiv Circle≃distCircle)
         ( cong fst (secEq (_ , isEquivInjCircleRestr)
          (invEq Circle≃distCircle ((f x) ℝS¹.+ (ℝS¹.- f (a , ≤ᵣ-refl a , a≤b))) ,
            _  ))
            ))) )
      ∙ ℝS¹.+Comm _ _


unwindDistCirclePathStep' : ∀ a b a≤b →
   (f : Interval[ a , b ]MetricSpace .fst → distCircle)
 → (∀ x → cartDist² (fst (f (a , (≤ᵣ-refl a , a≤b)))) (fst (f x) ) <ᵣ 2)
 → Σ ((fst (Interval[ a , b ]MetricSpace)) → ℝ)
   λ g → ((∀ x → f x ≡ f (a , (≤ᵣ-refl a , a≤b)) ℝS¹.+
     Circle→distCircle (injCircle (g x))) × (g (a , (≤ᵣ-refl a , a≤b)) ≡ 0))
unwindDistCirclePathStep' a b a≤b f fDist =
  let (g , g=) = unwindDistCirclePathStep a b a≤b f fDist
      ga= = g= (a , (≤ᵣ-refl a , a≤b))
      ga=' : injCircle 0 ≡ (injCircle
       (unwindDistCirclePathStep a b a≤b f fDist .fst
        (a , ≤ᵣ-refl a , a≤b)))
      ga=' = invEq (congEquiv (Circle≃distCircle))
        ( distCircle≡ (cong cos (𝐑'.0LeftAnnihilates _) ∙ cos0=1)
          (cong sin (𝐑'.0LeftAnnihilates _) ∙ sin0=0)
          ∙ sym (1gUniqueR _ (sym (ga=))))

      ga='' = fromCircle≡ _ _ (sym ga=')

  in (λ (x , x∈) → g (x , x∈) -ᵣ g (a , (≤ᵣ-refl a , a≤b)))
    ,  (λ (x , x∈) → g= (x , x∈) ∙
      cong (f (a , ≤ᵣ-refl a , a≤b) ℝS¹.+_)
        (cong {x = injCircle (g (x , x∈))}
              {y = (injCircle (g (x , x∈) -ᵣ g (a , ≤ᵣ-refl a , a≤b)))}
           Circle→distCircle
          (eq/ _ _  (_ , (ℝ! ∙ snd ga'')))))
    , +-ᵣ _

 where
  open GroupTheory (AbGroup→Group ℝS¹AbGroup)



DiscreteMetricStr : ∀ {ℓ} {A : Type ℓ} → Discrete A → MetricSpaceStr A
DiscreteMetricStr _≟_ = ww
 where

 module _ (x y : _) where
  discDist : Dec (x ≡ y) → ℝ
  discDist (yes p) = 0
  discDist (no ¬p) = 1

  discDistNonNeg : ∀ d → 0 ≤ᵣ discDist d
  discDistNonNeg (yes p) = decℚ≤ᵣ?
  discDistNonNeg (no ¬p) = decℚ≤ᵣ?

  discDist0→ : ∀ d → 0 ≡ discDist d → x ≡ y
  discDist0→ (yes p) x = p
  discDist0→ (no ¬p) x = ⊥.rec (ℤ.0≢1-ℤ (ℚ.eq/⁻¹ _ _ (inj-rat _ _ x)))

 discDistSym : ∀ x y d d' → discDist x y d ≡ discDist y x d'
 discDistSym x y (yes p) (yes p₁) = refl
 discDistSym x y (yes p) (no ¬p) = ⊥.rec (¬p (sym p))
 discDistSym x y (no ¬p) (yes p) = ⊥.rec (¬p (sym p))
 discDistSym x y (no ¬p) (no ¬p₁) = refl

 discDistTriangle : ∀ x y z d d' d'' →
      discDist x z d ≤ᵣ
      discDist x y d' +ᵣ discDist y z d''
 discDistTriangle x y z (yes p) d' d'' =
   snd ((_ , discDistNonNeg x y d') ₀₊+₀₊ᵣ (_ , discDistNonNeg y z d''))
 discDistTriangle x y z (no ¬p) (yes p) (yes p₁) = ⊥.rec (¬p (p ∙ p₁))
 discDistTriangle x y z (no ¬p) (yes p) (no ¬p₁) =
   ≡ᵣWeaken≤ᵣ _ _ (sym (+IdL _))
 discDistTriangle x y z (no ¬p) (no ¬p₁) d'' =
  isTrans≡≤ᵣ _ _ _ (sym (+IdR _)) (≤ᵣ-o+ _ _ 1 (discDistNonNeg y z d''))
 open IsMetric

 w : IsMetric _ (λ x y → discDist _ _ (x ≟ y))
 w .is-set = Discrete→isSet _≟_
 w .𝑑-nonNeg x y = discDistNonNeg x y (x ≟ y)
 w .𝑑-sym x y = discDistSym x y (x ≟ y) (y ≟ x)
 w .𝑑-pos x y 0<d x=y =
   isIrrefl<ᵣ 0
     (isTrans<≡ᵣ _ _ _ 0<d (cong (discDist x y)
      (isPropDec (Discrete→isSet _≟_ x y) (x ≟ y) (yes x=y))))


 w .𝑑-zero→≡ x y = discDist0→ x y (x ≟ y)
 w .𝑑-≡→zero x y x=y = cong (discDist x y)
      (isPropDec (Discrete→isSet _≟_ x y) (yes x=y) (x ≟ y))
 w .𝑑-triangle x y z = discDistTriangle x y z
   (x ≟ z) (x ≟ y) (y ≟ z)

 ww : MetricSpaceStr _
 ww .MetricSpaceStr.𝑑[_,_] x y = discDist _ _ (x ≟ y)
 ww .MetricSpaceStr.isMetric = w

trivialMetricSpace : MetricSpace₀
trivialMetricSpace = _ , DiscreteMetricStr {A = Unit} λ _ _ → yes refl

isUContFromTrivialMetricSpace : ∀ {ℓ} (A : MetricSpace ℓ)
  (f : ⟨ trivialMetricSpace ⟩ → ⟨ A ⟩ )
  → IsUContMap (snd (trivialMetricSpace)) f (snd A)
isUContFromTrivialMetricSpace A f ε =
  1 , λ _ _ _ → isTrans≡<ᵣ _ _ _ (sym (MA.𝑑-≡→zero _ _ refl)) (snd (ℚ₊→ℝ₊ ε))


 where
  module MA = MetricSpaceStr (snd A)
