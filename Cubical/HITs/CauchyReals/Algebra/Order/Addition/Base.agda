module Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core

opaque
 unfolding _+ᵣ_ minᵣ maxᵣ

 +IdL : ∀ x → 0 +ᵣ x ≡ x
 +IdL = ≡Continuous _ _ (IsContinuous+ᵣL 0) IsContinuousId
   (λ r → +ᵣ-rat 0 r ∙ cong rat (ℚ.+IdL r))

 +IdR : ∀ x → x +ᵣ 0 ≡ x
 +IdR = ≡Continuous _ _ (IsContinuous+ᵣR 0) IsContinuousId
   (λ r → +ᵣ-rat r 0 ∙ cong rat (ℚ.+IdR r))

 +ᵣMaxDistr : ∀ x y z → maxᵣ x y +ᵣ z ≡ maxᵣ (x +ᵣ z) (y +ᵣ z)
 +ᵣMaxDistr x y z =
   ≡Continuous _ _
      (IsContinuous∘ _ _ (IsContinuous+ᵣR z) (IsContinuousMaxR y))
      (IsContinuous∘ _ _ (IsContinuousMaxR (y +ᵣ z))
        (IsContinuous+ᵣR z))
      (λ x' →
        ≡Continuous _ _
          (IsContinuous∘ _ _ (IsContinuous+ᵣR z)
            (IsContinuousMaxL (rat x')))
          (IsContinuous∘ _ _ (IsContinuousMaxL (rat x' +ᵣ z))
            (IsContinuous+ᵣR z))
          (λ y' →
            ≡Continuous _ _
              (IsContinuous+ᵣL (maxᵣ (rat x') (rat y')))
              (cont₂maxᵣ _ _
                (IsContinuous+ᵣL (rat x'))
                (IsContinuous+ᵣL (rat y')))
              (λ z' →
                cong (_+ᵣ rat z') (maxᵣ-rat x' y')
                ∙ +ᵣ-rat _ _
                ∙ cong rat (ℚ.+MaxDistrℚ x' y' z')
                ∙ sym (maxᵣ-rat _ _)
                ∙ cong₂ maxᵣ
                    (sym (+ᵣ-rat x' z'))
                    (sym (+ᵣ-rat y' z')))
              z)
          y)
      x


opaque
 unfolding _≤ᵣ_

 ≤ᵣ-+o : ∀ m n o → m ≤ᵣ n → m +ᵣ o ≤ᵣ n +ᵣ o
 ≤ᵣ-+o m n o p = sym (+ᵣMaxDistr m n o) ∙ cong (_+ᵣ o) p


≤ᵣ-o+ : ∀ m n o → m ≤ᵣ n → o +ᵣ m ≤ᵣ o +ᵣ n
≤ᵣ-o+ m n o =
  subst2 _≤ᵣ_ (+ᵣComm _ _) (+ᵣComm _ _) ∘ ≤ᵣ-+o m n o


≤ᵣMonotone+ᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s
  → m +ᵣ o ≤ᵣ n +ᵣ s
≤ᵣMonotone+ᵣ m n o s m≤n o≤s =
  isTrans≤ᵣ _ _ _ (≤ᵣ-+o m n o m≤n) (≤ᵣ-o+ o s n o≤s)


-ᵣ≤ᵣ : ∀ x y → x ≤ᵣ y → -ᵣ y ≤ᵣ -ᵣ x
-ᵣ≤ᵣ x y p =
  subst2 _≤ᵣ_
    (+ᵣAssoc _ _ _ ∙ cong (_+ᵣ (-ᵣ y)) (+-ᵣ x) ∙ +IdL _)
    (cong (y +ᵣ_) (+ᵣComm _ _)
      ∙∙ +ᵣAssoc _ _ _
      ∙∙ cong (_+ᵣ (-ᵣ x)) (+-ᵣ y) ∙ +IdL _)
    (≤ᵣ-+o _ _ ((-ᵣ x) +ᵣ (-ᵣ y)) p)


≤ᵣ-ᵣ : ∀ x y → -ᵣ y ≤ᵣ -ᵣ x → x ≤ᵣ y
≤ᵣ-ᵣ x y =
  subst2 _≤ᵣ_ (-ᵣInvol x) (-ᵣInvol y) ∘ -ᵣ≤ᵣ (-ᵣ y) (-ᵣ x)


a≤b-c⇒c≤b-a-bootstrap : ∀ a b c → a ≤ᵣ b -ᵣ c → c ≤ᵣ b -ᵣ a
a≤b-c⇒c≤b-a-bootstrap a b c p =
  subst2 _≤ᵣ_
    (cong (a +ᵣ_) (+ᵣComm _ _)
      ∙∙ +ᵣAssoc _ _ _
      ∙ cong (_+ᵣ c) (+-ᵣ a)
      ∙∙ +IdL c)
    (sym (+ᵣAssoc _ _ _)
      ∙ cong (b +ᵣ_)
          (+ᵣAssoc _ _ _
            ∙∙ cong (_-ᵣ a) (+ᵣComm _ _ ∙ +-ᵣ c)
            ∙∙ +IdL _))
    (≤ᵣ-+o _ _ (c -ᵣ a) p)


opaque
 unfolding _<ᵣ_

 -ᵣ<ᵣ : ∀ x y → x <ᵣ y → -ᵣ y <ᵣ -ᵣ x
 -ᵣ<ᵣ x y = PT.map
   λ ((q , q') , z , z' , z'') →
     (ℚ.- q' , ℚ.- q) ,
       -ᵣ≤ᵣ (rat q') _ z'' ,
       ℚ.minus-< _ _ z' ,
       -ᵣ≤ᵣ x _ z


<ᵣ-ᵣ : ∀ x y → -ᵣ y <ᵣ -ᵣ x → x <ᵣ y
<ᵣ-ᵣ x y =
  subst2 _<ᵣ_ (-ᵣInvol x) (-ᵣInvol y) ∘ -ᵣ<ᵣ (-ᵣ y) (-ᵣ x)


reverseHalfLineStrict : ∀ x₀ →
  Iso (Σ _ (x₀ <ᵣ_)) (Σ _ (_<ᵣ -ᵣ x₀))
reverseHalfLineStrict x₀ .Iso.fun (x , x₀<) =
  -ᵣ x , -ᵣ<ᵣ _ _ x₀<
reverseHalfLineStrict x₀ .Iso.inv (x , <-x₀) =
  -ᵣ x , isTrans≡<ᵣ _ _ _ (sym (-ᵣInvol _)) (-ᵣ<ᵣ _ _ <-x₀)
reverseHalfLineStrict x₀ .Iso.sec _ =
  Σ≡Prop (λ _ → isProp<ᵣ _ _) (-ᵣInvol _)
reverseHalfLineStrict x₀ .Iso.ret _ =
  Σ≡Prop (λ _ → isProp<ᵣ _ _) (-ᵣInvol _)


reverseHalfLine : ∀ x₀ →
  Iso (Σ _ (x₀ ≤ᵣ_)) (Σ _ (_≤ᵣ -ᵣ x₀))
reverseHalfLine x₀ .Iso.fun (x , x₀≤) =
  -ᵣ x , -ᵣ≤ᵣ _ _ x₀≤
reverseHalfLine x₀ .Iso.inv (x , ≤-x₀) =
  -ᵣ x , isTrans≡≤ᵣ _ _ _ (sym (-ᵣInvol _)) (-ᵣ≤ᵣ _ _ ≤-x₀)
reverseHalfLine x₀ .Iso.sec _ =
  Σ≡Prop (λ _ → isProp≤ᵣ _ _) (-ᵣInvol _)
reverseHalfLine x₀ .Iso.ret _ =
  Σ≡Prop (λ _ → isProp≤ᵣ _ _) (-ᵣInvol _)


reverseHalfLineStrict' : ∀ x₀ →
  Iso (Σ _ ((-ᵣ x₀) <ᵣ_)) (Σ _ (_<ᵣ x₀))
reverseHalfLineStrict' x₀ .Iso.fun (x , x₀<) =
  -ᵣ x , isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ x₀<) (-ᵣInvol _)
reverseHalfLineStrict' x₀ .Iso.inv (x , <-x₀) =
  -ᵣ x , -ᵣ<ᵣ _ _ <-x₀
reverseHalfLineStrict' x₀ .Iso.sec _ =
  Σ≡Prop (λ _ → isProp<ᵣ _ _) (-ᵣInvol _)
reverseHalfLineStrict' x₀ .Iso.ret _ =
  Σ≡Prop (λ _ → isProp<ᵣ _ _) (-ᵣInvol _)


reverseHalfLine' : ∀ x₀ →
  Iso (Σ _ ((-ᵣ x₀) ≤ᵣ_)) (Σ _ (_≤ᵣ x₀))
reverseHalfLine' x₀ .Iso.fun (x , x₀≤) =
  -ᵣ x , isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _ x₀≤) (-ᵣInvol _)
reverseHalfLine' x₀ .Iso.inv (x , ≤-x₀) =
  -ᵣ x , -ᵣ≤ᵣ _ _ ≤-x₀
reverseHalfLine' x₀ .Iso.sec _ =
  Σ≡Prop (λ _ → isProp≤ᵣ _ _) (-ᵣInvol _)
reverseHalfLine' x₀ .Iso.ret _ =
  Σ≡Prop (λ _ → isProp≤ᵣ _ _) (-ᵣInvol _)


reverseHalfLineFn : ∀ x₀ y₀ →
  Iso ((Σ _ (x₀ ≤ᵣ_)) → (Σ _ (y₀ ≤ᵣ_)))
      ((Σ _ (_≤ᵣ (-ᵣ x₀))) → (Σ _ (_≤ᵣ (-ᵣ y₀))))
reverseHalfLineFn x₀ y₀ =
  compIso (codomainIso (reverseHalfLine y₀)) (domIso (reverseHalfLine x₀))


reverseHalfLineFnStrict : ∀ x₀ y₀ →
  Iso ((Σ _ (x₀ <ᵣ_)) → (Σ _ (y₀ <ᵣ_)))
      ((Σ _ (_<ᵣ (-ᵣ x₀))) → (Σ _ (_<ᵣ (-ᵣ y₀))))
reverseHalfLineFnStrict x₀ y₀ =
  compIso
    (codomainIso (reverseHalfLineStrict y₀))
    (domIso (reverseHalfLineStrict x₀))


reverseHalfLineFn' : ∀ x₀ y₀ →
  Iso ((Σ _ ((-ᵣ x₀) ≤ᵣ_)) → (Σ _ ((-ᵣ y₀) ≤ᵣ_)))
      ((Σ _ (_≤ᵣ x₀)) → (Σ _ (_≤ᵣ y₀)))
reverseHalfLineFn' x₀ y₀ =
  compIso (codomainIso (reverseHalfLine' y₀)) (domIso (reverseHalfLine' x₀))


reverseHalfLineFnStrict' : ∀ x₀ y₀ →
  Iso ((Σ _ ((-ᵣ x₀) <ᵣ_)) → (Σ _ ((-ᵣ y₀) <ᵣ_)))
      ((Σ _ (_<ᵣ x₀)) → (Σ _ (_<ᵣ y₀)))
reverseHalfLineFnStrict' x₀ y₀ =
  compIso
    (codomainIso (reverseHalfLineStrict' y₀))
    (domIso (reverseHalfLineStrict' x₀))
