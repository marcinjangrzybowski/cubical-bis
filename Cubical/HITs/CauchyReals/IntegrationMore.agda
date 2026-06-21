{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.IntegrationMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

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
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Summation

clampᵣ-IntegralOf' : ∀ a b → (a≤b : a ≤ᵣ b) → ∀ (f : (x : ℝ) → x ∈ intervalℙ a b → ℝ) s
   → on[ a , b ]IntegralOf
      (λ x → f (clampᵣ a b x) (clampᵣ∈ℚintervalℙ a b a≤b x)) is' s
   ≃ on[ a , b ]IntegralOf curry ∘ f is s

clampᵣ-IntegralOf' a b a≤b f s =

  propBiimpl→Equiv
   (isPropΠ λ _ → squash₁) (isPropΠ λ _ → squash₁)
    (PT.map (map-snd
    (λ X tp msh≤ →
      isTrans≡<ᵣ _ _ _
         (cong absᵣ (cong (_-ᵣ s)
           (riemannSum-clamp (snd tp) f  ∙
             cong (riemannSum' (tp .snd))
               (funExt λ _ →
                cong (f _) (∈-isProp (intervalℙ a b) _ _ _)))))
          (X tp msh≤)))
    ∘_)
    ((PT.map (map-snd
    (λ X tp msh≤ →
      isTrans≡<ᵣ _ _ _
         (sym $ cong absᵣ (cong (_-ᵣ s)
           ( (riemannSum-clamp (snd tp) f)  ∙
             cong (riemannSum' (tp .snd))
               (funExt λ _ →
                cong (f _) (∈-isProp (intervalℙ a b) _ _ _)))))
          (X tp msh≤)))
    ∘_))

Integral'-abs≤ : ∀ a b → a ≤ᵣ b → ∀ f s s'
            → on[ a , b ]IntegralOf f is' s
            → on[ a , b ]IntegralOf (absᵣ ∘ f) is' s'
            → absᵣ s ≤ᵣ s'
Integral'-abs≤ a b a≤b f s s' ∫f ∫∣f∣ =
 x<y+δ→x≤y _ _ λ ε →
  PT.rec3 (isProp<ᵣ _ _) (absIneq ε)
   (∫f (/2₊ (/2₊ ε))) ( ∫∣f∣ (/2₊ (/2₊ ε)))
   (∃RefinableTaggedPartition rtp-1/n a b a≤b)
 where
 absIneq : (ε : ℚ₊) → Σ ℚ₊ _ → Σ ℚ₊ _ → _ →
      absᵣ s <ᵣ s' +ᵣ rat (fst ε)
 absIneq ε (δ , X) (δ' , X') rtp =
   let tp-ab , mesh-ab = tpTP δ⊓δ'
       Y = ((isTrans≡<ᵣ _ _ _
             (minusComm-absᵣ _ _)
             (X tp-ab λ k →
            isTrans≤ᵣ _ _ _
              (mesh-ab k)
              (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst δ) (ℚ.min≤ (fst δ) (fst δ'))))))

       Y' = (isTrans<≡ᵣ _ _ _
            (a-b<c⇒a<c+b _ _ _
            (isTrans≤<ᵣ _ _ _
            (≤absᵣ _)
           (X' tp-ab λ k →
            isTrans≤ᵣ _ _ _
              (mesh-ab k)
              (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst δ') (ℚ.min≤' (fst δ) (fst δ'))))))
              (+ᵣComm _ _))


       Z = riemannSum'-absᵣ≤ (snd tp-ab) f
       ZZ = isTrans≤<ᵣ _ _ _(isTrans≤ᵣ _ _ _
             (a-b≤c⇒a≤c+b _ _ _
               (isTrans≤ᵣ _ _ _
                 (absᵣ-triangle-minus _ _)
                 (<ᵣWeaken≤ᵣ _ _ Y)))
             (≤ᵣ-o+ _ _ (rat (fst (/2₊ (/2₊ ε))))
              (isTrans≤ᵣ _ _ _ Z
                (<ᵣWeaken≤ᵣ _ _ Y'))))
             (isTrans≡<ᵣ _ _ _
               (+ᵣComm _ _ ∙ sym (+ᵣAssoc _ _ _)
                ∙ cong (s' +ᵣ_) (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε)))))
                (<ᵣ-o+ _ _ s' (<ℚ→<ᵣ _ _ (ℚ.x/2<x ε))))
   in ZZ
  where
  δ⊓δ' = ℚ.min₊ δ δ'
  open RefinableTaggedPartition[_,_] rtp


Integral'-≤ : ∀ a b → a ≤ᵣ b → ∀ f f' s s'
            → (∀ x → x ∈ intervalℙ a b → f x ≤ᵣ f' x)
            → on[ a , b ]IntegralOf f is' s
            → on[ a , b ]IntegralOf f' is' s'
            → s ≤ᵣ s'
Integral'-≤ a b a≤b f f' s s' f≤f' ∫f ∫f' =
 x<y+δ→x≤y _ _ λ ε →
  PT.rec3 (isProp<ᵣ _ _) (ineqForε ε)
   (∫f (/2₊ (/2₊ ε))) (∫f' (/2₊ (/2₊ ε)))
   (∃RefinableTaggedPartition rtp-1/n a b a≤b)
 where
 ineqForε : (ε : ℚ₊) → Σ ℚ₊ _ → Σ ℚ₊ _ → _ →
      s <ᵣ s' +ᵣ rat (fst ε)
 ineqForε ε (δ , X) (δ' , X') rtp =
   let tp-ab , mesh-ab = tpTP δ⊓δ'
       Y = a-b<c⇒a<c+b _ _ _
           (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
            (isTrans≡<ᵣ _ _ _
             (minusComm-absᵣ _ _)
             (X tp-ab λ k →
            isTrans≤ᵣ _ _ _
              (mesh-ab k)
              (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst δ) (ℚ.min≤ (fst δ) (fst δ'))))))

       Y' = (isTrans<≡ᵣ _ _ _
            (a-b<c⇒a<c+b _ _ _
            (isTrans≤<ᵣ _ _ _
            (≤absᵣ _)
           (X' tp-ab λ k →
            isTrans≤ᵣ _ _ _
              (mesh-ab k)
              (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst δ') (ℚ.min≤' (fst δ) (fst δ'))))))
              (+ᵣComm _ _))


       Z = riemannSum'≤ (snd tp-ab) f f' (curry ∘ f≤f')
   in isTrans<ᵣ _ _ _(isTrans<≤ᵣ _ _ _
        Y
        (≤ᵣ-o+ _ _ (rat (fst (/2₊ (/2₊ ε))))
         (isTrans≤ᵣ _ _ _ Z
           (<ᵣWeaken≤ᵣ _ _ Y'))))
        (isTrans≡<ᵣ _ _ _
          (+ᵣComm _ _ ∙ sym (+ᵣAssoc _ _ _)
           ∙ cong (s' +ᵣ_) (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε)))))
           (<ᵣ-o+ _ _ s' (<ℚ→<ᵣ _ _ (ℚ.x/2<x ε))))
  where
  δ⊓δ' = ℚ.min₊ δ δ'
  open RefinableTaggedPartition[_,_] rtp

Integral'-C· : ∀ a b → a ≤ᵣ b → ∀ C f s  →
  on[ a , b ]IntegralOf f is' s →
  on[ a , b ]IntegralOf (λ x → C ·ᵣ f x) is' (C ·ᵣ s)
Integral'-C· a b a≤b C f s ∫f ε =
  PT.rec squash₁
    (λ (C' , (absᵣC<C' , _)) →
      let C'₊ = (C' , ℚ.<→0< C'
               (<ᵣ→<ℚ 0 C' (isTrans≤<ᵣ 0 (absᵣ C) _ (0≤absᵣ _) absᵣC<C')))
          ε' = ε ℚ₊· invℚ₊ C'₊
      in PT.map
           (map-snd (λ {δ} X tp mesh≤ →
            isTrans≤<ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
               (cong absᵣ (cong (_-ᵣ C ·ᵣ s)
                 (riemannSum'C· (snd tp) C f)
                ∙ sym (𝐑'.·DistR- _ _ _))
                ∙ ·absᵣ _ _)
               (≤ᵣ-·ᵣo _ _ _
                 (0≤absᵣ _)
                 (<ᵣWeaken≤ᵣ _ _ absᵣC<C')))
              -- X tp mesh≤
              (fst (z<x/y₊≃y₊·z<x _ _ (ℚ₊→ℝ₊ C'₊))
                (isTrans<≡ᵣ _ _ _
                  (X tp mesh≤)
                  (rat·ᵣrat (fst ε) _ ∙
                   cong (rat (fst ε) ·ᵣ_)
                    (sym (invℝ₊-rat C'₊)))))))
           (∫f ε'))
    (denseℚinℝ (absᵣ C) ((absᵣ C) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 (absᵣ C) decℚ<ᵣ?)))


opaque
 unfolding minᵣ
 Integral'-+ : ∀ a b → a ≤ᵣ b → ∀ f g s s' →
   on[ a , b ]IntegralOf f is' s →
   on[ a , b ]IntegralOf g is' s' →
   on[ a , b ]IntegralOf (λ x → f x +ᵣ g x ) is' (s +ᵣ s')

 Integral'-+ a b x f g s s' ∫f ∫g  ε =
  PT.map2
   (λ (δ , X) (δ' , X') →
     let δ⊓δ' = ℚ.min₊ δ δ'
     in  δ⊓δ' , λ tp mesh≤  →
       isTrans≤<ᵣ _ _ _
         (isTrans≡≤ᵣ _ _ _
           (cong absᵣ (
             cong (_-ᵣ (s +ᵣ s')) (sym (riemannSum'+ (snd tp) f g))
             ∙ L𝐑.lem--041))
           (absᵣ-triangle _ _))
         (isTrans<≡ᵣ _ _ _
             (<ᵣMonotone+ᵣ _ _ _ _
               (X tp (λ k → isTrans≤ᵣ _ _ _ (mesh≤ k) (min≤ᵣ _ (rat (fst δ')))))
               (X' tp (λ k → isTrans≤ᵣ _ _ _ (mesh≤ k)
                (min≤ᵣ' (rat (fst δ)) _))))
             (+ᵣ-rat (fst (/2₊ ε)) _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst ε)))))
    (∫f (/2₊ ε)) (∫g (/2₊ ε))




IsUContinuousConst : ∀ C → IsUContinuous (λ _ → C)
IsUContinuousConst C ε = 1 , λ _ _ _ → refl∼ _ _

opaque
 unfolding absᵣ
 IsUContinuousAbsᵣ : IsUContinuous absᵣ
 IsUContinuousAbsᵣ = Lipschitiz→IsUContinuous 1 absᵣ (snd (absᵣL))

opaque
 unfolding maxᵣ
 IsUContinuousMaxᵣ : ∀ x → IsUContinuous (maxᵣ x)
 IsUContinuousMaxᵣ x = Lipschitiz→IsUContinuous 1 (maxᵣ x)
   λ u v ε x₁ → NonExpanding₂-Lemmas.NE.go∼R _ maxR x u v (1 ℚ₊· ε)
     (subst∼ (sym (ℚ.·IdL _)) x₁)


IsUContinuous+ᵣ₂ : ∀ f g → IsUContinuous f → IsUContinuous g →
   IsUContinuous λ x → f x +ᵣ g x
IsUContinuous+ᵣ₂ f g fC gC ε =
  let (δ  , X) = fC (/2₊ ε)
      (δ' , X') = gC (/2₊ ε)
      δ⊔δ' = ℚ.min₊ δ δ'
  in δ⊔δ' ,
   λ u v u∼v →
     invEq (∼≃abs<ε _ _ _)
      (isTrans<≡ᵣ _ _ _
        (isTrans≤<ᵣ _ _ _
          (isTrans≡≤ᵣ _ _ _
            (cong absᵣ L𝐑.lem--041)
            (absᵣ-triangle _ _))
          (<ᵣMonotone+ᵣ _ _ _ _
             (fst (∼≃abs<ε _ _ _) (X u v (∼-monotone≤ (ℚ.min≤ (fst δ) (fst δ')) u∼v)))
             (fst (∼≃abs<ε _ _ _) (X' u v (∼-monotone≤ (ℚ.min≤' (fst δ) (fst δ')) u∼v) ))))
        (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst ε))) )

IsUContinuousC·ᵣ : ∀ f → IsUContinuous f → (C : ℚ) →
   IsUContinuous λ x → rat C ·ᵣ f x
IsUContinuousC·ᵣ f icf C =
  ⊎.rec
    (λ p →
      subst IsUContinuous
        (funExt (λ x → sym (𝐑'.0LeftAnnihilates' _ _ (cong rat (sym p)))))
        (IsUContinuousConst 0))
   (λ 0＃C ε →
      let Z = 0＃→0<abs (rat C) (invEq (rat＃ 0 C) 0＃C)
          ∣C∣ = ℚ.abs C , ℚ.<→0< (ℚ.abs C) (<ᵣ→<ℚ 0 (ℚ.abs C)
                 (isTrans<≡ᵣ _ _ _ Z (absᵣ-rat C)))
          δ , X = icf (invℚ₊ ∣C∣ ℚ₊· ε)
      in δ , λ u v u∼v →
         let absDiff = fst (∼≃abs<ε _ _ _) (X u v u∼v)
         in invEq (∼≃abs<ε _ _ _)
               (isTrans≡<ᵣ _ _ _
                 (cong absᵣ (sym (𝐑'.·DistR- (rat C) _ _))
                   ∙ ·absᵣ _ _ ∙ cong₂ _·ᵣ_ (absᵣ-rat C) refl )
                 (fst (z<x/y₊≃y₊·z<x _ _ (ℚ₊→ℝ₊ ∣C∣))
                  (isTrans<≡ᵣ _ _ _ absDiff
                   (rat·ᵣrat (fst (invℚ₊ ∣C∣)) _ ∙ ·ᵣComm _ _ ∙
                    cong (rat (fst ε) ·ᵣ_)
                    (sym (invℝ₊-rat _) ))))))
    (ℚ.≡⊎# 0 C)

IsUContinuous-ᵣ₂ : ∀ f g → IsUContinuous f → IsUContinuous g →
   IsUContinuous λ x → f x -ᵣ g x
IsUContinuous-ᵣ₂ f g fC gC =
  subst IsUContinuous
    (funExt λ x → cong (f x +ᵣ_) (sym (-ᵣ≡[-1·ᵣ] (g x))))
    (IsUContinuous+ᵣ₂ _ _ fC (IsUContinuousC·ᵣ g gC -1))


lim-const : ∀ x y → lim (const x) y ≡ x
lim-const = Elimℝ-Prop.go elimProp
 where
 elimProp : Elimℝ-Prop _
 elimProp .Elimℝ-Prop.ratA x _ =
   eqℝ _ _ λ ε →
     lim-rat _ _ _ (/2₊ ε) _ _ (refl∼ _ (ℚ.<→ℚ₊ (fst (/2₊ ε)) (fst ε) (ℚ.x/2<x ε)) )
 elimProp .Elimℝ-Prop.limA x p x₁ y =
   eqℝ _ _ λ ε →
     lim-lim _ _ _ (/2₊ (/2₊ ε)) (/2₊ (/2₊ ε)) _ _
       (subst 0<_
          (cong (ℚ._-_ (fst ε)) (sym (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε)))))
          (snd (ℚ.<→ℚ₊ (fst (/2₊ ε)) (fst ε) (ℚ.x/2<x ε))))
       (sym∼ _ _ _
        (𝕣-lim' _ _ _ (/2₊ (/2₊ ε)) _
        (snd ((ℚ.<→ℚ₊ (fst (/2₊ (/2₊ ε))) (fst ε ℚ.- (fst (/2₊ (/2₊ ε)) ℚ.+ fst (/2₊ (/2₊ ε))))
         ((subst {x = fst (/2₊ ε)} (fst (/2₊ (/2₊ ε)) ℚ.<_)
           (sym (𝐐'.plusMinus _ _) ∙ cong₂ (ℚ._-_) (ℚ.ε/2+ε/2≡ε (fst ε)) (sym (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε)))) )
            (ℚ.x/2<x (/2₊ ε)))))))
         (refl∼ _ _)))
 elimProp .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isSetℝ _ _

⊎-map-comm-ids : {A B A' B' : Type} (f : A → A') (g : B → B') →
    ∀ x → ⊎.map f (idfun _) (⊎.map (idfun _) g x) ≡
            ⊎.map (idfun _) g (⊎.map f (idfun _) x)
⊎-map-comm-ids f g (inl x) = refl
⊎-map-comm-ids f g (inr x) = refl

concatTaggedPartition : ∀ a b c → a ≤ᵣ b → b ≤ᵣ c
                → (tp-ab : TaggedPartition[ a , b ])
                → (tp-bc : TaggedPartition[ b , c ])
                → Σ[ tp-ac ∈ TaggedPartition[ a , c ] ]
                  ((∀ f → riemannSum' (snd tp-ab) f +ᵣ riemannSum' (snd tp-bc) f ≡
                          riemannSum' (snd tp-ac) f)
                  × (∀ δ → mesh≤ᵣ (fst tp-ab) δ → mesh≤ᵣ (fst tp-bc) δ → mesh≤ᵣ (fst tp-ac) δ ))
concatTaggedPartition a b c a≤b b≤c (p-ab , s-ab) (p-bc , s-bc) =

  (pAC , sampleAC) , rsConcat , mesh-concat

 where


 module ctp-hlp₀ (n : ℕ) where

  F→⊎' = ⊎.map (idfun _) (Fin+→⊎ 1 (suc (p-bc .len)))
  F→⊎'' = Fin+→⊎ (suc n) (suc (suc (p-bc .len)))
  F→⊎ = F→⊎' ∘ F→⊎''

  F→⊎* = (compIso (Iso-Fin+⊎ _ _) (⊎.⊎Iso' idIso (Iso-Fin+⊎ _ _)))

 F→⊎≡iso : ∀ n x → ctp-hlp₀.F→⊎ n x
          ≡ Iso.fun (ctp-hlp₀.F→⊎* n) x
 F→⊎≡iso zero (zero , l , p) = refl
 F→⊎≡iso zero (suc k , l , p) = refl
 F→⊎≡iso (suc n) (zero , l , p) = refl
 F→⊎≡iso (suc n) (suc k , l , p) =
   let z = F→⊎≡iso n (k , l , injSuc (sym (+-suc _ _) ∙ p))
   in sym (⊎-map-comm-ids _  _ _) ∙ cong (⊎.map fsuc (idfun _)) z
       ∙ ⊎-map-comm-ids _  _ _


 module ctp-hlp (n : ℕ)
                (u : Fin (suc n) → Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ b))
                (u≤u : ∀ (k : Fin n) → fst (u (finj k)) ≤ᵣ fst (u (fsuc k)))
                  where
  open ctp-hlp₀ n public
  pts⊎ : Fin (suc n) ⊎ (Fin 1 ⊎ Fin (suc (len p-bc))) →
    Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ c)
  pts⊎ = ⊎.rec (map-snd (map-snd
    (flip (isTrans≤ᵣ _ _ _) b≤c)) ∘ u)
    (⊎.rec (λ _ → b , a≤b , b≤c)
     λ x → p-bc .pts x ,
       isTrans≤ᵣ _ _ _ a≤b (p-bc .a≤pts x) , p-bc .pts≤b x)


  pts* = pts⊎ ∘ F→⊎


 pts⊎-suc' : ∀ n u u≤u v → fst (ctp-hlp.pts⊎ n (λ z → u (fsuc z))
         (subst2 (λ k₁ k' → fst (u k₁) ≤ᵣ fst (u k')) (toℕ-injective refl)
          (toℕ-injective refl)
          ∘ u≤u ∘ fsuc) v)
      ≡ fst (ctp-hlp.pts⊎ (suc n) u u≤u (⊎.map fsuc (idfun (Fin 1 ⊎ Fin (suc (len p-bc)))) v))
 pts⊎-suc' n u u≤u (inl x) = refl
 pts⊎-suc' n u u≤u (inr (inl x)) = refl
 pts⊎-suc' n u u≤u (inr (inr x)) = refl

 pts⊎-suc : ∀ n k u u≤u →
    fst ((ctp-hlp.pts* n
       (u ∘ fsuc)
       (subst2 (λ k k' →
      fst (u k) ≤ᵣ fst (u k'))
      (toℕ-injective refl)
      (toℕ-injective refl)
      ∘ u≤u ∘ fsuc)
      k)) ≡ fst ((ctp-hlp.pts* (suc n) u u≤u (fsuc k)))

 pts⊎-suc n k*@(k , l , p) u u≤u =
   pts⊎-suc' n u u≤u (P.F→⊎ k*) ∙
     cong (fst ∘ P'.pts⊎)
      (⊎-map-comm-ids _ _ _ ∙
        congS (λ p → ⊎.map (λ x → x) (Fin+→⊎ 1 (suc (len p-bc)))
      (⊎.map fsuc (λ x → x)
       (Fin+→⊎ (suc n) (suc (suc (len p-bc))) (k , l , p))))
       (isSetℕ _ _ _ _))

  where

  module P = ctp-hlp n (λ z → u (fsuc z))
         (subst2 (λ k₁ k' → fst (u k₁) ≤ᵣ fst (u k')) (toℕ-injective refl)
          (toℕ-injective refl)
          ∘ u≤u ∘ fsuc)

  module P' = ctp-hlp (suc n) u u≤u



 pts⊎≤pts⊎ : ∀ n u u≤u k → fst (ctp-hlp.pts* n u u≤u (finj k))
     ≤ᵣ fst (ctp-hlp.pts* n u u≤u (fsuc k))
 pts⊎≤pts⊎ zero u _ (zero , k) = snd (snd (u fzero))
 pts⊎≤pts⊎ zero u _ (suc zero , fst₂ , snd₁) = a≤pts p-bc _
 pts⊎≤pts⊎ zero u _ k*@(suc (suc k) , l , p) =
  let k# : Fin (len p-bc)
      k# = (k , l
        ,  cong predℕ (sym (ℕ.+-suc l  (suc k))
           ∙ cong predℕ ((sym (ℕ.+-suc l (suc (suc k)))) ∙ p)))
  in subst2 (λ k k' →
      pts p-bc k ≤ᵣ pts p-bc k')
       (toℕ-injective refl)
       (toℕ-injective refl)
       (pts≤pts p-bc k#)
 pts⊎≤pts⊎ (suc n) u u≤u (zero , l , p) =
   subst2 (λ k k' →
      fst (u k) ≤ᵣ fst (u k'))
      (toℕ-injective refl)
      (toℕ-injective refl)
       (u≤u fzero)
 pts⊎≤pts⊎ (suc n) u u≤u (suc k , l , p) =
   subst2 _≤ᵣ_
     (pts⊎-suc n (finj k*) u u≤u
       ∙ cong (fst ∘ ctp-hlp.pts* (suc n) u u≤u)
          (toℕ-injective {fj = fsuc (finj k*)} {finj (suc k , l , p)} refl))
       (pts⊎-suc n (fsuc k*) u u≤u
       ∙ cong (fst ∘ ctp-hlp.pts* (suc n) u u≤u)
          (toℕ-injective {fj = (fsuc (fsuc k*))} {(fsuc (suc k , l , p))} refl))
      w
  where
  k* : Fin ((n ℕ.+ (suc (suc (len p-bc)))))
  k* = k , l , cong predℕ (sym (ℕ.+-suc l (suc k)) ∙ p)

  w = pts⊎≤pts⊎ n (u ∘ fsuc)
    (subst2 (λ k k' →
      fst (u k) ≤ᵣ fst (u k'))
      (toℕ-injective refl)
      (toℕ-injective refl)
      ∘ u≤u ∘ fsuc) k*

 open ctp-hlp (p-ab .len) (λ k → p-ab .pts k , p-ab .a≤pts k , p-ab .pts≤b k)
       (pts≤pts p-ab)


 pAC : Partition[ a , c ]
 pAC .len = (p-ab .len ℕ.+ suc (suc (p-bc .len)))
 pAC .pts = fst ∘ pts*
 pAC .a≤pts = fst ∘ snd ∘ pts*
 pAC .pts≤b = snd ∘ snd ∘ pts*
 pAC .pts≤pts = pts⊎≤pts⊎ _ _ (p-ab .pts≤pts)


 pts'-inl* : ∀ x → pts p-ab x ≡ pts pAC (injectFin+' x)
 pts'-inl* x = cong
   (fst ∘ pts⊎ ∘ F→⊎')
   (Fin+→⊎∘injectFin+' _ _ x)


 pts'-inl : ∀ (x : Fin (3 ℕ.+ len p-ab)) → pts' p-ab x ≡ pts' pAC (injectFin+' x)
 pts'-inl (zero , zero , p) = ⊥.rec (ℕ.znots (cong predℕ p))
 pts'-inl (zero , suc l , p) = refl
 pts'-inl x@(suc k , zero , p) =
  cong {x = inr fzero}
        {y = F→⊎'' pK}
        (fst ∘ pts⊎ ∘ F→⊎')
          (injectFin+'-flast-S _ _ _ (snd (snd pK)))

  where

  pK = (k , suc (len p-bc) , _)

 pts'-inl (suc k , l@(suc _) , p) =
  let k' = injectFin+' (suc k , l , p)
    in (pts'-inl* _ ∙
     cong (λ ll → fst
      (pts⊎
       (⊎.map (λ x → x) (Fin+→⊎ 1 (suc (len p-bc)))
        (Fin+→⊎ (suc (len p-ab)) (suc (suc (len p-bc)))
         (k , ll)))))
         (cong snd (toℕ-injective refl))) ∙
     cong (pts' pAC)
       (toℕ-injective
        {fj = suc k , (suc (suc (len p-bc))) ℕ.+ l ,
          (cong (ℕ._+ suc (suc k))
            (ℕ.+-comm (suc (suc (len p-bc))) l)) ∙ snd (snd k')}
        {fk = k'}
         refl)

 pts'-inr : ∀ (x : Fin (3 ℕ.+ len p-bc)) x<' → pts' p-bc x ≡
   pts' pAC (
     fst (injectFin+ {suc (suc (suc (len p-bc)))}
      {suc (suc (len p-ab))}
      x)
     , x<')

 pts'-inr (zero , zero , p) (zero , snd₁) = ⊥.rec (znots (injSuc p))
 pts'-inr (suc k , zero , p) (zero , snd₁) = refl
 pts'-inr (k , zero , p) (suc k' , p') =
   ⊥.rec (snotz (inj-+m {suc k'} {_} {zero} p''))
   where
   p'' = p' ∙
     cong (λ x → suc (suc (suc (len p-ab ℕ.+ x))))
      (sym (injSuc p))
 pts'-inr (zero , suc l , p) (zero , p') =
   ⊥.rec (znots (inj-m+ {suc (suc (suc (len p-ab)))} {0} p'))
 pts'-inr (zero , suc l , p) (suc k' , p') =
   pts'-inl flast ∙
     cong (pts' pAC)
       (toℕ-injective
         {_}
          {injectFin+' {suc (suc (len p-bc))}
           {n = suc (suc (suc (len p-ab)))} flast}
          {(fst (injectFin+ (zero , suc l , p)) , suc k' , p')}
         (injectFin+'-flast≡injectFin+-fzero
         (suc (suc (len p-ab))) (suc (suc (len p-bc)))))

 pts'-inr (suc k , suc l , p) (zero , p') =
   ⊥.rec (znots $
    inj-+m {0} {k} {suc l}
     (injSuc (p'' ∙ (sym (injSuc p)) ∙ +-suc l (suc k)) ∙ +-suc l k))
   where
   p'' = inj-m+ {suc (suc (suc (len p-ab)))} p'
 pts'-inr (suc k , suc l , p) (suc k' , p') =
   cong {x = inr (inr _)}
     {F→⊎ (suc (len p-ab) ℕ.+ suc k , k' , _)}
     (fst ∘ pts⊎)
     ((sym (Iso.rightInv F→⊎* _) ∙
      cong (Iso.fun F→⊎*) (toℕ-injective refl))
        ∙ sym (F→⊎≡iso (len p-ab) _))

  where
  module H = Iso (compIso
      (Iso-Fin+⊎ (suc (len p-ab)) (suc (suc (len p-bc))))
      (⊎.⊎Iso (idIso {A = Fin (suc (len p-ab))})
             (Iso-Fin+⊎ 1 (suc (len p-bc)))))

 <w' : ∀ x → pts' pAC (finj (Iso.inv (Iso-Fin+⊎ _ _) x)) ≤ᵣ
      ⊎.rec (samples s-ab) (samples s-bc)
       x
 <w' (inl x) = isTrans≡≤ᵣ _ _ _
   (cong (pts' pAC) (finj∘inj' x)
    ∙ sym (pts'-inl (finj x)))
   (pts'≤samples s-ab x)
 <w' (inr x) = isTrans≡≤ᵣ _ _ _
     (cong (pts' pAC) (finj∘inj {2 ℕ.+ len p-ab} x
      (snd (finj (injectFin+ {n = 2 ℕ.+ len p-ab} x))))
       ∙ sym (pts'-inr (finj x)
       ((snd (finj (injectFin+ {n = 2 ℕ.+ len p-ab} x))))))
     (pts'≤samples s-bc x)


 w'< : ∀ x → ⊎.rec (samples s-ab) (samples s-bc) x ≤ᵣ
     pts' pAC (fsuc (Iso.inv (Iso-Fin+⊎ _ _) x))


 w'< (inl x) =
   isTrans≤≡ᵣ _ _ _
     (samples≤pts' s-ab x)
     (pts'-inl (fsuc x) ∙
       cong (pts' pAC) (sym (fsuc∘inj' x)))
 w'< (inr x) = isTrans≤≡ᵣ _ _ _
   (samples≤pts' s-bc x)
     (pts'-inr (fsuc x) h ∙
       cong (pts' pAC) (sym (fsuc∘inj x
        h))  )
   where
    h =
       subst (ℕ._<
      suc (suc (suc (len p-ab ℕ.+ suc (suc (len p-bc))))))
       (cong (suc ∘ suc) (sym (+-suc _ _)))
        (snd (fsuc (injectFin+ {n = 2 ℕ.+ len p-ab} x)))

 sampleAC : Sample pAC
 sampleAC .samples = ⊎.rec (samples s-ab) (samples s-bc) ∘ Fin+→⊎ _ _
 sampleAC .pts'≤samples x =  isTrans≡≤ᵣ _ _ _
   (cong (pts' pAC ∘ finj)
     (sym (Iso.leftInv (Iso-Fin+⊎ (suc (suc (p-ab .len))) _) x)))
     (<w' (Iso.fun (Iso-Fin+⊎ _ _) x))
 sampleAC .samples≤pts' x =
   isTrans≤≡ᵣ _ _ _ (w'< (Iso.fun (Iso-Fin+⊎ _ _) x))
     ((cong (pts' pAC ∘ fsuc)
     (Iso.leftInv (Iso-Fin+⊎ (suc (suc (p-ab .len))) _) x)))

 rsConcat : (f : ℝ → ℝ) →
        riemannSum' s-ab f +ᵣ riemannSum' s-bc f ≡ riemannSum' sampleAC f
 rsConcat f =
   cong₂ _+ᵣ_
     (riemannSum'-alt-lem s-ab f ∙
      congS {A = Fin (suc (suc ( len p-ab))) → ℝ}

        (λ f → foldlFin {n = suc (suc ( len p-ab))}
          (λ S k →
           S +ᵣ f k) (rat 0)
           (idfun _))
       (funExt λ x → cong₂ _·ᵣ_
         (cong₂ _-ᵣ_
           (pts'-inl (fsuc x) ∙
             cong {x = (injectFin+' (fsuc x))}
                   {(fsuc (injectFin+' x))} (pts' pAC)
                   (toℕ-injective refl))
           ((pts'-inl (finj x) ∙
             cong {x = (injectFin+' (finj x))}
                   {(finj (injectFin+' x))} (pts' pAC)
                   (toℕ-injective refl))))
         (cong f (sym (rec⊎-injectFin+' (fst ∘ samplesΣ s-ab) _ x) ))))
     (riemannSum'-alt-lem s-bc f ∙
       congS {A = Fin (suc (suc ( len p-bc))) → ℝ}

        (λ f → foldlFin {n = suc (suc ( len p-bc))}
          (λ S k →
           S +ᵣ f k) (rat 0)
           (idfun _))
           (funExt λ x → cong₂ _·ᵣ_
         (cong₂ _-ᵣ_
           (pts'-inr (fsuc x)
             (x< x)
             ∙ sym (cong (pts' pAC) (fsuc∘inj x (x< x))))
           (pts'-inr (finj x) (x<' x) ∙
              sym (cong (pts' pAC)
                (finj∘inj {n = 2 ℕ.+ len p-ab}  x (x<' x)))))
         (cong f (sym (rec⊎-injectFin+ (fst ∘ samplesΣ s-ab) _ x))))) ∙∙
     sym (foldFin-sum-concat
      (suc (suc (len p-ab)))
      (suc (suc (len p-bc))) _)
   ∙∙ sym (riemannSum'-alt-lem sampleAC f)
   where
   x< : (x : Fin (suc (suc (len p-bc)))) →
         _ ℕ.< _
   x< k =
     subst (suc (suc (len p-ab ℕ.+ fst (fsuc k))) ℕ.<_)
       (cong (suc ∘ suc) (+-suc _ _))
       (ℕ.<-k+ {k = suc (suc (len p-ab))} (ℕ.<-k+ {k = 1} (snd k)))

   x<' : (x : Fin (suc (suc (len p-bc)))) →
         _ ℕ.< _
   x<' k = subst (suc (suc (len p-ab ℕ.+ fst (finj k))) ℕ.<_)
       (cong (suc ∘ suc) (+-suc _ _))
       (ℕ.<-k+ {k = suc (suc (len p-ab))} (ℕ.≤-suc (snd k)))



 ⊎suc ⊎inj : Fin (suc (suc (len p-ab))) ⊎ (Fin 1 ⊎ Fin (suc (len p-bc)))
        → Fin (suc (suc (suc (len p-ab)))) ⊎ (Fin (suc (suc (len p-bc))))
 ⊎suc = ⊎.rec (inl ∘ fsuc) (inr ∘ ⊎.rec (λ _ → fzero) (fsuc))
 ⊎inj = ⊎.rec (inl ∘ finj) (⊎.rec (λ _ → inl flast) (inr ∘ finj))

 ⊎→F''' : Fin (suc (suc (suc (len p-ab)))) ⊎ Fin (suc (suc (len p-bc))) →
           Fin (suc (suc (suc (len p-ab))) ℕ.+ suc (suc (len p-bc)))
 ⊎→F''' = Iso.inv (Iso-Fin+⊎ (suc (suc (suc (len p-ab)))) _)

 w'''-⊎ : (δ : ℝ) → mesh≤ᵣ p-ab δ → mesh≤ᵣ p-bc δ →
         ∀ k → (pts' pAC
           (⊎→F''' (⊎suc k) ))
            -ᵣ (pts' pAC (⊎→F''' (⊎inj k))) ≤ᵣ δ
 w'''-⊎ δ me me' (inl x) =
    isTrans≡≤ᵣ _ _ _
      (cong₂ _-ᵣ_
           (sym (pts'-inl (fsuc x)))
           (sym (pts'-inl (finj x))))
      (me x)
 w'''-⊎ δ me me' (inr (inl x)) =
    isTrans≡≤ᵣ _ _ _
      (cong₂ _-ᵣ_
           (cong {x = injectFin+ {n = suc (suc (suc (len p-ab)))} fzero}
                 {fst (injectFin+ {suc (suc (len p-bc))}
                  {n = suc (suc (len p-ab))} (fsuc fzero))
                  , h} (pts' pAC)
                   (toℕ-injective (cong (2 ℕ.+_) (sym (+-suc _ _))))
             ∙ sym (pts'-inr (fsuc fzero)
            (h)))
           (sym (pts'-inl flast)))
      (me' fzero)
    where
    h : _
    h = snd $ finj (injectFin+ {suc (suc (len p-bc))} {n = suc (suc (len p-ab))}
         (fsuc fzero))

 w'''-⊎ δ me me' (inr (inr x)) =

    isTrans≡≤ᵣ _ _ _
      (cong₂ _-ᵣ_
           (cong (pts' pAC) p1 ∙ sym (pts'-inr (fsuc (fsuc x))
             (subst (suc (suc (len p-ab ℕ.+ fst (fsuc (fsuc x)))) ℕ.<_)
       (cong (suc ∘ suc) (+-suc _ _))
       (ℕ.<-k+ {k = suc (suc (len p-ab))} (ℕ.<-k+ {k = 2} (snd x))))))
           (cong (pts' pAC) p2
            ∙ sym (pts'-inr (finj (fsuc x))
             (subst (suc (suc (len p-ab ℕ.+ fst (finj (fsuc x)))) ℕ.<_)
       (cong (suc ∘ suc) (+-suc _ _))
       (ℕ.<-k+ {k = suc (suc (len p-ab))} (ℕ.≤-suc (snd (fsuc x))))))))
      (me' (fsuc x))
   where
    p1 : (⊎→F''' (⊎suc (inr (inr x)))) ≡
        (fst (injectFin+ {suc (suc (suc (len p-bc)))} {suc (suc (len p-ab))}
         (fsuc (fsuc x))) ,
       subst (suc (suc (len p-ab ℕ.+ fst (fsuc (fsuc x)))) ℕ.<_)
       (λ i → suc (suc (+-suc (len p-ab) (suc (suc (len p-bc))) i)))
       (ℕ.<-k+ {2 ℕ.+ x .fst} {k = suc (suc (len p-ab))}
          (ℕ.<-k+ {x .fst} (snd x))))
    p1 = toℕ-injective (cong (suc ∘ suc) (sym (+-suc _ _)))

    p2 :  (⊎→F''' (⊎inj (inr (inr x)))) ≡

           (fst (injectFin+ {suc (suc (suc (len p-bc)))} {suc (suc (len p-ab))}
              (finj (fsuc x))) ,
            subst (suc (suc (len p-ab ℕ.+ fst (finj (fsuc x)))) ℕ.<_)
            (λ i → suc (suc (+-suc (len p-ab) (suc (suc (len p-bc))) i)))
            (ℕ.<-k+ {k = suc (suc (len p-ab))}
             (ℕ.≤-suc (snd (fsuc x)))))
    p2 = toℕ-injective (cong (suc ∘ suc) (sym (+-suc _ _)))

 module F→⊎''' =
   Iso (compIso (Iso-Fin+⊎ (suc (suc (len p-ab))) (suc (suc (len p-bc))))
          (⊎.⊎Iso idIso
             (Iso-Fin+⊎ 1 _)))


 w'''-F→⊎→F-fsuc : ∀ k → fsuc (F→⊎'''.inv k) ≡ ⊎→F''' (⊎suc k)
 w'''-F→⊎→F-fsuc (inl x) = toℕ-injective refl
 w'''-F→⊎→F-fsuc (inr (inl (k , l , p))) =
  toℕ-injective
   (cong (λ k → suc (suc (suc (len p-ab ℕ.+ k))))
    (snd (m+n≡0→m≡0×n≡0 {l} {k} (injSuc (sym (+-suc l k) ∙ p)))))
 w'''-F→⊎→F-fsuc (inr (inr x)) = toℕ-injective refl

 w'''-F→⊎→F-finj : ∀ k → finj (F→⊎'''.inv k) ≡ ⊎→F''' (⊎inj k)
 w'''-F→⊎→F-finj (inl x) = toℕ-injective refl
 w'''-F→⊎→F-finj (inr (inl (k , l , p))) =
  toℕ-injective (cong (suc ∘ suc)
   (cong (len p-ab ℕ.+_) ((snd (m+n≡0→m≡0×n≡0 {l} {k}
    (injSuc (sym (+-suc l k) ∙ p)))))
    ∙ +-zero _))
 w'''-F→⊎→F-finj (inr (inr x)) = toℕ-injective
  (cong (2 ℕ.+_) (+-suc _ _))


 mesh-concat : (δ : ℝ) → mesh≤ᵣ p-ab δ → mesh≤ᵣ p-bc δ →
         ∀ k → pts' pAC (fsuc k) -ᵣ pts' pAC (finj k) ≤ᵣ δ
 mesh-concat δ me me' k =
   isTrans≡≤ᵣ _ _ _
     (cong₂ _-ᵣ_
       (cong (pts' pAC) (cong fsuc (sym (F→⊎'''.leftInv k))
        ∙ w'''-F→⊎→F-fsuc (F→⊎'''.fun k)))
       (cong (pts' pAC) (cong finj (sym (F→⊎'''.leftInv k))
        ∙ w'''-F→⊎→F-finj (F→⊎'''.fun k))))
     (w'''-⊎ δ me me' (F→⊎'''.fun k))

clampDistᵣ
   : (L L' : ℝ) (x y : ℝ) →
     absᵣ (clampᵣ L L' y -ᵣ clampᵣ L L' x) ≤ᵣ
     absᵣ (y -ᵣ x)
clampDistᵣ L L' x y =
 ≤Cont₂
   {λ L L' → absᵣ (clampᵣ L L' y -ᵣ clampᵣ L L' x)}
   {λ _ _ → absᵣ (y -ᵣ x)}
  (cont∘₂ IsContinuousAbsᵣ
    (IsContinuous-₂∘ (IsContinuousClamp₂ y) (IsContinuousClamp₂ x)))
     (cont₂-id _)
  (λ u u' → clampDistᵣ' u u' x y)
  L L'


clampᵣ∼ : ∀ {a b u v ε} → u ∼[ ε ] v → clampᵣ a b u ∼[ ε ] clampᵣ a b v
clampᵣ∼ {a} {b} = invEq (∼≃abs<ε _ _ _)
  ∘ isTrans≤<ᵣ _ _ _ (clampDistᵣ a b _ _)
  ∘ fst (∼≃abs<ε _ _ _)


Integral'-additive : ∀ a b c → a ≤ᵣ b → b ≤ᵣ c → ∀ f s s' s+s' →
  on[ a , b ]IntegralOf f is' s →
  on[ b , c ]IntegralOf f is' s' →
  on[ a , c ]IntegralOf f is' s+s' →
  s +ᵣ s' ≡ s+s'

Integral'-additive a b c a≤b b≤c f s s' s+s' S S' S+S' =
  eqℝ _ _ (invEq (∼≃abs<ε _ _ _) ∘ integralDifference)

 where
 integralDifference : (ε : ℚ₊) → absᵣ (s +ᵣ s' +ᵣ -ᵣ s+s') <ᵣ rat (fst ε)
 integralDifference ε =
   PT.rec3
    (isProp<ᵣ _ _)
    (λ (δ , X) (δ' , X') (δ'' , X'') →
      PT.rec2 (isProp<ᵣ _ _)
        (λ Y Y' →
          let δ⊓δ' = ℚ.min₊ (ℚ.min₊ δ δ') δ''
              tp-ab , mesh-ab = RefinableTaggedPartition[_,_].tpTP  Y δ⊓δ'
              tp-bc , mesh-bc = RefinableTaggedPartition[_,_].tpTP Y' δ⊓δ'

              tp-ac , rs+ , mesh-ac  = concatTaggedPartition a b c a≤b b≤c
                     tp-ab tp-bc
              R = X'' tp-ac λ k →
                   isTrans≤ᵣ _ _ _
                     (mesh-ac (rat (fst δ⊓δ')) mesh-ab mesh-bc k)
                     (≤ℚ→≤ᵣ _ _ ((ℚ.min≤' (fst (ℚ.min₊ δ δ')) (fst δ''))))
          in isTrans<ᵣ _ _ _
                (isTrans≤<ᵣ _ _ _
                  (isTrans≡≤ᵣ _ _ _
                   (cong absᵣ
                     ( sym (𝐑'.+IdR' _ _ (𝐑'.+InvR' _ _ (sym (rs+ f))))
                      ∙ L𝐑.lem--066
                     ∙ cong₂ _+ᵣ_ L𝐑.lem--041 refl
                     ))
                  (isTrans≤ᵣ _ _ _
                   (absᵣ-triangle _ _)
                   (≤ᵣ-+o _ _ _ (absᵣ-triangle _ _))))
                  (<ᵣMonotone+ᵣ _ _ _ _
                   (<ᵣMonotone+ᵣ _ _ _ _
                    (isTrans≡<ᵣ _ _ _
                     (minusComm-absᵣ _ _)
                     (X tp-ab (λ k →
                     isTrans≤ᵣ _ _ _ (mesh-ab k)
                       (≤ℚ→≤ᵣ _ _
                         ((ℚ.isTrans≤ (fst δ⊓δ') _ (fst δ)
                         (ℚ.min≤ (ℚ.min (fst δ) (fst δ')) (fst δ''))
                         (ℚ.min≤ (fst δ) (fst δ'))))) )))
                    (isTrans≡<ᵣ _ _ _
                     (minusComm-absᵣ _ _)
                     (X' tp-bc (λ k →
                     isTrans≤ᵣ _ _ _ (mesh-bc k) (≤ℚ→≤ᵣ _ _
                       (ℚ.isTrans≤ (fst δ⊓δ') _ (fst δ')
                         (ℚ.min≤ (ℚ.min (fst δ) (fst δ')) (fst δ''))
                         (ℚ.min≤' (fst δ) (fst δ')))) ))))
                   R
                   ))
                (isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
                  (cong₂ _+ᵣ_
                    (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε))))
                    (cong rat (sym (ℚ.·Assoc (fst ε) _ _)))
                    ∙ +ᵣ-rat _ _
                    ∙ cong rat
                      (sym (ℚ.·DistL+ (fst ε) _ _)))
                  (<ℚ→<ᵣ _ _
                    (ℚ.<-o· _ _ (fst ε) (ℚ.0<ℚ₊ ε)
                       (ℚ.decℚ<?
                        {[ pos 1 / 1+ 1 ]
                         ℚ.+ [ pos 1 / 1+ 1 ] ℚ.· [ pos 1 / 1+ 1 ]}
                         {1}) )))
                     (cong rat (ℚ.·IdR (fst ε)))))
        (∃RefinableTaggedPartition rtp-1/n a b a≤b )
        (∃RefinableTaggedPartition rtp-1/n b c b≤c))
    (S (/2₊ (/2₊ ε))) (S' (/2₊ (/2₊ ε))) (S+S' (/2₊ (/2₊ ε)))




Integral'-empty : ∀ a → ∀ f s →
  on[ a , a ]IntegralOf f is' s →
  s ≡ 0
Integral'-empty a f s ∫f =
  sym (𝐑'.plusMinus s s)
   ∙∙ cong (_-ᵣ s)
   (Integral'-additive a a a (≤ᵣ-refl a) (≤ᵣ-refl a) f s s s
    ∫f ∫f ∫f )
  ∙∙ +-ᵣ s


module IntegrationUC
 (rtpℚ : ∀ (A B : ℚ) → A ℚ.≤ B
    → RefinableTaggedPartition[ rat A , rat B ] ) where


 module _ (a b : ℝ) (a≤b : a ≤ᵣ b) where


  Integrate-UContinuous' : ∀ f → IsUContinuous f →
   Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B) → Σ ℝ λ R → on[ a , b ]IntegralOf f is' R
  Integrate-UContinuous' f ucf ((A , B) , A≤a , b≤B) =
        IntegralOfUContinuous , isIntegralOfUContinuous
   where
   clamped-pts =
    (clamp-RefinableTaggedPartition
             _ _ a b a≤b
              (A≤a , (isTrans≤ᵣ _ _ _ a≤b b≤B))
              (isTrans≤ᵣ _ _ _ A≤a a≤b , b≤B)
             (rtpℚ A B
               (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                 (isTrans≤ᵣ _ _ _ A≤a a≤b)
                   b≤B))))
   open PreIntegration a b a≤b A B A≤a b≤B clamped-pts f ucf

  preIntegrate-UContinuous : ∀ f → IsUContinuous f
   → ∃[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)
   → Σ ℝ λ R → on[ a , b ]IntegralOf f is' R
  preIntegrate-UContinuous f ucf =
    PT.rec {A = Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)}
     (IntegratedProp a b a≤b f)
     (Integrate-UContinuous' f ucf)

  opaque
   Integrate-UContinuous : ∀ f → IsUContinuous f →
    Σ ℝ λ R → on[ a , b ]IntegralOf f is' R
   Integrate-UContinuous f ucf = preIntegrate-UContinuous f ucf
      (∃enclosingℚInterval a b)



   IntegralConst : ∀ C fc
      → fst (Integrate-UContinuous (λ _ → C) fc) ≡ (C ·ᵣ (b -ᵣ a))
   IntegralConst C fc =
    PT.elim
      (λ q → isSetℝ
        (fst (PT.rec {A = Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)}
      (IntegratedProp a b a≤b (λ _ → C))
      (Integrate-UContinuous' (λ _ → C) fc) q))
        ((C ·ᵣ (b -ᵣ a)) ))
        AA
      (∃enclosingℚInterval a b)
    where
    AA : (x : Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)) →
          fst
          (PT.rec (IntegratedProp a b a≤b (λ _ → C))
           (Integrate-UContinuous' (λ _ → C) fc) ∣ x ∣₁)
          ≡ C ·ᵣ (b -ᵣ a)
    AA ((A , B) , A≤a , b≤B) =
      congLim' _ _ _ (λ ε →
         Partition[_,_].riemannSum'Const
           (snd (tpSeq (suc _))) C) ∙ lim-const _ _

     where

      rtp : RefinableTaggedPartition[ rat A , rat B ]
      rtp = (rtpℚ A B ((≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                 (isTrans≤ᵣ _ _ _ A≤a a≤b)
                   b≤B))))

      clamped-pts : RefinableTaggedPartition[ a , b ]
      clamped-pts = (clamp-RefinableTaggedPartition
             _ _ a b a≤b
              (A≤a , (isTrans≤ᵣ _ _ _ a≤b b≤B))
              (isTrans≤ᵣ _ _ _ A≤a a≤b , b≤B)
             (rtpℚ A B
               (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                 (isTrans≤ᵣ _ _ _ A≤a a≤b)
                   b≤B))))
      open RefinableTaggedPartition[_,_] clamped-pts

      open PreIntegration a b a≤b A B A≤a b≤B clamped-pts
        (λ _ → C) (IsUContinuousConst C)


 IntegralConcat :
   ∀ a b c (a≤b : a ≤ᵣ b) (b≤c : b ≤ᵣ c)
     (f : ℝ → ℝ) (fc : IsUContinuous f) →
     fst (Integrate-UContinuous a b a≤b f fc)
     +ᵣ fst (Integrate-UContinuous b c b≤c f fc)
     ≡ fst (Integrate-UContinuous a c (isTrans≤ᵣ _ _ _ a≤b b≤c) f fc)
 IntegralConcat a b c a≤b b≤c f fc =
   Integral'-additive a b c a≤b b≤c f
        _ _ _
        (snd (Integrate-UContinuous a b a≤b f fc))
        (snd (Integrate-UContinuous b c b≤c f fc))
        (snd (Integrate-UContinuous a c (isTrans≤ᵣ _ _ _ a≤b b≤c) f fc))

 Integral+ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → fst (Integrate-UContinuous a b a≤b f fc)
      +ᵣ  fst (Integrate-UContinuous a b a≤b g gc)
       ≡ fst (Integrate-UContinuous a b a≤b
         (λ x → f x +ᵣ g x) (IsUContinuous+ᵣ₂ f g fc gc))
 Integral+ a b a≤b f g fc gc =
   Integral'Uniq a b a≤b _ _ _
    (Integral'-+ a b a≤b f g
     _ _
     (snd (Integrate-UContinuous a b a≤b f fc))
     (snd (Integrate-UContinuous a b a≤b g gc)))
    (snd (Integrate-UContinuous a b a≤b
         (λ x → f x +ᵣ g x) (IsUContinuous+ᵣ₂ f g fc gc)))



 Integral-C· : ∀ a b (a≤b : a ≤ᵣ b) C f fc fc'
    → C ·ᵣ fst (Integrate-UContinuous a b a≤b f fc)

       ≡ fst (Integrate-UContinuous a b a≤b
         (λ x → C ·ᵣ f x) fc')
 Integral-C· a b a≤b C f fc fc' =
   Integral'Uniq a b a≤b _ _ _
     (Integral'-C· a b a≤b C f _ (snd (Integrate-UContinuous a b a≤b f fc)) )
     (snd (Integrate-UContinuous a b a≤b
         (λ x → C ·ᵣ f x) fc'))


 Integrate-UContinuous-≡ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → (∀ x → f x ≡ g x)
     → fst (Integrate-UContinuous a b a≤b f fc)
     ≡ fst (Integrate-UContinuous a b a≤b g gc)
 Integrate-UContinuous-≡ a b a≤b f g fc gc x =
   cong {A = Σ _ IsUContinuous}
         {x = f , fc} {g , subst IsUContinuous (funExt x) fc }
         (λ (g , gc) → fst (Integrate-UContinuous a b a≤b g gc))
          (ΣPathP (funExt x , toPathP refl))
     ∙ Integral'Uniq a b a≤b _ _ _
       (snd (Integrate-UContinuous a b a≤b g
          (subst IsUContinuous (funExt x) fc)))
        (snd (Integrate-UContinuous a b a≤b g gc))


 Integrate-UContinuous-≡-∈ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → (∀ x → x ∈ intervalℙ a b → f x ≡ g x)
       → fst (Integrate-UContinuous a b a≤b f fc)
       ≡ fst (Integrate-UContinuous a b a≤b g gc)
 Integrate-UContinuous-≡-∈ a b a≤b f g fc gc x =
   Integral'Uniq a b a≤b _ _ _
     (PT.map (map-snd (λ {δ} X tp msh< →
      isTrans≡<ᵣ _ _ _
        (cong (λ rs → absᵣ
         (rs -ᵣ
          Integrate-UContinuous a b a≤b f fc .fst))
             (sym (riemannSum'≡ (snd tp) _ _ x)))
        (X tp msh<)))
       ∘ (snd (Integrate-UContinuous a b a≤b f fc)))
     (snd (Integrate-UContinuous a b a≤b g gc))

 Integral- : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → fst (Integrate-UContinuous a b a≤b f fc)
      -ᵣ  fst (Integrate-UContinuous a b a≤b g gc)
       ≡ fst (Integrate-UContinuous a b a≤b
         (λ x → f x -ᵣ g x) (IsUContinuous-ᵣ₂ f g fc gc))
 Integral- a b a≤b f g fc gc = PT.rec
   (isSetℝ _ _)
     (λ icNeg →
        let -1·gc : IsUContinuous (λ x → (rat [ ℤ.negsuc zero / 1+ zero ]) ·ᵣ g x)
            -1·gc = subst IsUContinuous
                    (funExt (λ _ → ·ᵣComm _ _)) (IsUContinuous∘ icNeg gc)
            -gc : IsUContinuous (λ x → -ᵣ (g x))
            -gc = subst IsUContinuous
                    (funExt λ x → sym (-ᵣ≡[-1·ᵣ] (g x))) -1·gc
        in   cong (fst (Integrate-UContinuous a b a≤b f fc) +ᵣ_)
                   (-ᵣ≡[-1·ᵣ] (fst (Integrate-UContinuous a b a≤b g gc))
                     ∙∙ Integral-C· a b a≤b
                         (rat [ ℤ.negsuc zero / 1+ zero ]) g gc -1·gc
                     ∙∙ Integrate-UContinuous-≡ a b a≤b
                         _ _ _ _
                          (λ x → sym (-ᵣ≡[-1·ᵣ] (g x))))

                ∙ Integral+ a b a≤b f (-ᵣ_ ∘ g) fc
                  -gc
                 ∙ Integrate-UContinuous-≡ a b a≤b _ _ _ _
                   (λ x → sym (x-ᵣy≡x+ᵣ[-ᵣy] (f x) (g x))))
     (IsUContinuous·ᵣR (rat [ ℤ.negsuc zero / 1+ zero ]) )

 Integral-absᵣ≤ : ∀ a b (a≤b : a ≤ᵣ b) f fc fc' →
       absᵣ (fst (Integrate-UContinuous a b a≤b f fc))
         ≤ᵣ (fst (Integrate-UContinuous a b a≤b (absᵣ ∘ f) fc'))
 Integral-absᵣ≤ a b a≤b f fc fc' =
   Integral'-abs≤ a b a≤b f _ _
     (snd (Integrate-UContinuous a b a≤b f fc))
     (snd (Integrate-UContinuous a b a≤b (absᵣ ∘ f) fc'))


 IntegralAbs : ∀ a b (a≤b : a ≤ᵣ b) f fc
    → ∀ fc-sup → (∀ x → x ∈ intervalℙ a b → absᵣ (f x) ≤ᵣ fc-sup)
    → absᵣ (fst (Integrate-UContinuous a b a≤b f fc)) ≤ᵣ fc-sup ·ᵣ (b -ᵣ a)
 IntegralAbs a b a≤b f fc fc-sup x =
  isTrans≤≡ᵣ _ _ _
    (isTrans≤ᵣ _ _ _
    (Integral-absᵣ≤  a b a≤b _ _ _)
    (Integral'-≤ a b a≤b (absᵣ ∘ f) (λ _ → fc-sup) _ _
      x
      (snd (Integrate-UContinuous a b a≤b (absᵣ ∘ f)
        (IsUContinuous∘ IsUContinuousAbsᵣ fc)) )
      (snd (Integrate-UContinuous a b a≤b (λ _ → fc-sup)
        (IsUContinuousConst _)))))
    (IntegralConst a b a≤b fc-sup _)

 Integrate-UContinuousℙ : ∀ a b (a≤b : a ≤ᵣ b) f
   → IsUContinuousℙ (intervalℙ a b) f →
    Σ ℝ λ R → on[ a , b ]IntegralOf curry ∘ f is R
 Integrate-UContinuousℙ a b a≤b f ucf =
   map-snd (fst (clampᵣ-IntegralOf' _ _ _ _ _))
     (Integrate-UContinuous
       a b a≤b (λ x → f (clampᵣ a b x) (clampᵣ∈ℚintervalℙ a b a≤b x))
        ((λ {ε} →
          map-snd
           λ {δ} X u v u∼v →
            X _ _ _ _
             (invEq (∼≃abs<ε _ _ _)
              (isTrans≤<ᵣ _ _ _
                (clampDistᵣ a b v u)
                (fst (∼≃abs<ε _ _ _) u∼v))))
           ∘ ucf))


 Integrate-UContinuousℙ-≡ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → (∀ x x∈ → f x x∈ ≡ g x x∈)
    → fst (Integrate-UContinuousℙ a b a≤b f fc)
       ≡ fst (Integrate-UContinuousℙ a b a≤b g gc)
 Integrate-UContinuousℙ-≡ a b a≤b f g fc gc x =
   cong {x = f , fc} {g , _}
     (fst ∘ uncurry (Integrate-UContinuousℙ a b a≤b))
      (ΣPathP (funExt₂ x , toPathP refl))
        ∙ IntegralUniq a b a≤b _ _ _
       (snd (Integrate-UContinuousℙ a b a≤b g
          (subst (IsUContinuousℙ (intervalℙ a b)) (funExt₂ x) fc)))
        (snd (Integrate-UContinuousℙ a b a≤b g gc))


 FTOC⇒ : ∀ x₀ (f : ℝ → ℝ) → (ucf : IsUContinuous f)
                 → (uDerivativeOfℙ (pred≥ x₀) ,
                         (λ x x₀≤x →
                           fst (Integrate-UContinuous x₀ x x₀≤x f ucf))
                         is (λ x _ → f x))
 FTOC⇒ x₀ f ucf ε =
  PT.map (map-snd (ftoc _))
   (IsUContinuous-εᵣ f ucf
    (ℚ₊→ℝ₊ ([ 1 / 2 ] , _ ) ₊·ᵣ (ℚ₊→ℝ₊ ε)))
  where
  ftoc : ∀ δ → ((u v : ℝ) → u ∼[ δ ] v → absᵣ (f u -ᵣ f v) <ᵣ _)
   → ∀ x x₀≤x (r : ℝ) (r∈ : r ∈ (λ x₁ → pred≥ x₀ (x +ᵣ x₁)))
      (x＃r : 0 ＃ r) →
      absᵣ r <ᵣ fst (ℚ₊→ℝ₊ δ) →
      absᵣ
      (f x -ᵣ
       differenceAtℙ (pred≥ x₀)
       (λ x₁ x₀≤x₁ → fst (Integrate-UContinuous x₀ x₁ x₀≤x₁ f ucf)) x r
       x＃r x₀≤x r∈)
      <ᵣ rat (fst ε)
  ftoc δ X x x₀≤x h r∈ 0＃h x₁ =
    invEq (z<x≃y₊·z<y₊·x _ _ h₊)
     (isTrans≡<ᵣ _ _ _
       (cong₂ _·ᵣ_ (sym (absᵣNonNeg (absᵣ h) (0≤absᵣ h))) refl ∙ sym (·absᵣ _ _) ∙
        cong absᵣ (𝐑'.·DistR- (absᵣ h) _ _ ∙ cong₂ _-ᵣ_ (·ᵣComm _ _ ∙ fx-const-integral)
           (cong₂ _·ᵣ_ (·sign-flip≡ h 0＃h) refl  ∙ (·ᵣComm _ _) ∙
            ·ᵣAssoc _ _ _ ∙
             cong₂ _·ᵣ_ ([x/y]·yᵣ _ h 0＃h) refl
             ∙ h-sidesCases-lem 0＃h) ∙
              Integral- x'* x* x*∈
                (λ _ → f x) f
                (IsUContinuousConst (f x)) ucf))
       (isTrans<≡ᵣ _ _ _
         (isTrans≤<ᵣ _ _ _ (IntegralAbs x'* x* x*∈
            (λ x₂ → f x -ᵣ f x₂)
           (IsUContinuous-ᵣ₂ (λ _ → f x) f (IsUContinuousConst (f x)) ucf) (rat [ 1 / 2 ] ·ᵣ rat (fst ε))
         X')
         (isTrans≡<ᵣ _ _ _
           (sym (·ᵣAssoc _ _ _))
           (<ᵣ-·ᵣo  _ _ ((ℚ₊→ℝ₊ ε) ₊·ᵣ (_ , 0<x*-x'*)) decℚ<ᵣ? )))
         (·IdL _ ∙ cong (rat (fst ε) ·ᵣ_) x*-x'*≡∣h∣ ∙ ·ᵣComm _ _)))


   where



   x* : ℝ
   x* = maxᵣ x (x +ᵣ h)

   x'* : ℝ
   x'* = minᵣ x (x +ᵣ h)

   x*∈ = (isTrans≤ᵣ x'* _ x* (min≤ᵣ x (x +ᵣ h)) (≤maxᵣ x (x +ᵣ h)) )


   opaque
    unfolding maxᵣ
    x*-x'*≡∣h∣ : x* -ᵣ x'* ≡ absᵣ h
    x*-x'*≡∣h∣ = ⊎.rec
      (λ 0<h →
       let z = <ᵣWeaken≤ᵣ x (x +ᵣ h)
             (isTrans≡<ᵣ _ _ _ (sym (+IdR x)) (<ᵣ-o+ 0 h x 0<h))

       in cong₂ _-ᵣ_ (≤→maxᵣ _ _ z) (≤→minᵣ x (x +ᵣ h) z)
            ∙∙ L𝐑.lem--063 {x} {h} ∙∙ sym (absᵣPos h 0<h))
      (λ h<0 →
       let z = <ᵣWeaken≤ᵣ (x +ᵣ h) x
              (isTrans<≡ᵣ _ _ _ (<ᵣ-o+ h 0 x h<0) (+IdR x))

       in cong₂ _-ᵣ_
          (maxᵣComm x (x +ᵣ h) ∙ ≤→maxᵣ _ _ z)
          (minᵣComm x (x +ᵣ h) ∙ ≤→minᵣ _ _ z)
          ∙∙ sym (L𝐑.lem--050 {h} {x}) ∙∙ sym (absᵣNeg _ h<0))
     0＃h

   h₊ : ℝ₊
   h₊ = absᵣ h , 0＃→0<abs h 0＃h

   0<x*-x'* : 0 <ᵣ x* -ᵣ x'*
   0<x*-x'* = isTrans<≡ᵣ _ _ _ (snd h₊)
     (sym x*-x'*≡∣h∣)

   opaque
    unfolding minᵣ maxᵣ
    h-sidesCases-lem : ∀ 0＃h →
      (fst (Integrate-UContinuous x₀ (x +ᵣ h) r∈ f ucf) -ᵣ
         fst (Integrate-UContinuous x₀ x x₀≤x f ucf))
        ·ᵣ signᵣ h 0＃h ≡
         fst (Integrate-UContinuous x'* x* x*∈ f ucf)
    h-sidesCases-lem (inl u) =
        ·IdR _
      ∙ cong (_-ᵣ fst (Integrate-UContinuous x₀ _ x₀≤x f ucf))
        ( cong (λ r∈ → fst (Integrate-UContinuous x₀ (x +ᵣ h) r∈ f ucf))
               (isProp≤ᵣ _ _ _ _)
        ∙ sym (IntegralConcat x₀ x (x +ᵣ h) x₀≤x x≤x+h
             f ucf))
      ∙ L𝐑.lem--063 ∙
         cong {A = Σ (ℝ × ℝ) (uncurry _≤ᵣ_)}
             {x = (x , x +ᵣ h) , _}
             {(x'* , x*) , _}
           ((λ ((x'* ,  x*) , x*∈)  →
              fst (Integrate-UContinuous x'* x* x*∈ f ucf)))
           (Σ≡Prop (uncurry isProp≤ᵣ)
            (cong₂ _,_
                (sym (≤→minᵣ x (x +ᵣ h) (x≤x+h)))
                (sym (≤→maxᵣ x (x +ᵣ h) (x≤x+h)))))

       where
       x≤x+h : x ≤ᵣ x +ᵣ h
       x≤x+h = isTrans≡≤ᵣ _ _ _ (sym (+IdR x))
             (≤ᵣ-o+ _ _ x (<ᵣWeaken≤ᵣ _ _ u))
    h-sidesCases-lem (inr u) =
       ·ᵣComm _ _
     ∙∙ sym (-ᵣ≡[-1·ᵣ] _)
     ∙∙ -[x-y]≡y-x _ _
     ∙∙ cong (_-ᵣ fst (Integrate-UContinuous x₀ (x +ᵣ h) r∈ f ucf))
             (cong (λ r∈ → fst (Integrate-UContinuous x₀ x r∈ f ucf))
               (isProp≤ᵣ _ _ _ _)
            ∙ sym (IntegralConcat x₀ (x +ᵣ h) x r∈ x+h≤x
               f ucf))
     ∙ L𝐑.lem--063
     ∙∙ cong {A = Σ (ℝ × ℝ) (uncurry _≤ᵣ_)}
             {x = (x +ᵣ h , x) , _}
             {(x'* , x*) , _}
           ((λ ((x'* ,  x*) , x*∈)  →
              fst (Integrate-UContinuous x'* x* x*∈ f ucf)))
           (Σ≡Prop (uncurry isProp≤ᵣ)
            (cong₂ _,_
                (sym (≤→minᵣ (x +ᵣ h) x (x+h≤x)) ∙ minᵣComm _ x)
                (sym (≤→maxᵣ (x +ᵣ h) x (x+h≤x)) ∙ maxᵣComm _ x)))
       where
       x+h≤x : x +ᵣ h ≤ᵣ x
       x+h≤x = isTrans≤≡ᵣ _ _ _
             (≤ᵣ-o+ _ _ x (<ᵣWeaken≤ᵣ _ _ u))
             (+IdR x)

   fx-const-integral : f x ·ᵣ absᵣ h ≡
        fst (Integrate-UContinuous x'* x* x*∈ (λ _ → f x) (IsUContinuousConst _))
   fx-const-integral =
       cong (f x ·ᵣ_) (sym x*-x'*≡∣h∣)
     ∙ sym (IntegralConst x'* x* x*∈ (f x) (IsUContinuousConst _))

   opaque
    unfolding maxᵣ

    X' : (x' : ℝ) →
          x' ∈ intervalℙ x'* x* →
          absᵣ (f x -ᵣ f x') ≤ᵣ rat [ 1 / 2 ] ·ᵣ rat (fst ε)
    X' x' (≤x' , x'≤) =
      <ᵣWeaken≤ᵣ _ _ (X x x' (invEq (∼≃abs<ε _ _ _)
       ((isTrans≤<ᵣ _ _ _
        (isTrans≤≡ᵣ _ _ _
         (hh 0＃h)
          (x*-x'*≡∣h∣)) x₁))))

      where
       hh : rat [ pos 0 / 1+ 0 ] ＃ h →  absᵣ (x +ᵣ -ᵣ x') ≤ᵣ x* -ᵣ x'*
       hh (inl 0<h) = isTrans≡≤ᵣ _ _ _
         (minusComm-absᵣ _ _ )
         (isTrans≡≤ᵣ _ _ _
           (absᵣNonNeg _ (x≤y→0≤y-x _ _
             (isTrans≡≤ᵣ _ _ _ (sym (≤→minᵣ x (x +ᵣ h) (x≤x+h))) ≤x')))
           (≤ᵣMonotone+ᵣ _ _ _ _ x'≤ (-ᵣ≤ᵣ _ _ (min≤ᵣ x (x +ᵣ h)))))
          where
           x≤x+h : x ≤ᵣ x +ᵣ h
           x≤x+h = isTrans≡≤ᵣ _ _ _ (sym (+IdR x))
                 (≤ᵣ-o+ _ _ x (<ᵣWeaken≤ᵣ _ _ 0<h))
       hh (inr h<0) =
         (isTrans≡≤ᵣ _ _ _
           (absᵣNonNeg _ ((x≤y→0≤y-x _ _
             (isTrans≤≡ᵣ _ _ _ x'≤ (maxᵣComm x (x +ᵣ h) ∙
              (≤→maxᵣ (x +ᵣ h) x (x+h≤x)))))))
            (≤ᵣMonotone+ᵣ _ _ _ _ (≤maxᵣ x (x +ᵣ h))
             (-ᵣ≤ᵣ _ _ ≤x'))
           )


        where
        x+h≤x : x +ᵣ h ≤ᵣ x
        x+h≤x = isTrans≤≡ᵣ _ _ _
              (≤ᵣ-o+ _ _ x (<ᵣWeaken≤ᵣ _ _ h<0))
              (+IdR x)



 FTOC⇐' : ∀ a b (a<b : a <ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
           → ∀ (ucf : IsUContinuousℙ (intervalℙ a b) f)
           → uDerivativeOfℙ (intervalℙ a b) , F is f
           → fst (Integrate-UContinuousℙ a b (<ᵣWeaken≤ᵣ _ _ a<b) f ucf)
               ≡ F b _ -ᵣ F a _
 FTOC⇐' a b a<b f F ucf udc =
   let a≤b = <ᵣWeaken≤ᵣ _ _ a<b
       f∘clamp = λ x → f (clampᵣ a b x) (clampᵣ∈ℚintervalℙ a b a≤b x)
       ucf∘clamp : IsUContinuous f∘clamp
       ucf∘clamp = map-snd
         (λ {δ} X u v u∼v → X _ _ _ _ (clampᵣ∼ {a} {b}  u∼v))
                ∘ ucf
       z =
           subst2 (uDerivativeOfℙ (pred≥ a) ,_is_)
             (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
             (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
             (C·uDerivativeℙ (pred≥ a) -1 _ _ (FTOC⇒ a f∘clamp ucf∘clamp))


       f* : (r : ℝ) → r ∈ intervalℙ a b → ℝ
       f* r r∈ = -ᵣ (fst (Integrate-UContinuous a r (fst r∈) f∘clamp ucf∘clamp))
       zD : _
       zD = +uDerivativeℙ (intervalℙ a b) _ _
                f* (λ x _ → -ᵣ (f∘clamp x))
              udc λ ε →
                PT.map (map-snd
                  (λ X →
                    λ x x∈ h h∈ 0＃h x₁ →
                     X x (fst x∈) h (fst h∈) 0＃h x₁
                     ))
                  (z ε)
       b∈ = a≤b , ≤ᵣ-refl _
       a∈ = ≤ᵣ-refl _ , a≤b
       z' : F a (≤ᵣ-refl a , a≤b) ≡ F b (a≤b , ≤ᵣ-refl b) +ᵣ f* b b∈
       z' = sym (𝐑'.+IdR' _ _
             (cong -ᵣ_
               (Integral'-empty a f∘clamp _
                (snd (Integrate-UContinuous a a (≤ᵣ-refl a) f∘clamp ucf∘clamp)))
               ∙ (-ᵣ-rat 0)))
             ∙ nullDerivative→const a b
                a∈ b∈
                a<b (λ r r∈ → F r r∈ +ᵣ f* r r∈)

                 (subst (uDerivativeOfℙ (intervalℙ a b) ,
                   (λ r r∈ → F r r∈ +ᵣ f* r r∈) is_)
                   (funExt₂ (λ x x∈ →
                     cong₂ _-ᵣ_  refl
                       ( cong (uncurry f)
                         (Σ≡Prop (∈-isProp (intervalℙ a b))
                          (sym (∈ℚintervalℙ→clampᵣ≡ a b x x∈)))) ∙ +-ᵣ _ )) zD)
   in Integrate-UContinuous-≡-∈ a b a≤b _ _ _ _
        (λ _ _ → refl)
       ∙ sym L𝐑.lem--079
       ∙ cong₂ _-ᵣ_ refl (sym z')

 -- FTOC⇐'' : ∀ a b (a<b : a <ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
 --           → (ucf : IsUContinuousℙ (intervalℙ a b) f)
 --           → uDerivativeOfℙ (intervalℙ a b) , F is f
 --           → ∀ x x∈
 --           → on[ a , x ]IntegralOf
 --               (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is
 --               (F x x∈ -ᵣ F a {!!})
 -- FTOC⇐'' a b a<b f F ucf fd x x∈ = {!w!}
 --  where
 --  w = FTOC⇐' a x

 FTOC⇐ : ∀ a b (a<b : a <ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
        → IsUContinuousℙ (intervalℙ a b) f
           → uDerivativeOfℙ (intervalℙ a b) , F is f
           → (on[ a , b ]IntegralOf curry ∘ f is (F b _ -ᵣ F a _))
 FTOC⇐ a b a<b f F ucf udc =
     subst (on[ a , b ]IntegralOf curry ∘ f is_)
     (FTOC⇐' a b a<b _ _ ucf udc)
     (snd (Integrate-UContinuousℙ a b (<ᵣWeaken≤ᵣ a b a<b) f ucf))

open IntegrationUC rtp-1/n  public
