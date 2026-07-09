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
open import Cubical.Data.Int.Fast.Base as ℤ using (pos; negsuc; ℕ₊₁→ℤ; _·_; _-_)
import Cubical.Data.Int.Fast.Properties as ℤ
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.Partition
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.TaggedPartitionConcatenation
open import Cubical.HITs.CauchyReals.Summation
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.RationalsImports

open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

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
   (∫f ((ε /2₊) /2₊)) ( ∫∣f∣ ((ε /2₊) /2₊))
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
             (≤ᵣ-o+ _ _ (rat (fst ((ε /2₊) /2₊)))
              (isTrans≤ᵣ _ _ _ Z
                (<ᵣWeaken≤ᵣ _ _ Y'))))
             (isTrans≡<ᵣ _ _ _
               (+ᵣComm _ _ ∙ sym (+ᵣAssoc _ _ _)
                ∙ cong (s' +ᵣ_) (+ᵣ-rat _ _ ∙ cong rat (ε/2+ε/2≡ε (fst (ε /2₊)))))
                (<ᵣ-o+ _ _ s' (<ℚ→<ᵣ _ _ (x/2<x ε))))
   in ZZ
  where
  δ⊓δ' = min₊ δ δ'
  open RefinableTaggedPartition[_,_] rtp


Integral'-≤ : ∀ a b → a ≤ᵣ b → ∀ f f' s s'
            → (∀ x → x ∈ intervalℙ a b → f x ≤ᵣ f' x)
            → on[ a , b ]IntegralOf f is' s
            → on[ a , b ]IntegralOf f' is' s'
            → s ≤ᵣ s'
Integral'-≤ a b a≤b f f' s s' f≤f' ∫f ∫f' =
 x<y+δ→x≤y _ _ λ ε →
  PT.rec3 (isProp<ᵣ _ _) (ineqForε ε)
   (∫f ((ε /2₊) /2₊)) (∫f' ((ε /2₊) /2₊))
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
        (≤ᵣ-o+ _ _ (rat (fst ((ε /2₊) /2₊)))
         (isTrans≤ᵣ _ _ _ Z
           (<ᵣWeaken≤ᵣ _ _ Y'))))
        (isTrans≡<ᵣ _ _ _
          (+ᵣComm _ _ ∙ sym (+ᵣAssoc _ _ _)
           ∙ cong (s' +ᵣ_) (+ᵣ-rat _ _ ∙ cong rat (ε/2+ε/2≡ε (fst (ε /2₊)))))
           (<ᵣ-o+ _ _ s' (<ℚ→<ᵣ _ _ (x/2<x ε))))
  where
  δ⊓δ' = min₊ δ δ'
  open RefinableTaggedPartition[_,_] rtp

Integral'-C· : ∀ a b → a ≤ᵣ b → ∀ C f s  →
  on[ a , b ]IntegralOf f is' s →
  on[ a , b ]IntegralOf (λ x → C ·ᵣ f x) is' (C ·ᵣ s)
Integral'-C· a b a≤b C f s ∫f ε =
  PT.rec squash₁
    (λ (C' , (absᵣC<C' , _)) →
      let C'₊ = (C' , ℚ<→0< C'
               (<ᵣ→<ℚ 0 C' (isTrans≤<ᵣ 0 (absᵣ C) _ (0≤absᵣ _) absᵣC<C')))
          ε' = ε ℚ₊· invℚ₊ C'₊
      in PT.map
           (map-snd (λ {δ} X tp mesh≤ →
            isTrans≤<ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
               (cong absᵣ (cong (_-ᵣ C ·ᵣ s)
                 (riemannSum'C· (snd tp) C f)
                ∙ sym (Rℝ.·DistR- _ _ _))
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

sum-minus-sum-path : ∀ (r r' s s' : ℝ) →
  (r +ᵣ r') -ᵣ (s +ᵣ s') ≡ (r -ᵣ s) +ᵣ (r' -ᵣ s')
sum-minus-sum-path r r' s s' =
  cong ((r +ᵣ r') +ᵣ_) (sym (Rℝ.-Dist s s'))
  ∙ Rℝ.+ShufflePairs r r' (-ᵣ s) (-ᵣ s')

opaque
 unfolding minᵣ
 Integral'-+ : ∀ a b → a ≤ᵣ b → ∀ f g s s' →
   on[ a , b ]IntegralOf f is' s →
   on[ a , b ]IntegralOf g is' s' →
   on[ a , b ]IntegralOf (λ x → f x +ᵣ g x ) is' (s +ᵣ s')

 Integral'-+ a b x f g s s' ∫f ∫g  ε =
  PT.map2
   (λ (δ , X) (δ' , X') →
     let δ⊓δ' = min₊ δ δ'
     in  δ⊓δ' , λ tp mesh≤  →
       isTrans≤<ᵣ _ _ _
         (isTrans≡≤ᵣ _ _ _
           (cong absᵣ (
             cong (_-ᵣ (s +ᵣ s')) (sym (riemannSum'+ (snd tp) f g))
             ∙ sum-minus-sum-path (riemannSum' (snd tp) f) (riemannSum' (snd tp) g) s s'))
           (absᵣ-triangle _ _))
         (isTrans<≡ᵣ _ _ _
             (<ᵣMonotone+ᵣ _ _ _ _
               (X tp (λ k → isTrans≤ᵣ _ _ _ (mesh≤ k)
                 (≤ℚ→≤ᵣ (fst δ⊓δ') (fst δ) (ℚ.min≤ (fst δ) (fst δ')))))
               (X' tp (λ k → isTrans≤ᵣ _ _ _ (mesh≤ k)
                 (≤ℚ→≤ᵣ (fst δ⊓δ') (fst δ') (ℚ.min≤' (fst δ) (fst δ'))))))
             (+ᵣ-rat (fst (ε /2₊)) _ ∙ cong rat (ε/2+ε/2≡ε (fst ε)))))
    (∫f (ε /2₊)) (∫g (ε /2₊))


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
  let (δ  , X) = fC (ε /2₊)
      (δ' , X') = gC (ε /2₊)
      δ⊔δ' = min₊ δ δ'
  in δ⊔δ' ,
   λ u v u∼v →
     invEq (∼≃abs<ε _ _ _)
      (isTrans<≡ᵣ _ _ _
        (isTrans≤<ᵣ _ _ _
          (isTrans≡≤ᵣ _ _ _
            (cong absᵣ (sum-minus-sum-path (f u) (g u) (f v) (g v)))
            (absᵣ-triangle _ _))
          (<ᵣMonotone+ᵣ _ _ _ _
             (fst (∼≃abs<ε _ _ _) (X u v (∼-monotone≤ (ℚ.min≤ (fst δ) (fst δ')) u∼v)))
             (fst (∼≃abs<ε _ _ _) (X' u v (∼-monotone≤ (ℚ.min≤' (fst δ) (fst δ')) u∼v) ))))
        (+ᵣ-rat _ _ ∙ cong rat (ε/2+ε/2≡ε (fst ε))) )

IsUContinuousC·ᵣ : ∀ f → IsUContinuous f → (C : ℚ) →
   IsUContinuous λ x → rat C ·ᵣ f x
IsUContinuousC·ᵣ f icf C =
  ⊎.rec
    (λ p →
      subst IsUContinuous
        (funExt (λ x → sym (Rℝ.0LeftAnnihilates' _ _ (cong rat (sym p)))))
        (IsUContinuousConst 0))
   (λ 0＃C ε →
      let Z = 0＃→0<abs (rat C) (invEq (rat＃ 0 C) 0＃C)
          ∣C∣ = abs C , ℚ<→0< (abs C) (<ᵣ→<ℚ 0 (abs C)
                 (isTrans<≡ᵣ _ _ _ Z (absᵣ-rat C)))
          δ , X = icf (invℚ₊ ∣C∣ ℚ₊· ε)
      in δ , λ u v u∼v →
         let absDiff = fst (∼≃abs<ε _ _ _) (X u v u∼v)
         in invEq (∼≃abs<ε _ _ _)
               (isTrans≡<ᵣ _ _ _
                 (cong absᵣ (sym (Rℝ.·DistR- (rat C) _ _))
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
     lim-rat _ _ _ (ε /2₊) _ _ (refl∼ _ (ℚ.<→ℚ₊ (fst (ε /2₊)) (fst ε) (x/2<x ε)) )
 elimProp .Elimℝ-Prop.limA x p x₁ y =
   eqℝ _ _ λ ε →
     lim-lim _ _ _ ((ε /2₊) /2₊) ((ε /2₊) /2₊) _ _
       (subst ℚ.0<_
          (cong (ℚ._-_ (fst ε)) (sym (ε/2+ε/2≡ε (fst (ε /2₊)))))
          (snd (ℚ.<→ℚ₊ (fst (ε /2₊)) (fst ε) (x/2<x ε))))
       (sym∼ _ _ _
        (𝕣-lim' _ _ _ ((ε /2₊) /2₊) _
        (snd ((ℚ.<→ℚ₊ (fst ((ε /2₊) /2₊)) (fst ε ℚ.- (fst ((ε /2₊) /2₊) ℚ.+ fst ((ε /2₊) /2₊)))
         ((subst {x = fst (ε /2₊)} (fst ((ε /2₊) /2₊) ℚ.<_)
           (sym (Rℚ.plusMinus _ _) ∙ cong₂ (ℚ._-_) (ε/2+ε/2≡ε (fst ε)) (sym (ε/2+ε/2≡ε (fst (ε /2₊)))) )
            (x/2<x (ε /2₊)))))))
         (refl∼ _ _)))
 elimProp .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isSetℝ _ _

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

minus-plus-minus-path : ∀ (a b c : ℝ) →
  (a -ᵣ b) +ᵣ (b -ᵣ c) ≡ a -ᵣ c
minus-plus-minus-path a b c =
  +ᵣAssoc (a -ᵣ b) b (-ᵣ c)
  ∙ cong (_+ᵣ -ᵣ c) (Rℝ.minusPlus a b)

additive-diff-path₀ : ∀ (s s' t r r' : ℝ) →
  s +ᵣ s' -ᵣ t ≡ ((s -ᵣ r) +ᵣ (s' -ᵣ r')) +ᵣ ((r +ᵣ r') -ᵣ t)
additive-diff-path₀ s s' t r r' =
  sym (minus-plus-minus-path (s +ᵣ s') (r +ᵣ r') t)
  ∙ cong (_+ᵣ ((r +ᵣ r') -ᵣ t)) (sum-minus-sum-path s s' r r')

additive-diff-path : ∀ (s s' t r r' rSum : ℝ) →
  r +ᵣ r' ≡ rSum →
  s +ᵣ s' -ᵣ t ≡ ((s -ᵣ r) +ᵣ (s' -ᵣ r')) +ᵣ (rSum -ᵣ t)
additive-diff-path s s' t r r' rSum r+r'≡rSum =
  additive-diff-path₀ s s' t r r'
  ∙ cong (λ z → ((s -ᵣ r) +ᵣ (s' -ᵣ r')) +ᵣ (z -ᵣ t)) r+r'≡rSum

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
          let δ⊓δ' = min₊ (min₊ δ δ') δ''
              tp-ab , mesh-ab = RefinableTaggedPartition[_,_].tpTP  Y δ⊓δ'
              tp-bc , mesh-bc = RefinableTaggedPartition[_,_].tpTP Y' δ⊓δ'

              tp-ac , rs+ , mesh-ac  = concatTaggedPartition a b c a≤b b≤c
                     tp-ab tp-bc
              R = X'' tp-ac λ k →
                   isTrans≤ᵣ _ _ _
                     (mesh-ac (rat (fst δ⊓δ')) mesh-ab mesh-bc k)
                    (≤ℚ→≤ᵣ _ _ ((ℚ.min≤' (fst (min₊ δ δ')) (fst δ''))))
          in isTrans<ᵣ _ _ _
                (isTrans≤<ᵣ _ _ _
                  (isTrans≡≤ᵣ _ _ _
                   (cong absᵣ
                     (additive-diff-path s s' s+s'
                       (riemannSum' (snd tp-ab) f)
                       (riemannSum' (snd tp-bc) f)
                       (riemannSum' (snd tp-ac) f)
                       (rs+ f)))
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
                    (+ᵣ-rat _ _ ∙ cong rat (ε/2+ε/2≡ε (fst (ε /2₊))))
                    (cong rat (sym (ℚ.·Assoc (fst ε) _ _)))
                    ∙ +ᵣ-rat _ _
                    ∙ cong rat
                      (sym (ℚ.·DistL+ (fst ε) _ _)))
                  (<ℚ→<ᵣ _ _
                    (ℚ.<-o· _ _ (fst ε) (snd ε)
                       (ℚ.decℚ<?
                        {[ pos 1 / 1+ 1 ]
                         ℚ.+ [ pos 1 / 1+ 1 ] ℚ.· [ pos 1 / 1+ 1 ]}
                         {1}) )))
                     (cong rat (ℚ.·IdR (fst ε)))))
        (∃RefinableTaggedPartition rtp-1/n a b a≤b )
        (∃RefinableTaggedPartition rtp-1/n b c b≤c))
    (S ((ε /2₊) /2₊)) (S' ((ε /2₊) /2₊)) (S+S' ((ε /2₊) /2₊))




Integral'-empty : ∀ a → ∀ f s →
  on[ a , a ]IntegralOf f is' s →
  s ≡ 0
Integral'-empty a f s ∫f =
  sym (Rℝ.plusMinus s s)
   ∙∙ cong (_-ᵣ s)
   (Integral'-additive a a a (≤ᵣ-refl a) (≤ᵣ-refl a) f s s s
    ∫f ∫f ∫f )
  ∙∙ +-ᵣ s

x-[x+-y]≡y : ∀ (x y : ℝ) → x -ᵣ (x +ᵣ -ᵣ y) ≡ y
x-[x+-y]≡y x y = v-[v-u]≡u y x

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
     (Integral'≡ a b a≤b f g
       (fst (Integrate-UContinuous a b a≤b f fc))
       x
       (snd (Integrate-UContinuous a b a≤b f fc)))
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


 -- Previous names: FTOC⇒, FTOC⇐', and FTOC⇐ lived here.
 -- They now live in FundamentalTheoremOfCalculus with the point-point
 -- `uDerivativeOfℙ` API.

-- Previously this module opened `IntegrationUC rtp-1/n public`, exporting the
-- default integration machinery at top level. Open `IntegrationUC rtp-1/n` explicitly instead.
