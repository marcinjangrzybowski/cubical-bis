module Cubical.HITs.CauchyReals.Calculus.Integration.Properties where

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

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using
  (absᵣ-triangle-minus)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp using
  (clampᵣ∈intervalℙ)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Limits using (lim-const)
open import Cubical.HITs.CauchyReals.Analysis.Uniform
  using
  ( IsUContinuousConst
  ; IsUContinuousAbsᵣ
  ; IsUContinuousMaxᵣ
  ; IsUContinuous+ᵣ₂
  ; IsUContinuousC·ᵣ
  ; IsUContinuous-ᵣ₂
  ; clampDistᵣ
  ; clampᵣ∼
  )
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.MeanValue
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Concatenation
open import Cubical.HITs.CauchyReals.Calculus.Integration.Summation
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

clampᵣ-IntegralOf' : ∀ a b → (a≤b : a ≤ᵣ b) → ∀ (f : (x : ℝ) → x ∈ intervalℙ a b → ℝ) s
   → on[ a , b ]IntegralOf
      (λ x → f (clampᵣ a b x) (clampᵣ∈intervalℙ a b a≤b x)) is' s
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

[x-y]-[x-z]≡z-y : ∀ (x y z : ℝ) → (x -ᵣ y) -ᵣ (x -ᵣ z) ≡ z -ᵣ y
[x-y]-[x-z]≡z-y x y z = ℝ!
