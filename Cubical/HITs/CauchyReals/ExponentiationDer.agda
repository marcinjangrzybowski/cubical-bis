{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.ExponentiationDer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos; ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

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
open import Cubical.HITs.CauchyReals.Bisect
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Derivative

open import Cubical.HITs.CauchyReals.Exponentiation

import Cubical.Algebra.CommRing.Instances.Int as ℤCRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.CommRing.Properties as CR

module L𝐙 = Lems ℤCRing.ℤCommRing
module 𝐙' = RingTheory (CR.CommRing→Ring ℤCRing.ℤCommRing )



slopeMonotone^ : (n : ℕ) (a b a' b' : ℝ₊)
  → (a<b : fst a <ᵣ fst b) → (a'<b' : fst a' <ᵣ fst b')
  → (a≤a' : fst a ≤ᵣ fst a') →  (b≤b' : fst b ≤ᵣ fst b') →
  (((fst b ^ⁿ n) -ᵣ (fst a ^ⁿ n))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a<b ))
      ≤ᵣ
  (((fst b' ^ⁿ n) -ᵣ (fst a' ^ⁿ n))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
slopeMonotone^ zero a b a' b' a<b a'<b' a≤a' b≤b' =
  ≡ᵣWeaken≤ᵣ _ _
    ((𝐑'.0LeftAnnihilates' _ _ (+-ᵣ _))
    ∙ sym (𝐑'.0LeftAnnihilates' _ _ (+-ᵣ _)))
slopeMonotone^ (suc zero) a b a' b' a<b a'<b' a≤a' b≤b' =
  ≡ᵣWeaken≤ᵣ _ _
    ((cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a<b )) (cong₂ _-ᵣ_ (·IdL _) (·IdL _))
      ∙ x·invℝ₊[x] _)
     ∙ sym (x·invℝ₊[x] _) ∙ (cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
       (sym ((cong₂ _-ᵣ_ (·IdL _) (·IdL _))))))
slopeMonotone^ (suc (suc N)) a b a' b' a<b a'<b' a≤a' b≤b' =
   subst2 _≤ᵣ_
     (sym ([x·yᵣ]/₊y _ (_ , x<y→0<y-x _ _ a<b ))
       ∙ cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a<b )) (·ᵣComm _ _ ∙ fa.[b-a]·S≡bⁿ-aⁿ))
     (sym ([x·yᵣ]/₊y _ (_ , x<y→0<y-x _ _ a'<b'))
       ∙ cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' )) (·ᵣComm _ _ ∙ fa'.[b-a]·S≡bⁿ-aⁿ))
     (Seq≤→Σ≤-upto
       (geometricProgression _ fa.r)
       (geometricProgression _ fa'.r)
       (suc (suc N))
       w)
 where
 open bⁿ-aⁿ N
 module fa = factor (fst a) (fst b) (snd a) (snd b)
 module fa' = factor (fst a') (fst b') (snd a') (snd b')

 w : (n₁ : ℕ) → n₁ ℕ.< suc (suc N) →
      geometricProgression (fst b ^ⁿ (suc N)) (fst a ／ᵣ[ fst b , _ ]) n₁ ≤ᵣ
      geometricProgression (fst b' ^ⁿ (suc N)) (fst a' ／ᵣ[ fst b' , _ ]) n₁
 w n x =
  let (m , p) = ℕ.predℕ-≤-predℕ x
  in subst2 _≤ᵣ_ -- ^ℕ-+
    ((cong₂ _·ᵣ_ refl (sym ([x/y]·yᵣ _ _ (inl (0<x^ⁿ _ _ (snd b))))
     ∙ ·ᵣComm _ _) ∙ ·ᵣAssoc _ _ _)
      ∙ cong₂ _·ᵣ_
          ((cong fst (^ℕ-+ b _ _) ∙ cong ((fst b) ^ⁿ_) (p)))
          (／^ⁿ _ _ _ _ _)
      ∙ sym (geometricProgressionClosed _ _ _))
    ((cong₂ _·ᵣ_ refl (sym ([x/y]·yᵣ _ _ (inl (0<x^ⁿ _ _ (snd b'))))
     ∙ ·ᵣComm _ _) ∙ ·ᵣAssoc _ _ _)
      ∙ cong₂ _·ᵣ_
          ((cong fst (^ℕ-+ b' _ _) ∙ cong ((fst b') ^ⁿ_) (p)))
          (／^ⁿ _ _ _ _ _)
      ∙ sym (geometricProgressionClosed _ _ _))
    (≤ᵣ₊Monotone·ᵣ _ _ _ _
      (<ᵣWeaken≤ᵣ _ _ (0<x^ⁿ _ _ (snd b')))
      (<ᵣWeaken≤ᵣ _ _ (0<x^ⁿ _ _ (snd a)))
      (^ⁿ-Monotone _ (<ᵣWeaken≤ᵣ _ _ (snd b)) b≤b')
       (^ⁿ-Monotone _ (<ᵣWeaken≤ᵣ _ _ (snd a)) a≤a') )

slope-monotone-ₙ√ : (n : ℕ) (a b a' b' : ℝ₊)
  → (a<b : fst a <ᵣ fst b) → (a'<b' : fst a' <ᵣ fst b')
  → (a≤a' : fst a ≤ᵣ fst a') →  (b≤b' : fst b ≤ᵣ fst b') →
  ((fst (root (1+ n) b') -ᵣ fst (root (1+ n) a'))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
      ≤ᵣ
  ((fst (root (1+ n) b) -ᵣ fst (root (1+ n) a))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a<b ))
slope-monotone-ₙ√ n a b a' b' a<b a'<b' a≤a' b≤b' =
  fst (x/y≤x'/y'≃y'/x'≤y/x _ _ _ _) $
   subst2 _≤ᵣ_
    ((cong₂ _·ᵣ_ (cong₂ _-ᵣ_
      (cong fst (Iso.rightInv (nth-pow-root-iso (1+ n)) _))
     (cong fst (Iso.rightInv (nth-pow-root-iso (1+ n)) _))) refl))
    (cong₂ _·ᵣ_ (cong₂ _-ᵣ_
     (cong fst (Iso.rightInv (nth-pow-root-iso (1+ n)) _))
     (cong fst (Iso.rightInv (nth-pow-root-iso (1+ n)) _))) refl)
    $ slopeMonotone^ (suc n)
     ((root (1+ n) a)) ((root (1+ n) b)) ((root (1+ n) a')) ((root (1+ n) b'))
    (ₙ√-StrictMonotone (1+ n) a<b)
      (ₙ√-StrictMonotone (1+ n) a'<b')
       (ₙ√-Monotone {a} {a'} (1+ n) a≤a')
       ((ₙ√-Monotone {b} {b'} (1+ n) b≤b'))


·-limℙ : ∀ P x f g F G
        → at x limitOfℙ P , f is F
        → at x limitOfℙ P , g is G
        → at x limitOfℙ P , (λ r x₁ x₂ → f r x₁ x₂ ·ᵣ g r x₁ x₂) is (F ·ᵣ G)
·-limℙ P x f g F G fL gL ε =
  PT.map3 w (fL (ε'f)) (gL (ε'g)) (gL 1)

 where

 ε'f : ℝ₊
 ε'f = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ G ,
          isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G)))

 ε'g : ℝ₊
 ε'g = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ F ,
          isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F)))


 w : _
 w (δ , p) (δ' , p') (δ'' , p'') = δ* , ww

  where

   f·g : ∀ r → _ → _ → ℝ
   f·g r x₁ x₂ = f r x₁ x₂ ·ᵣ g r x₁ x₂

   δ* : ℝ₊
   δ* = minᵣ₊ (minᵣ₊ δ δ') δ''

   ww : ∀ (r : ℝ) (r∈ : r ∈ P) (x＃r : x ＃ r) →
          absᵣ (x -ᵣ r) <ᵣ fst δ* →
          absᵣ (F ·ᵣ G -ᵣ (f·g) r r∈ x＃r) <ᵣ fst ε
   ww r r∈ x＃r x₁ = subst2 _<ᵣ_
        (cong absᵣ (sym L𝐑.lem--065))
        yy
        (isTrans≤<ᵣ _ _ _
          ((absᵣ-triangle _ _) )
          (<ᵣMonotone+ᵣ _ _ _ _
            (isTrans≡<ᵣ _ _ _
              (·absᵣ _ _)
              (<ᵣ₊Monotone·ᵣ _ _ _ _
              (0≤absᵣ _) (0≤absᵣ _) gx< u))
              (isTrans≡<ᵣ _ _ _ (·absᵣ _ _)
                (<ᵣ₊Monotone·ᵣ _ _ _ _
              ((0≤absᵣ F)) (0≤absᵣ _)
               (subst (_<ᵣ (1 +ᵣ (absᵣ F)))
                (+IdL _)
                 (<ᵣ-+o (rat 0) (rat 1) (absᵣ F) decℚ<ᵣ?)) u'))))


     where
      x₁' = isTrans<≤ᵣ _ _ _ x₁
                 (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ _ _))
      x₁'' = isTrans<≤ᵣ _ _ _ x₁
                 (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ' _ _))
      x₁''' = isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ' _ _)
      u = p r r∈ x＃r x₁'
      u' = p' r r∈ x＃r x₁''
      u'' = p'' r r∈ x＃r x₁'''
      gx< : absᵣ (g r r∈ x＃r) <ᵣ 1 +ᵣ absᵣ G
      gx< =
         subst (_<ᵣ (1 +ᵣ absᵣ G))
            (cong absᵣ (sym (L𝐑.lem--035)))

           (isTrans≤<ᵣ _ _ _
             (absᵣ-triangle ((g r r∈ x＃r) -ᵣ G) G)
              (<ᵣ-+o _ 1 (absᵣ G)
                (subst (_<ᵣ 1) (minusComm-absᵣ _ _) u'')))
      0<1+g = <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G)
      0<1+f = <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F)

      yy : _ ≡ _
      yy =
        (cong₂ _+ᵣ_
            (cong ((1 +ᵣ absᵣ G) ·ᵣ_)
              (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
                (invℝ≡ _ _ _)
               ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
              (invℝ (1 +ᵣ absᵣ G)
                  (inl (isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) 0<1+g)))) ∙
              ·ᵣAssoc _ _ _)
            (cong ((1 +ᵣ absᵣ F) ·ᵣ_)
              (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
               (invℝ≡ _ _ _)
               ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
              (invℝ (1 +ᵣ absᵣ F)
                  (inl (isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) 0<1+f)))) ∙
               ·ᵣAssoc _ _ _) ∙
            sym (·DistR+ _ _ (fst (ε ₊／ᵣ₊ 2)))
             ∙∙ cong {y = 2} (_·ᵣ (fst (ε ₊／ᵣ₊ 2)))
                             (cong₂ _+ᵣ_
                                 (x·invℝ[x] (1 +ᵣ absᵣ G)
                                   (inl (isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) 0<1+g)))
                                 (x·invℝ[x] (1 +ᵣ absᵣ F)
                                   (inl (isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) 0<1+f)))
                                   ∙ +ᵣ-rat _ _
                                )
                        ∙∙ ·ᵣComm 2 (fst (ε ₊／ᵣ₊ 2))  ∙
                          [x/y]·yᵣ (fst ε) _ (inl _))


IsContinuousLimΔℙ : ∀ P f x x∈ → IsContinuousWithPred P f →
                    at 0 limitOfℙ (P ∘S (x +ᵣ_))  ,
                     (λ Δx x∈ _ → f (x +ᵣ Δx) x∈) is (f x x∈)
IsContinuousLimΔℙ P f x x∈ cx =
  let z = IsContinuousLimℙ (P ∘S (x +ᵣ_)) _ 0
           (subst (fst ∘ P) (sym (+IdR _)) x∈)
            (IsContinuousWP∘ _ _ _ _ (λ _ x → x)
              cx (AsContinuousWithPred _ _ (IsContinuous+ᵣL x)))
  in subst2 (at (rat [ pos zero / 1+ zero ]) limitOfℙ (P ∘S (x +ᵣ_))  ,_is_)
         refl (cong₂ f ((+IdR _)) (toPathP ((snd (P _)) _ _ ))) z


chainRuleIncrℙ : ∀ x f f'gx g g'x
        → (gPos : ∀ x x∈ → 0 <ᵣ g x x∈)
        → (∀ x x∈ y y∈ → x <ᵣ y → g x x∈ <ᵣ g y y∈)
        → IsContinuousWithPred pred0< g
        → derivativeOfℙ pred0< , g at x is g'x
         → derivativeOfℙ pred0< , f at (g (fst x) (snd x) , gPos _ _) is f'gx
        → derivativeOfℙ pred0< ,
           (λ r r∈ → f (g r r∈) (gPos _ _)) at x is (f'gx ·ᵣ g'x)

chainRuleIncrℙ x₊@(x , 0<x) f f'gx g g'x gPos incrG gC gD fD =

  let z = ·-limℙ _ _ _ _ _ _ w gD
  in subst (at (rat [ pos zero / 1+ zero ])
       limitOfℙ (pred0< ∘S (x +ᵣ_)) ,_is (f'gx ·ᵣ g'x))
      (funExt₃ λ x₁ y z₁ → sym (x/y=x/z·z/y _ _ _ _ _))
       z


 where
 0#g : ∀ h → ∀ h∈ → (0＃h : 0 ＃ h) → 0 ＃ (g (x +ᵣ h) h∈ -ᵣ g x 0<x)
 0#g h h∈ =
   ⊎.map ((x<y→0<y-x _ _ ∘S incrG _ _ _ _)
           ∘S subst (_<ᵣ (x +ᵣ h)) (+IdR x) ∘S <ᵣ-o+ _ _ x)
            (((x<y→x-y<0 _ _ ∘S incrG _ _ _ _)
           ∘S subst ((x +ᵣ h) <ᵣ_) (+IdR x) ∘S <ᵣ-o+ _ _ x))

 w' :   ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
        (∀ h h∈ 0＃h →
           absᵣ (0 -ᵣ h) <ᵣ fst δ →
             absᵣ (f'gx -ᵣ ((f (g (x) 0<x  +ᵣ h) h∈ -ᵣ f (g x 0<x) (gPos x 0<x))
           ／ᵣ[ (h) , 0＃h ])) <ᵣ fst ε)

 w' = fD

 w : at 0 limitOfℙ _ ,
        (λ h h∈ 0＃h → (f (g (x +ᵣ h) h∈) (gPos _ _) -ᵣ f (g x 0<x) (gPos _ _))
           ／ᵣ[ (g (x +ᵣ h) h∈ -ᵣ g x 0<x) , 0#g h h∈ 0＃h ]) is f'gx
 w ε =
   PT.rec squash₁
     (λ (δ , X) →
         PT.map  (map-snd
            λ X* r r∈ ＃r <a →
              let Δg<δ = isTrans≡<ᵣ _ _ _
                     (cong absᵣ (+IdL _ ∙ -[x-y]≡y-x _ _))
                    (X* r r∈ ＃r <a)
                  z = X ((g (x +ᵣ r) r∈ -ᵣ g x 0<x))
                      (subst-∈ pred0< (sym L𝐑.lem--05 ) (gPos _ _))
                       (0#g _ _ ＃r) Δg<δ
              in isTrans≡<ᵣ _ _ _
                   (cong (λ xx →
                       absᵣ (f'gx -ᵣ
                         ((xx -ᵣ f (g x 0<x) (gPos x 0<x))
                          ／ᵣ[ g (x +ᵣ r) r∈ -ᵣ g x 0<x , 0#g r r∈ ＃r ])
                       ))
                     (cong (uncurry f)
                       (Σ≡Prop (snd ∘ pred0<) (sym L𝐑.lem--05))) )
                   z)
           (IsContinuousLimΔℙ _ _ x 0<x gC δ))

     (w' ε)


preMapLimitPos : ∀ P Q x x' f g y →
   (u : ∀ r r∈ ＃r →  g r r∈ ＃r ∈ Q)
   (v : ∀ r r∈ ＃r → x' ＃ g r r∈ ＃r)
  → at x  limitOfℙ P , g is x'
  → at x' limitOfℙ Q , f is y
  → at x  limitOfℙ P ,
   (λ r r∈ ＃r → f (g r r∈ ＃r) (u _ _ _) (v _ _ _ )) is y
preMapLimitPos _ _ _ _ _ _ _ _ _ gL =
  PT.rec squash₁
    (λ (δ , X) →
      PT.rec squash₁
       (λ (δ' , X') →
         ∣ δ' , (λ _ _ _ uu →
           let vv = X' _ _ _ uu
           in X _ _ _ vv) ∣₁)
       (gL δ)) ∘_


mapLimitPos' : ∀ x P Q f g y y∈ → (f∈ : ∀ r r∈ x＃ → f r r∈ x＃ ∈ Q)
  → IsContinuousWithPred Q g
  → at x limitOfℙ P , f is y
  → at x limitOfℙ P , (λ r r∈ x＃ → g (f r r∈ x＃) (f∈ _ _ _)) is
      g y y∈
mapLimitPos' x P Q f g y y∈ f∈ gC fL (ε , 0<ε) =
    PT.rec squash₁
    (λ (q , 0<q , q<ε) →
     let q₊ = (q , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<q))
     in PT.rec squash₁
         (λ (δ' , D') →
            PT.rec squash₁
              (λ (δ , D) →
                ∣ minᵣ₊ (ℚ₊→ℝ₊ δ') δ ,
                    (λ r r∈ x＃r x-r<δ →
                       let uu = D r r∈ x＃r
                                  (isTrans<≤ᵣ _ _ _ x-r<δ
                                    (min≤ᵣ' (rat (fst δ')) _))
                           uu' = D' (f r r∈ x＃r) (f∈ r r∈ x＃r)
                                 (invEq (∼≃abs<ε _ _ _) uu)
                       in  isTrans<ᵣ _ _ _
                            (fst (∼≃abs<ε _ _ _) uu')
                            q<ε) ∣₁)
              (fL (ℚ₊→ℝ₊ (δ'))))
         (gC y (q₊) y∈))
   (denseℚinℝ _ _ 0<ε)



invDerivativeℙPos-temp : ∀ x f f' f'Pos (fPos : ∀ x 0<x → 0 <ᵣ f x 0<x )
  → (isEquivF : isEquiv {A = ℝ × Unit} {B = ℝ₊}
       λ x → f (fst x) (snd x) , fPos (fst x) (snd x) )
   → (∀ x y → fst x <ᵣ fst y →
       fst (invEq (_ , isEquivF) x) <ᵣ fst (invEq (_ , isEquivF) y))
   → (∀ x y → fst x <ᵣ fst y →
       (f (fst x) (snd x)) <ᵣ (f (fst y) (snd y)))
       → IsContinuousWithPred ⊤Pred f
  → IsContinuousWithPred pred0< (λ x x∈ → fst (invEq (_ , isEquivF) (x , x∈)))
  → derivativeOfℙ ⊤Pred , f at x is f'
  → derivativeOfℙ pred0< , (λ r 0<r →
       fst (invEq (_ , isEquivF) (r , 0<r)))
         at f (fst x) (snd x) , fPos _ _
       is fst (invℝ₊ (f' , f'Pos))
invDerivativeℙPos-temp x f f' f'Pos fPos isEquivF incrG incrF  fC gC dF =
  subst
    (uncurry (at (rat [ pos zero / 1+ zero ]) limitOfℙ_,_is
      fst (invℝ₊ (f' , f'Pos)) ))
    (ΣPathP (refl , funExt₃
      pp)) d''
  where

  e : _ ≃ _
  e = (_ , isEquivF)

  g = invEq e

  y = f (fst x) (snd x)



  h'' : (r : ℝ) → r ∈ (λ x₁ → pred0< (y +ᵣ x₁)) → ℝ
  h'' h h∈  = fst (g (_ , h∈)) -ᵣ fst x


  h' : (r : ℝ) → r ∈ (λ x₁ → pred0< (y +ᵣ x₁)) → 0 ＃ r → ℝ
  h' h h∈ _ = h'' h h∈



  uu : (r : ℝ) (r∈ : r ∈ (λ x₂ → pred0< (y +ᵣ x₂))) (＃r : 0 ＃ r) →
        h' r r∈ ＃r ∈ (λ x₂ → ⊤Pred (x .fst +ᵣ x₂))
  uu _ r∈ _ = tt

  vv : (r : ℝ) (r∈ : r ∈ (λ x₂ → pred0< (y +ᵣ x₂))) (＃r : 0 ＃ r) →
        0 ＃ h' r r∈ ＃r
  vv r r∈ = ⊎.elim
    (inl ∘ λ p → x<y→0<y-x _ _ (isTrans≡<ᵣ _ _ _
     (sym (cong fst (retEq e _)))
     (incrG (y , fPos _ _) _ (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
       ((<ᵣ-o+ 0 _ y p))))) )
    (inr ∘ λ p →
      (x<y→x-y<0 _ _ (isTrans<≡ᵣ _ _ _
       (incrG _ _ (isTrans<≡ᵣ _ _ _ (<ᵣ-o+ _ 0 y p) (+IdR _)))
         (cong fst (retEq e _)))) )

  h-lim : at 0 limitOfℙ (λ x₁ → pred0< (y +ᵣ x₁)) , (λ h h∈ _ → h'' h h∈) is 0
  h-lim = subst (at _ limitOfℙ _ , h' is_) (𝐑'.+InvR' _ _
      (cong (fst ∘ invEq e) (ℝ₊≡ (+IdR y)) ∙ cong fst (retEq e _)))
    (IsContinuousLimℙ (λ x₁ → pred0< (y +ᵣ x₁)) h'' 0
      (isTrans<≡ᵣ _ _ _ (fPos (fst x) (snd x)) (sym (+IdR _)))

      (IsContinuousWP∘ ⊤Pred _ _ _ _
        (AsContinuousWithPred _ _ (IsContinuous+ᵣR (-ᵣ fst x)))
          (IsContinuousWP∘ _ _
               _ _ _ gC
           (AsContinuousWithPred _ _ (IsContinuous+ᵣL y ))))
           )

  d' : at 0 limitOfℙ (λ x₁ → pred0< (y +ᵣ x₁)) ,
        (λ r r∈ ＃r →
           differenceAtℙ ⊤Pred f (x .fst) (h' r r∈ ＃r) (vv r r∈ ＃r) (x .snd)
           (uu r r∈ ＃r))
        is f'
  d' = preMapLimitPos _ _ _ _ _
     h'
     f'
     uu vv
      h-lim dF


  h''-pos : (r : ℝ) (r∈ : r ∈ (λ x₁ → pred0< (f (fst x) (snd x) +ᵣ x₁)))
              (x＃ : 0 ＃ r) →
             0 <ᵣ differenceAtℙ ⊤Pred f (x .fst) (h' r r∈ x＃)
               _ (x .snd) _
  h''-pos r r∈ x＃ = incr→0<differenceAtℙ _ _ _ _ _ _ _
   λ _ _ _ _ → incrF _ _


  d'' :
   at 0 limitOfℙ pred0< ∘S (y +ᵣ_) ,
       (λ r z z₁ →
          invℝ' .fst
          (differenceAtℙ ⊤Pred f (x .fst) (h' r z z₁) _ (x .snd) _)
          (h''-pos r z z₁))
         is (fst (invℝ₊ (f' , f'Pos)) )
  d'' = mapLimitPos' _ _ _ _ _ f'
        f'Pos
        h''-pos
        (snd invℝ')
        d'


  pp : ∀ x' u v → fst (invℝ₊ (_ , _))
                   ≡ differenceAtℙ pred0< _
                      _ x' v (fPos (fst x) (snd x)) u
  pp x' u v =
    cong {x = _ , uuu} (fst ∘ invℝ₊)
       (ℝ₊≡ (sym (absᵣPos _ uuu) ∙ ·absᵣ _ _))
      ∙ (cong fst (invℝ₊· (absᵣ _ , 0＃→0<abs _ zz)
          (_ , 0＃→0<abs _ (invℝ0＃ _ _))) ∙
       cong₂ _·ᵣ_
          (cong (fst ∘ invℝ₊) (ℝ₊≡ (cong absᵣ zzz))
            ∙ sym (absᵣ-invℝ _ _))
          (sym (absᵣ-invℝ _ _)
           ∙ cong absᵣ (invℝInvol _ _  ∙
            cong₂ _-ᵣ_ refl (cong fst (sym (retEq e _))))
             ))
       ∙ ·ᵣComm _ _ ∙ sym (·absᵣ _ _) ∙ (absᵣPos _
        (incr→0<differenceAtℙ _ _ _ _ _ _ _
         λ _ _ _ _ → incrG _ _))
   where -- ·absᵣ _ _
   uuu = _

   qq : f (x .fst +ᵣ h' x' u v) (uu x' u v) ≡ y +ᵣ x'
   qq = cong₂ f (L𝐑.lem--05) (toPathP refl)
         ∙ cong fst (secEq e _)


   zzz : f (x .fst +ᵣ h' x' u v) (uu x' u v) -ᵣ f (x .fst) (x .snd)
              ≡ x'
   zzz = cong (_-ᵣ f (x .fst) (x .snd)) qq ∙ L𝐑.lem--063


   zz : 0 ＃ ((f (x .fst +ᵣ h' x' u v) (uu x' u v)) -ᵣ f (x .fst) (x .snd))
   zz = subst (0 ＃_) (sym zzz) v


invDerivativeℙ : ∀ x (f : ℝ → ℝ) f' f'Pos (fPos : ∀ x → 0 <ᵣ f x)
  → (isEquivF : isEquiv {A = ℝ} {B = ℝ₊} λ x → f x  , fPos x)
   → (∀ x y → fst x <ᵣ fst y →
       (invEq (_ , isEquivF) x) <ᵣ (invEq (_ , isEquivF) y))
   → (∀ x y → x <ᵣ y →  (f x) <ᵣ (f y)) → IsContinuous f
  → IsContinuousWithPred pred0< (λ x x∈ → (invEq (_ , isEquivF) (x , x∈)))
  → derivativeOf f at x is f'
  → derivativeOfℙ pred0< , (λ r 0<r →
        (invEq (_ , isEquivF) (r , 0<r)))
         at f x , fPos _
       is fst (invℝ₊ (f' , f'Pos))
invDerivativeℙ x f f' f'Pos fPos isEquivF incrG incrF  fC gC dF =
 invDerivativeℙPos-temp
   (x , tt)
   (λ x _ → f x)
   f'
   f'Pos
   (λ v _ → fPos v)
   (snd (isoToEquiv rUnit×Iso ∙ₑ (_ , isEquivF)))
   (λ x₁ y x₂ → incrG _ _ x₂)
   (λ x₁ y x₂ → incrF _ _ x₂)
   (AsContinuousWithPred _ _ fC)
   gC
   (as-derivativeOfℙ _ _ _ _ _ dF)


invDerivativeℙPos : ∀ x f f' f'Pos (fPos : ∀ x 0<x → 0 <ᵣ f x 0<x )
  → (isEquivF : isEquiv {A = ℝ₊} {B = ℝ₊}
       λ x → f (fst x) (snd x) , fPos (fst x) (snd x) )
   → (∀ x y → fst x <ᵣ fst y →
       fst (invEq (_ , isEquivF) x) <ᵣ fst (invEq (_ , isEquivF) y))
   → (∀ x y → fst x <ᵣ fst y →
       (f (fst x) (snd x)) <ᵣ (f (fst y) (snd y)))
       → IsContinuousWithPred pred0< f
  → IsContinuousWithPred pred0< (λ x x∈ → fst (invEq (_ , isEquivF) (x , x∈)))
  → derivativeOfℙ pred0< , f at x is f'
  → derivativeOfℙ pred0< , (λ r 0<r →
       fst (invEq (_ , isEquivF) (r , 0<r)))
         at f (fst x) (snd x) , fPos _ _
       is fst (invℝ₊ (f' , f'Pos))
invDerivativeℙPos x f f' f'Pos fPos isEquivF incrG incrF  fC gC dF =
  subst
    (uncurry (at (rat [ pos zero / 1+ zero ]) limitOfℙ_,_is
      fst (invℝ₊ (f' , f'Pos)) ))
    (ΣPathP (refl , funExt₃
      pp)) d''
  where


  e : _ ≃ _
  e = (_ , isEquivF)

  g = invEq e

  y = f (fst x) (snd x)



  h'' : (r : ℝ) → r ∈ (λ x₁ → pred0< (y +ᵣ x₁)) → ℝ
  h'' h h∈  = fst (g (_ , h∈)) -ᵣ fst x


  h' : (r : ℝ) → r ∈ (λ x₁ → pred0< (y +ᵣ x₁)) → 0 ＃ r → ℝ
  h' h h∈ _ = h'' h h∈



  uu : (r : ℝ) (r∈ : r ∈ (λ x₂ → pred0< (y +ᵣ x₂))) (＃r : 0 ＃ r) →
        h' r r∈ ＃r ∈ (λ x₂ → pred0< (x .fst +ᵣ x₂))
  uu _ r∈ _ =
   isTrans<≡ᵣ _ _ _ (snd (g (_ , r∈)))
     (sym L𝐑.lem--05)

  vv : (r : ℝ) (r∈ : r ∈ (λ x₂ → pred0< (y +ᵣ x₂))) (＃r : 0 ＃ r) →
        0 ＃ h' r r∈ ＃r
  vv r r∈ = ⊎.elim
    (inl ∘ λ p → x<y→0<y-x _ _ (isTrans≡<ᵣ _ _ _
     (sym (cong fst (retEq e _)))
     (incrG (y , fPos _ _) _ (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
       ((<ᵣ-o+ 0 _ y p))))) )
    (inr ∘ λ p →
      (x<y→x-y<0 _ _ (isTrans<≡ᵣ _ _ _
       (incrG _ _ (isTrans<≡ᵣ _ _ _ (<ᵣ-o+ _ 0 y p) (+IdR _)))
         (cong fst (retEq e _)))) )


  h-lim : at 0 limitOfℙ (λ x₁ → pred0< (y +ᵣ x₁)) , (λ h h∈ _ → h'' h h∈) is 0
  h-lim = subst (at _ limitOfℙ _ , h' is_) (𝐑'.+InvR' _ _
      (cong (fst ∘ invEq e) (ℝ₊≡ (+IdR y)) ∙ cong fst (retEq e _)))
    (IsContinuousLimℙ (λ x₁ → pred0< (y +ᵣ x₁)) h'' 0
      (isTrans<≡ᵣ _ _ _ (fPos (fst x) (snd x)) (sym (+IdR _)))

      (IsContinuousWP∘ ⊤Pred _ _ _ _
        (AsContinuousWithPred _ _ (IsContinuous+ᵣR (-ᵣ fst x)))
          (IsContinuousWP∘ _ _
               _ _ _ gC
           (AsContinuousWithPred _ _ (IsContinuous+ᵣL y ))))
           )

  d' : at 0 limitOfℙ (λ x₁ → pred0< (y +ᵣ x₁)) ,
        (λ r r∈ ＃r →
           differenceAtℙ pred0< f (x .fst) (h' r r∈ ＃r) (vv r r∈ ＃r) (x .snd)
           (uu r r∈ ＃r))
        is f'
  d' = preMapLimitPos _ _ _ _ _
     h'
     f'
     uu vv
      h-lim dF


  h''-pos : (r : ℝ) (r∈ : r ∈ (λ x₁ → pred0< (f (fst x) (snd x) +ᵣ x₁)))
              (x＃ : 0 ＃ r) →
             0 <ᵣ differenceAtℙ pred0< f (x .fst) (h' r r∈ x＃)
               _ (x .snd) _
  h''-pos r r∈ x＃ = incr→0<differenceAtℙ _ _ _ _ _ _ _
   λ _ _ _ _ → incrF _ _


  d'' :
   at 0 limitOfℙ pred0< ∘S (y +ᵣ_) ,
       (λ r z z₁ →
          invℝ' .fst
          (differenceAtℙ pred0< f (x .fst) (h' r z z₁) _ (x .snd) _)
          (h''-pos r z z₁))
         is (fst (invℝ₊ (f' , f'Pos)) )
  d'' = mapLimitPos' _ _ _ _ _ f'
        f'Pos
        h''-pos
        (snd invℝ')
        d'


  pp : ∀ x' u v → fst (invℝ₊ (_ , _))
                   ≡ differenceAtℙ pred0< _
                      _ x' v (fPos (fst x) (snd x)) u
  pp x' u v =
    cong {x = _ , uuu} (fst ∘ invℝ₊)
       (ℝ₊≡ (sym (absᵣPos _ uuu) ∙ ·absᵣ _ _))
      ∙ (cong fst (invℝ₊· (absᵣ _ , 0＃→0<abs _ zz)
          (_ , 0＃→0<abs _ (invℝ0＃ _ _))) ∙
       cong₂ _·ᵣ_
          (cong (fst ∘ invℝ₊) (ℝ₊≡ (cong absᵣ zzz))
            ∙ sym (absᵣ-invℝ _ _))
          (sym (absᵣ-invℝ _ _)
           ∙ cong absᵣ (invℝInvol _ _  ∙
            cong₂ _-ᵣ_ refl (cong fst (sym (retEq e _))))
             ))
       ∙ ·ᵣComm _ _ ∙ sym (·absᵣ _ _) ∙ (absᵣPos _
        (incr→0<differenceAtℙ _ _ _ _ _ _ _
         λ _ _ _ _ → incrG _ _))
   where -- ·absᵣ _ _
   uuu = _

   qq : f (x .fst +ᵣ h' x' u v) (uu x' u v) ≡ y +ᵣ x'
   qq = cong₂ f (L𝐑.lem--05) (toPathP (isProp<ᵣ _ _ _ _))
         ∙ cong fst (secEq e _)


   zzz : f (x .fst +ᵣ h' x' u v) (uu x' u v) -ᵣ f (x .fst) (x .snd)
              ≡ x'
   zzz = cong (_-ᵣ f (x .fst) (x .snd)) qq ∙ L𝐑.lem--063


   zz : 0 ＃ ((f (x .fst +ᵣ h' x' u v) (uu x' u v)) -ᵣ f (x .fst) (x .snd))
   zz = subst (0 ＃_) (sym zzz) v

derivative-n√ : ∀ x n →
        derivativeOfℙ pred0< , curry (fst ∘ root (1+ n))
                  at x is fst
                   (invℝ₊ (fromNat (suc n) ₊·ᵣ (root (1+ n) x ₊^ⁿ n)))
derivative-n√ x@(x' , 0<x') n = subst2
  (derivativeOfℙ pred0< ,_at_is
   fst (invℝ₊ (fromNat (suc n) ₊·ᵣ (root (1+ n) x ₊^ⁿ n))))
   refl (secEq e x) w
 where

 e = isoToEquiv (nth-pow-root-iso (1+ n))

 y = invEq e x

 w = invDerivativeℙPos y _ _ (snd (fromNat (suc n) ₊·ᵣ (y ₊^ⁿ n)))
       (λ x₁ 0<x → snd ((x₁ , 0<x) ₊^ⁿ (suc n)))
       (snd e)
       (λ _ _ → ₙ√-StrictMonotone _)
       (λ a b  → ^ⁿ-StrictMonotone _ ℕ.zero-<-suc
         (<ᵣWeaken≤ᵣ _ _ (snd a)) ((<ᵣWeaken≤ᵣ _ _ (snd b))))
       (AsContinuousWithPred _ _ (IsContinuous^ⁿ _))
       (IsContinuousRoot _ )
       λ ε →
         PT.map (map-snd
             λ {a} X r _ → X r) (derivative-^ⁿ n (fst y) ε)

reciporalDerivative : ∀ x f f' → (fPos : ∀ x 0<x → 0 <ᵣ f x 0<x)
 → IsContinuousWithPred pred0< f
 → derivativeOfℙ pred0< , f at x is f'
 → derivativeOfℙ pred0< , (λ r 0<r → fst (invℝ₊ (f r 0<r , fPos _ _)))
     at x is (-ᵣ (f' ／ᵣ₊ ((f (fst x) (snd x) , fPos _ _ ) ₊·ᵣ
                       (f (fst x) (snd x) , fPos _ _ ))))
reciporalDerivative (x , x∈) f f' fPos fC d =
  subst2
         {x = pp₀}
         {y = pp₁}
         {z = [1/f]'} (at 0 limitOfℙ pred0< ∘S (x +ᵣ_) ,_is_)
         pp
        (cong ((f' ·ᵣ_) ∘ -ᵣ_ ∘ fst ∘ invℝ₊)
          (ℝ₊≡ {_ , ℝ₊· (f x x∈ , fPos x x∈) (f (x +ᵣ 0) x+0∈ , fPos _ _)}
            {_ , _} (cong (f x x∈  ·ᵣ_)
              (cong₂ f (+IdR x) (toPathP (isProp<ᵣ _ _ _ _)))))
           ∙ ·-ᵣ _ _)
            w
 where
 f⁻² = -ᵣ (fst (invℝ₊ ((f x x∈ , fPos _ _ ) ₊·ᵣ
                       (f x x∈ , fPos _ _ ))))

 [1/f]' = _

 x+0∈ = (subst-∈ pred0< (sym (+IdR _)) x∈)

 f⁻²-lim : at 0 limitOfℙ (λ x₁ → pred0< (x +ᵣ x₁)) ,
            (λ x' x'∈ _ →
               -ᵣ (fst
               (invℝ₊
                ((f x x∈ , fPos x x∈) ₊·ᵣ (f (x +ᵣ x') x'∈ , fPos (x +ᵣ x') x'∈)))))
            is (-ᵣ (fst (invℝ₊ ((f x x∈ , fPos _ _ ) ₊·ᵣ
                       (f (x +ᵣ 0) x+0∈
                        , fPos _ _ )))))
 f⁻²-lim = IsContinuousLimℙ _ _ 0 (x+0∈)
                (IsContinuousWP∘ ⊤Pred _ _ _ _
                  (AsContinuousWithPred _ _ IsContinuous-ᵣ)
                    (IsContinuousWP∘ _ _ _ _ _
                       (snd invℝ')
                        (IsContinuousWP∘ ⊤Pred _ _ _ _
                          (AsContinuousWithPred _ _ (IsContinuous·ᵣL _))
                           (IsContinuousWP∘ _ _ _ _ _
                             fC
                             (AsContinuousWithPred _ _ (IsContinuous+ᵣL x))))))
 pp₀ = _
 pp₁ = _

 pp : pp₀ ≡ pp₁
 pp = funExt₃ λ _ _ _ → 𝐑.·CommAssocr _ _ _ ∙
   cong (_·ᵣ invℝ _ _) ((·-ᵣ _ _ ∙
     cong (-ᵣ_)
       (cong₂ _·ᵣ_ refl (cong fst (invℝ₊· _ _))
        ∙ 𝐑'.·DistL- (f (x +ᵣ _) _) (f x x∈) _ ∙
        cong₂ _-ᵣ_ (·ᵣComm _ _ ∙ [x/₊y]·yᵣ _ _)
         (·ᵣComm _ _ ∙ cong (_·ᵣ f x x∈) (·ᵣComm _ _) ∙
           [x/₊y]·yᵣ _ _)) )
     ∙ -[x-y]≡y-x _ _)

 w : at 0 limitOfℙ pred0< ∘S (x +ᵣ_) , pp₀ is [1/f]'
 w = ·-limℙ (pred0< ∘S (x +ᵣ_)) 0 _ _ _ _ d f⁻²-lim


derivative-^ℤ : ∀ x k → ¬ (k ≡ 0) →
   derivativeOfℙ pred0< , curry (fst ∘S (_^ℤ k)) at x is
     (rat [ k / 1 ] ·ᵣ fst (x ^ℤ (k ℤ.- 1 )))
derivative-^ℤ (x , 0<x) (pos zero) ¬k=0 = ⊥.rec (¬k=0 refl)
derivative-^ℤ (x , 0<x) (pos (suc n)) ¬k=0  ε =
  PT.map (map-snd
    λ {a} X r _ → X r) (derivative-^ⁿ n x ε)
derivative-^ℤ x₊@(x , 0<x) (ℤ.negsuc n) _ =
  let h = reciporalDerivative (x , 0<x)
           (λ r x₂ → fst ((r , x₂) ^ℤ pos (suc n))) _
             (λ r x₂ → snd ((r , x₂) ^ℤ pos (suc n)))
             (AsContinuousWithPred _ _ (IsContinuous^ⁿ _))
             (λ ε → PT.map (map-snd
              λ {a} X r _ → X r)
              (derivative-^ⁿ n x ε))
  in subst (derivativeOfℙ pred0< , _ at _ is_)
      (cong -ᵣ_ (sym (·ᵣAssoc _ _ _)) ∙
        sym (-ᵣ· _ _) ∙
         cong₂ (_·ᵣ_)
         (-ᵣ-rat _)
         (cong ((x ^ⁿ n) ·ᵣ_)
           (cong fst (cong invℝ₊ (ℝ₊≡ (sym (·ᵣAssoc _ _ _) ∙
             cong ((x ^ⁿ n) ·ᵣ_) (·ᵣComm _ _)))
              ∙ invℝ₊·  (x₊ ₊^ⁿ n) (x₊ ₊^ⁿ (suc (suc n)))))
           ∙ ·ᵣAssoc _ _ _ ∙ 𝐑'.·IdL' _ _ (x·invℝ₊[x] _)
         )) h

[0/n]=[0/m] : ∀ n m → [ 0 / n ] ≡ [ 0 / m ]
[0/n]=[0/m] n m = eq/ _ _ refl

0#[n/m]→n≠0 : ∀ n m → 0 ℚ.# [ n , (1+ m) ] → ¬ n ≡ 0
0#[n/m]→n≠0 n m x n=0 =
 let x' = subst (0 ℚ.#_) (cong [_/ (1+ m) ] n=0 ∙ [0/n]=[0/m] _ _) x
 in ℚ.isIrrefl# 0 x'


derivative-^ℚ : ∀ x q → 0 ℚ.# q →
   derivativeOfℙ pred0< , curry (fst ∘S (_^ℚ q)) at x is
     (rat q ·ᵣ fst (x ^ℚ (q ℚ.- 1)))

derivative-^ℚ x = SQ.ElimProp.go w
  where
  w : ElimProp _
  w .ElimProp.isPropB _ = isPropΠ2 λ _ _ → squash₁
  w .ElimProp.f ( n , (1+ m) ) 0#q =
    subst (derivativeOfℙ pred0< , _ at x is_)
        (cong₂ (_·ᵣ_) refl (cong fst (invℝ₊· _ _))
          ∙ L𝐑.lem--086
          ∙ cong₂ (_·ᵣ_) (cong (rat [ n / 1 ] ·ᵣ_)
             (cong
               {x = fromNat (suc m)}
               {y = ℚ₊→ℝ₊ (fromNat (suc m))}
               (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ m)
               ∙ invℝ₊-rat (fromNat (suc m)))
           ∙ sym (rat·ᵣrat _ _) ∙ cong rat (invℚ₊-[/] n m))
            (cong₂ (_·ᵣ_) refl (cong fst (sym (invℝ₊^ℚ _ [ pos m / 1+ m ]))
               ∙ cong fst (sym (^ℚ-minus' x _)))
             ∙ cong fst (^ℚ-+ _ [ _ / 1+ m ] _
              ∙ cong (x ^ℚ_) (
                ℚ.n/k-m/k _ _ _ ∙
                  cong [_/ 1+ m ] (sym (ℤ.+Assoc _ _ _)
                    ∙ cong {y = ℤ.- pos (suc m)} (n ℤ.+_)
                     (sym (ℤ.negsuc+ 0 m))) ∙ sym (ℚ.n/k-m/k n (pos (suc m)) (1+ m))
                   ∙ cong (ℚ._-_ [ n / 1+ m ] ) (ℚ.k/k _)))))
        ww -- sym (^ℚ-minus' x [ pos m / 1+ m ])
   where
   ww : derivativeOfℙ pred0< , curry (fst ∘S (_^ℚ [ n / (1+ m) ])) at x is
              ((rat [ n / 1 ] ·ᵣ fst (root (1+ m) x ^ℤ (n ℤ.- 1 ))) ·ᵣ
                fst (invℝ₊ (fromNat (suc m) ₊·ᵣ (root (1+ m) x ₊^ⁿ m))))
   ww = chainRuleIncrℙ _ _ _ _ _ _
          (λ x₁ x∈ y y∈ x₂ →
            ₙ√-StrictMonotone {x₁ , x∈} {y , y∈} (1+ m) x₂ )
          (IsContinuousRoot (1+ m))
         (derivative-n√ x m)
         (derivative-^ℤ _ n (0#[n/m]→n≠0 _ _ 0#q))



opaque
 unfolding invℝ
 bernoulli's-ineq-^ℚⁿ : ∀ x n → 1 ℚ.< x
  →
   ((fromNat (suc (suc n))) ℚ.· (x ℚ.- 1)) ℚ.+ 1  ℚ.< (x ℚ^ⁿ (suc (suc n)))
 bernoulli's-ineq-^ℚⁿ x n 1<x =
  <ᵣ→<ℚ _ _
    (subst2 _<ᵣ_
      (cong (1 +ᵣ_) (sym (rat·ᵣrat _ _)) ∙  +ᵣComm _ _) (^ⁿ-ℚ^ⁿ _ _)
      (bernoulli's-ineq-^ℚ (ℚ₊→ℝ₊ (x ,
        ℚ.<→0< _ (ℚ.isTrans< 0 1 _ (ℚ.0<pos  _ _) 1<x)))
        (fromNat (suc (suc n))) (<ℚ→<ᵣ _ _ 1<x)
           (ℚ.<ℤ→<ℚ _ _ (invEq (ℤ.pos-<-pos≃ℕ< _ _)
             (ℕ.suc-≤-suc (ℕ.zero-<-suc {n}))))))




ℚ0≤x·ᵣx : ∀ x → 0 ℚ.≤ x ℚ.· x
ℚ0≤x·ᵣx = SQ.ElimProp.go w
  where
  w : ElimProp _
  w .ElimProp.isPropB _ = ℚ.isProp≤ _ _
  w .ElimProp.f (pos n , b) = ℚ.≤Monotone·-onNonNeg 0 [ ℤ.pos n , b ] 0 [ ℤ.pos n , b ]
    (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _)
  w .ElimProp.f (ℤ.negsuc n , b) =
    subst {x = [ ℤ.pos (suc n) , b ] ℚ.· [ ℤ.pos (suc n) , b ]}
          {y = [ ℤ.negsuc n , b ] ℚ.· [ ℤ.negsuc n , b ]}
          (0 ℚ.≤_) (cong [_/ _ ] (sym (ℤ.negsuc·negsuc _ _)))
      (ℚ.≤Monotone·-onNonNeg 0 [ ℤ.pos (suc n) , b ] 0 [ ℤ.pos (suc n) , b ]
    (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _))


0≤x·ᵣx : ∀ x → 0 ≤ᵣ x ·ᵣ x
0≤x·ᵣx = ≤Cont (IsContinuousConst 0) (cont₂·ᵣ _ _ IsContinuousId IsContinuousId)
  λ u → isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ _ _
    (ℚ0≤x·ᵣx u)) (rat·ᵣrat u u )


opaque
 unfolding invℝ
 x+1/x-bound : ∀ (x : ℝ₊) → rat [ 1 / 2 ] ≤ᵣ fst x →
    (fst x -ᵣ 1) -ᵣ (1 -ᵣ fst (invℝ₊ x))  ≤ᵣ (2 ·ᵣ (fst x -ᵣ 1)) ·ᵣ (fst x -ᵣ 1)
 x+1/x-bound x 1/2≤x =
   isTrans≡≤ᵣ _ _ _
     (λ i →  (fst x -ᵣ 1 -ᵣ (1 -ᵣ ·IdL (fst (invℝ₊ x)) (~ i))))
     (b≤c-b⇒a+b≤c _ _ _ (isTrans≡≤ᵣ _ _ _
       (-[x-y]≡y-x _ _)
       (a≤c+b⇒a-c≤b _ _ _
       (isTrans≤≡ᵣ _ _ _ (invEq (z/y≤x₊≃z≤y₊·x _ _ _) (invEq (x≤y≃0≤y-x _ _)
         (isTrans≤≡ᵣ _ _ _ h L𝐑.lem--085))) (+ᵣComm _ _)))))

  where
  h :  0  ≤ᵣ (fst x -ᵣ 1) ·ᵣ (fst x -ᵣ 1) ·ᵣ ((L𝐑.[ 2 ]r ·ᵣ x .fst) -ᵣ 1)
  h = isTrans≡≤ᵣ _ _ _ (rat·ᵣrat 0 0)
      (≤ᵣ₊Monotone·ᵣ 0 _ 0 _
        (0≤x·ᵣx _) (≤ᵣ-refl 0)
        (0≤x·ᵣx _) (fst (x≤y≃0≤y-x _ _)
         (fst (z/y≤x₊≃z≤y₊·x (fst x) 1 2) (isTrans≡≤ᵣ _ _ _
           (·IdL _ ∙ decℚ≡ᵣ?) 1/2≤x) )))


lnSeq : ℝ₊ → ℕ → ℝ
lnSeq z n =  (fst (z ^ℚ [ 1 / 2+ n ]) -ᵣ 1)  ·ᵣ fromNat (suc (suc n))


opaque
 unfolding -ᵣ_
 lnSeqMonStrictInZ : (z z' : ℝ₊)
                → fst z <ᵣ fst z'
                → ∀ n → lnSeq z n <ᵣ lnSeq z' n
 lnSeqMonStrictInZ z z' z<z' n =
   <ᵣ-·ᵣo _ _ (fromNat (suc (suc n)))
    $ <ᵣ-+o _ _ -1
      (^ℚ-StrictMonotone {z} {z'} ([ 1 / 2+ n ] , _) z<z')

 lnSeqMonInZ : (z z' : ℝ₊)
                → fst z ≤ᵣ fst z'
                → ∀ n → lnSeq z n ≤ᵣ lnSeq z' n
 lnSeqMonInZ z z' z≤z' n =
   ≤ᵣ-·ᵣo _ _ (fromNat (suc (suc n))) (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos _ _))
    $ ≤ᵣ-+o _ _ -1
      (^ℚ-Monotone {z} {z'} ([ 1 / 2+ n ] , _) z≤z')



 lnSeqCont : ∀ n → IsContinuousWithPred pred0<
              (λ z 0<z → lnSeq (z , 0<z) n)
 lnSeqCont n =  IsContinuousWP∘' pred0< _ _
      (IsContinuous∘ _ _ (IsContinuous·ᵣR _)
        ((IsContinuous+ᵣR -1))
        ) (IsContinuous^ℚ [ 1 / 2+ n ])


lnSeq' : ℝ₊ → ℕ → ℝ
lnSeq' z n = (1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ])))  ·ᵣ fromNat (suc (suc n))


lnSeq'Cont : ∀ n → IsContinuousWithPred pred0<
             (λ z 0<z → lnSeq' (z , 0<z) n)
lnSeq'Cont n =  IsContinuousWP∘' pred0< _ _
     (IsContinuous∘ _ _ (IsContinuous·ᵣR _)
       (IsContinuous∘ _ _ (IsContinuous+ᵣL 1)
        IsContinuous-ᵣ)
       ) (IsContinuous^ℚ (ℚ.- [ 1 / 2+ n ]))

lnSeq'[z]≡lnSeq[1/x] : ∀ n z → -ᵣ lnSeq' z n ≡ lnSeq (invℝ₊ z) n
lnSeq'[z]≡lnSeq[1/x] n z =  sym (-ᵣ· _ _)
  ∙ cong (_·ᵣ fromNat (suc (suc n)))
    (-[x-y]≡y-x 1 _ ∙
     cong (_-ᵣ 1)
      (cong fst (^ℚ-minus' _ _)))

lnSeq[z]≡lnSeq'[1/x] : ∀ n z → lnSeq z n ≡ -ᵣ lnSeq' (invℝ₊ z) n
lnSeq[z]≡lnSeq'[1/x] n z =
     cong (flip lnSeq n) (sym (invℝ₊Invol z))
   ∙ sym (lnSeq'[z]≡lnSeq[1/x] n (invℝ₊ z))


x^→∞ : ∀ m (ε : ℚ₊) →
         Σ[ N ∈ ℕ ]
           (∀ n → N ℕ.< n → fromNat m ℚ.< (((fst ε) ℚ.+ 1) ℚ^ⁿ n))
x^→∞ m ε =
 let (1+ N , X) = ℚ.ceilℚ₊
         (fromNat (suc m) ℚ₊· invℚ₊ ε )
 in   suc N
    , λ { zero 0< → ⊥.rec (ℕ.¬-<-zero 0<)
      ; (suc zero) <1 → ⊥.rec (ℕ.¬-<-zero (ℕ.predℕ-≤-predℕ <1))
      ; (suc (suc n)) <ssn →
       ℚ.isTrans< (fromNat m) _ _
         (subst (fromNat m ℚ.<_)
           (ℚ.·Comm _ _)
           (ℚ.isTrans< _ (fromNat (suc m)) _
             (ℚ.<ℤ→<ℚ _ _ ((ℤ.isRefl≤ {pos (suc m)})))
              (ℚ.x·invℚ₊y<z→x<y·z _ _ _ X)))
         (ℚ.isTrans< _ _ _ (ℚ.<-·o
           (fromNat (suc N))
           (fromNat (suc (suc n))) _ (ℚ.0<ℚ₊ ε)
           (ℚ.<ℤ→<ℚ _ _  (invEq (ℤ.pos-<-pos≃ℕ< (suc N) (suc (suc n))) <ssn)))
          (ℚ.isTrans< _ _ _ (
           ℚ.isTrans≤< _ _ _
            (ℚ.≡Weaken≤ _ _
             (cong ((fromNat (suc (suc n))) ℚ.·_)
              lem--034))
            (ℚ.<+ℚ₊' _ _ 1 (ℚ.isRefl≤ _)))
          (bernoulli's-ineq-^ℚⁿ ((fst ε) ℚ.+ 1) n
           (subst (1 ℚ.<_) (ℚ.+Comm _ _)
            (ℚ.<+ℚ₊' 1 1 ε (ℚ.isRefl≤ 1))))))}


-- bernoulli's-ineq-^ℚ-r<1 : ∀ x r → 1 <ᵣ fst x → 0 ℚ.< r → r ℚ.< 1 → fst (x ^ℚ r) <ᵣ 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)


module _ (z : ℝ₊) where

 lnSeq=diff : ∀ n → ((fst (z ^ℚ (0 ℚ.+ [ 1 / (2+ n)])) -ᵣ
                fst (z ^ℚ 0)) ／ᵣ[ rat [ 1 / (2+ n)] , inl (snd (ℚ₊→ℝ₊ ([ 1 / 2+ n ] , _))) ])
                 ≡ lnSeq z n
 lnSeq=diff n = cong₂ _·ᵣ_ (cong₂ _-ᵣ_ (cong (fst ∘ (z ^ℚ_)) (ℚ.+IdL _)) refl )
  (invℝ-rat _ _ (inl (ℚ.0<→< _ tt)))

 lnSeq≤ : ∀ n → lnSeq z n ≤ᵣ fst z -ᵣ 1
 lnSeq≤ n = subst2 _≤ᵣ_
   (cong ((fst (z ^ℚ ([ 1 / 2+ n ])) -ᵣ 1) ·ᵣ_)
      (invℝ₊-rat _ ∙ cong rat (cong (fst ∘ invℚ₊)
    (ℚ₊≡ (ℚ.+IdR _)) ∙ ℚ.invℚ₊-invol _)))

   (𝐑'.·IdR' _ _
     (cong fst invℝ₊1) ∙ cong (_-ᵣ 1) (cong fst (^ℚ-1 _)))
   (slope-incr z 0 [ 1 / 2+ n ] 1
      (ℚ.0<pos _ _)
      ((fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (suc (suc n))))
        (ℚ.≤ℤ→≤ℚ 1 (pos (suc (suc n)))
          (ℤ.suc-≤-suc {0} {pos (suc n)}
            ((ℤ.≤-suc {0} {pos n} (ℤ.zero-≤pos {n} )))))))

      (ℚ.0<pos _ _))



 lnSeq≤lnSeq : ∀ n m → m ℕ.≤ n → lnSeq z n ≤ᵣ lnSeq z m
 lnSeq≤lnSeq n m m≤n =
   subst2 _≤ᵣ_
     (cong ((fst (z ^ℚ ([ 1 / 2+ n ])) -ᵣ 1) ·ᵣ_)
        (invℝ₊-rat _ ∙ cong rat (cong (fst ∘ invℚ₊)
      (ℚ₊≡ (ℚ.+IdR _)) ∙ ℚ.invℚ₊-invol _)))
     (cong ((fst (z ^ℚ ([ 1 / 2+ m ])) -ᵣ 1) ·ᵣ_)
        (invℝ₊-rat _ ∙ cong rat (cong (fst ∘ invℚ₊)
      (ℚ₊≡ (ℚ.+IdR _)) ∙ ℚ.invℚ₊-invol _)))
     (slope-monotone z 0 [ 1 / 2+ n ] 0 [ 1 / 2+ m ]
            (ℚ.0<pos _ _) (ℚ.0<pos _ _) (ℚ.0≤pos _ _)
             (fst (ℚ.invℚ₊-≤-invℚ₊ (fromNat (suc (suc m))) (fromNat (suc (suc n))))
               (ℚ.≤ℤ→≤ℚ _ _ (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _) (ℕ.≤-k+ {k = 2} m≤n)))))

 lnSeq'≤lnSeq' : ∀ m n → m ℕ.≤ n → lnSeq' z m ≤ᵣ lnSeq' z n
 lnSeq'≤lnSeq' m n m<n =
   subst2 _≤ᵣ_
        ((cong ((1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ m ]))) ·ᵣ_)
     (invℝ₊-rat _ ∙ cong rat (cong (fst ∘ invℚ₊)
    (ℚ₊≡ (ℚ.+IdL _
    ∙ ℚ.-Invol _)) ∙ ℚ.invℚ₊-invol _))))
     (cong ((1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ]))) ·ᵣ_)
     (invℝ₊-rat _ ∙ cong rat (cong (fst ∘ invℚ₊)
    (ℚ₊≡ (ℚ.+IdL _
    ∙ ℚ.-Invol _)) ∙ ℚ.invℚ₊-invol _)))
     (slope-monotone z (ℚ.- [ 1 / 2+ _ ]) 0 (ℚ.- [ 1 / 2+ _ ]) 0
             (ℚ.minus-< 0 [ 1 / 2+ _ ] ((ℚ.0<pos 0 (1+ _))))
             (ℚ.minus-< 0 [ 1 / 2+ _ ] ((ℚ.0<pos 0 (1+ _))))

             (ℚ.minus-≤ [ 1 / 2+ _ ] [ 1 / 2+ _ ]
                (fst (ℚ.invℚ₊-≤-invℚ₊ (fromNat (suc (suc m))) ((fromNat (suc (suc n)))))
                       ((ℚ.≤ℤ→≤ℚ _ _ (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _) (ℕ.≤-k+ {k = 2} m<n))))))
              (ℚ.isRefl≤ 0))


--  0≤ᵣlnSeq : ∀ n → 0 ≤ᵣ lnSeq z n
--  0≤ᵣlnSeq n =  isTrans≡≤ᵣ _ _ _ (rat·ᵣrat 0 0) $
--    ≤ᵣ₊Monotone·ᵣ _ _ _ _
--     w (≤ᵣ-refl _)
--     w  (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos _ _) )

--    where

--    w = fst (x≤y≃0≤y-x _ _) (1≤^ℚ z _ 1≤z)

 lnSeq'≤lnSeq : ∀ n m → lnSeq' z n ≤ᵣ lnSeq z m
 lnSeq'≤lnSeq n m =
   subst2 _≤ᵣ_
     (cong ((1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ]))) ·ᵣ_)
       (invℝ₊-rat _ ∙ cong rat (cong (fst ∘ invℚ₊)
      (ℚ₊≡ (ℚ.+IdL _
      ∙ ℚ.-Invol _)) ∙ ℚ.invℚ₊-invol _)))
     (cong ((fst (z ^ℚ ([ 1 / 2+ m ])) -ᵣ 1) ·ᵣ_)
        (invℝ₊-rat _ ∙ cong rat (cong (fst ∘ invℚ₊)
      (ℚ₊≡ (ℚ.+IdR _)) ∙ ℚ.invℚ₊-invol _)))
     (slope-monotone z (ℚ.- [ 1 / 2+ n ]) 0 0 [ 1 / 2+ m ]
            (ℚ.minus-< 0 [ pos 1 / 2+ n ] (ℚ.0<pos _ _)) (ℚ.0<pos _ _ )
            (ℚ.minus-≤ 0 [ pos 1 / 2+ n ] (ℚ.0≤pos _ _)) (ℚ.0≤pos _ _))


seqΔ-δ : (Z : ℕ) → (ε : ℚ₊) → Σ ℕ λ N → (n : ℕ) →
            N ℕ.< n →
            fromNat (suc (suc Z)) ℚ.<
            ((fst (ε ℚ₊· invℚ₊ (fromNat (suc Z) ℚ₊· 2)) ℚ.+ 1) ℚ^ⁿ
             n)
seqΔ-δ Z ε = x^→∞ (suc (suc Z))
         (ε ℚ₊· (invℚ₊ ((([ pos (suc Z) / 1 ] , _)) ℚ₊· 2)))

opaque
 unfolding -ᵣ_ _+ᵣ_

 seqΔ-pos : ∀ z Z → (z<Z : fst z ≤ᵣ fromNat (suc (suc Z))) →
    1 ≤ᵣ fst z → ∀ (ε : ℚ₊) →
    (∀ n → (fst (seqΔ-δ Z ε)) ℕ.< n →
       lnSeq z n -ᵣ lnSeq' z n <ᵣ (rat (fst ε)))

 seqΔ-pos z Z z≤Z 1≤z ε =
  let (N , X) = x^→∞ (suc (suc Z))
          (ε ℚ₊· (invℚ₊ ((([ pos (suc Z) / 1 ] , _)) ℚ₊· 2)))
  in λ { n N<n →
     let
         X' = X (suc (suc n)) (ℕ.≤-trans N<n (ℕ.≤SumRight {k = 2}) )
         X'' = isTrans<≡ᵣ _ _ _ (a<c+b⇒a-b<c _ _ _
             (isTrans<≡ᵣ _ _ _ (^ℚ-StrictMonotone {fromNat (suc (suc Z)) }
                {ℚ₊→ℝ₊
                  (((ε ℚ₊· invℚ₊ (([ pos (suc Z) / 1 ] , tt) ℚ₊· 2)) ℚ₊+ 1)
                   ℚ₊^ⁿ (suc (suc n)))}
                 ([ 1 / 1+ (suc n) ] , _)
                 (<ℚ→<ᵣ _ _ X'))
                 (cong (fst ∘ _^ℚ [ pos 1 / 1+ (suc n) ])
                   (ℝ₊≡ (sym (^ⁿ-ℚ^ⁿ _ _)))
                  ∙  cong fst (^ℚ-·
                      (ℚ₊→ℝ₊
                       ((ε ℚ₊· invℚ₊ (([ pos (suc Z) / 1 ] , tt) ℚ₊· 2)) ℚ₊+ 1))
                       (fromNat (suc (suc n))) [ pos 1 / 1+ (suc n) ])
                       ∙ cong (fst ∘
                          (ℚ₊→ℝ₊ ((ε ℚ₊· invℚ₊ (([ pos (suc Z) / 1 ] , _) ℚ₊· 2))
                            ℚ₊+ 1) ^ℚ_)) (ℚ.x·invℚ₊[x] (fromNat _))
                       ∙ cong fst (^ℚ-1 _) ∙ cong (_+ᵣ 1) (rat·ᵣrat _ _))))
                       (cong (rat (fst ε) ·ᵣ_)
                         (sym (invℝ₊-rat _)))
         X''' = isTrans≡<ᵣ _ _ _
                  (cong (_·ᵣ
                 (fst (fromNat (suc (suc Z)) ^ℚ [ 1 / 2+ n ]) -ᵣ 1))
                  (cong rat (cong {y = fromNat (suc Z)} (ℚ._· 2)
                   (ℚ.ℤ-→ℚ- _ _ ∙ cong [_/ 1 ] (sym (ℤ.pos- _ _)) )
                  )))
                  (fst (z<x/y₊≃y₊·z<x _ _ _) X'')
     in isTrans≡<ᵣ _ _ _
       (cong (λ y → lnSeq z n -ᵣ  (1 -ᵣ y) ·ᵣ fromNat (suc (suc n)) )
         (cong fst (^ℚ-minus' z _) ∙
           cong fst (invℝ₊^ℚ _ _))
        ∙ sym (𝐑'.·DistL- _ _ _))
       (isTrans≤<ᵣ _ _ _
         (isTrans≤≡ᵣ _ _ _ (≤ᵣ-·ᵣo _ _ (fromNat (suc (suc n)))
          (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos _ _))
          ((x+1/x-bound _ (isTrans≤ᵣ _ _ _
             decℚ≤ᵣ?
             (1≤^ℚ z
               ([ pos 1 / 2+ n ] , _)
               1≤z)
               ))))
          (sym (·ᵣAssoc _ _ _)))
          (isTrans≤<ᵣ _ _ _
           (≤ᵣ₊Monotone·ᵣ _ _ _ _
           (let w = fst (x≤y≃0≤y-x _ _) (1≤^ℚ z ([ 1 / 2+ n ] , _) 1≤z)
            in isTrans≡≤ᵣ _ _ _ (sym (𝐑'.0RightAnnihilates 2) ) (≤ᵣ-o·ᵣ _ _ 2 decℚ≤ᵣ?
                   (x≤y→0≤y-x 1 _ (1≤^ℚ _ _
                    (isTrans≤ᵣ _ _ _ 1≤z z≤Z)))))


            (0≤ᵣlnSeq _)
             (≤ᵣ-o·ᵣ _ _ 2 decℚ≤ᵣ?
              (≤ᵣ-+o _ _ -1
               (^ℚ-Monotone {y = fromNat (suc (suc Z))} ([ 1 / 2+ n ] , _) z≤Z)))
             (isTrans≤ᵣ _ _ _ (lnSeq≤ z n)
               (≤ᵣ-+o _ _ -1 z≤Z)))
           (isTrans≡<ᵣ _ _ _ (·ᵣComm _ _ ∙  (·ᵣAssoc _ _ _) ∙
            cong (_·ᵣ (fst (fromNat (suc (suc Z)) ^ℚ [ 1 / 2+ n ]) +ᵣ -1))
             (sym (rat·ᵣrat _ _)) )
               X''')))
               }
   where

    0≤ᵣlnSeq : ∀ n → 0 ≤ᵣ lnSeq z n
    0≤ᵣlnSeq n =  isTrans≡≤ᵣ _ _ _ (rat·ᵣrat 0 0) $
      ≤ᵣ₊Monotone·ᵣ _ _ _ _
       w (≤ᵣ-refl _)
       w  (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos _ _) )

      where

      w : rat 0 ≤ᵣ fst (z ^ℚ [ 1 / 2+ n ]) -ᵣ 1
      w = fst (x≤y≃0≤y-x _ _) (1≤^ℚ z _ 1≤z)

opaque
 unfolding invℝ

 1≤x-⊔-x⁻¹ : ∀ x → 1 ≤ᵣ fst (maxᵣ₊ x (invℝ₊ x))
 1≤x-⊔-x⁻¹ (x , 0<x) =
  <→≤ContPos'pred {0}
   (AsContinuousWithPred _ _ (IsContinuousConst 1))
   (contDiagNE₂WP maxR _ _ _
     (AsContinuousWithPred _ _ (IsContinuousId))
       (snd invℝ'))
   (λ u 0<u →
     ⊎.rec (λ 1≤u → isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ 1≤u) (≤maxᵣ _ _))
           (λ u≤1 → isTrans≤ᵣ _ _ _
                      (≤ℚ→≤ᵣ _ (fst (invℚ₊ (u , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<u))))
             (fst (ℚ.invℚ₊-≤-invℚ₊ _ _) u≤1))
            (isTrans≤≡ᵣ _ _ _
             (≤maxᵣ _ (rat u))
              ( maxᵣComm _ _ ∙ cong (maxᵣ (rat u)) (sym (invℝ₊-rat _)
               ∙ cong (fst ∘ invℝ₊) (ℝ₊≡ refl)))))
       (ℚ.≤cases 1 u))
   x 0<x




Lipschitz-·R : ∀ q a → absᵣ a ≤ᵣ rat (fst q) → Lipschitz-ℝ→ℝ q (_·ᵣ a)
Lipschitz-·R q a a<q u v ε u∼v =
   invEq (∼≃abs<ε _ _ _) (
    subst2 _<ᵣ_
     (sym (·absᵣ _ _) ∙ cong absᵣ (𝐑'.·DistL- _ _ _))
     (·ᵣComm _ _ ∙ sym (rat·ᵣrat _ _))
     (isTrans≤<ᵣ _ _ _
       (≤ᵣ-o·ᵣ _ _ _ (0≤absᵣ _) a<q)
       (<ᵣ-·ᵣo _ _ (ℚ₊→ℝ₊ q) (fst (∼≃abs<ε _ _ _) u∼v))))

∃Lipschitz-·R : ∀ a → ∃[ L ∈ ℚ₊ ] Lipschitz-ℝ→ℝ L (_·ᵣ a)
∃Lipschitz-·R a =
  PT.map (λ (q , (<q , _)) →
    (q , (ℚ.<→0< _ $ <ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) <q)))
      , Lipschitz-·R _ a (<ᵣWeaken≤ᵣ _ _ <q) )
   (denseℚinℝ _ _
    (isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ 0 1 (absᵣ a) decℚ<ᵣ?)))


module expPreDer (Z : ℕ) where
 module expPreDer' (z : ℝ₊)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z) where



  seqΔ : ∀ (ε : ℚ₊) →
     (∀ n → (fst (seqΔ-δ Z ε)) ℕ.< n →
        lnSeq z n -ᵣ lnSeq' z n <ᵣ (rat (fst ε)))

  seqΔ ε n a<n =
      isTrans≡<ᵣ _ _ _ (w' n z)
        (seqΔ-pos z⊔z⁻¹ Z z⊔z⁻¹≤Z (1≤x-⊔-x⁻¹ z) ε n a<n)

   where
     diff : ℝ₊ → ℕ → ℝ
     diff z n = lnSeq z n -ᵣ lnSeq' z n

     z⊔z⁻¹ : ℝ₊
     z⊔z⁻¹ = maxᵣ₊ z (invℝ₊ z)

     z⊔z⁻¹≤Z : fst z⊔z⁻¹ ≤ᵣ fromNat (suc (suc Z))
     z⊔z⁻¹≤Z = max≤-lem _ _ _ z≤Z
      (subst2 _≤ᵣ_
        (·IdR _) (·IdR _)
        (fst (z/y'≤x/y≃y₊·z≤y'₊·x 1 1 (invℝ₊ z) (fromNat (suc (suc Z))))
         (subst2 _≤ᵣ_
        ((sym (invℝ₊-rat (fromNat (suc (suc Z)))) ∙
         cong (fst ∘ invℝ₊) (ℝ₊≡ refl))
         ∙ sym (·IdL _)) (cong fst (sym (invℝ₊Invol z)) ∙ sym (·IdL _))
         1/Z≤z)))
     opaque
      unfolding _+ᵣ_
      wC : ∀ n →
        IsContinuousWithPred pred0<
          (λ z 0<z → diff (z , 0<z) n)
      wC n = contDiagNE₂WP sumR pred0<  _ _
                (lnSeqCont n)
                (IsContinuousWP∘' pred0< _ _ IsContinuous-ᵣ
                 (lnSeq'Cont n))

     w-r<1 : ∀ n r 0<r → diff (ℚ₊→ℝ₊ (r , 0<r)) n ≡
                        diff (invℝ₊ (ℚ₊→ℝ₊ (r , 0<r))) n
     w-r<1 n r 0<r =
        +ᵣComm _ _ ∙ cong₂ _+ᵣ_
          (lnSeq'[z]≡lnSeq[1/x] n (ℚ₊→ℝ₊ (r , 0<r)))
          (lnSeq[z]≡lnSeq'[1/x] n (ℚ₊→ℝ₊ (r , 0<r)))


     opaque
      unfolding maxᵣ
      w-r : ∀ n r 0<r → diff (ℚ₊→ℝ₊ (r , 0<r)) n ≡
                         diff (maxᵣ₊ (ℚ₊→ℝ₊ (r , 0<r)) (ℚ₊→ℝ₊ (invℚ₊ (r , 0<r)))) n
      w-r n r 0<r = ⊎.rec
          (λ ≤r → cong (flip diff n)
                   (ℝ₊≡ {ℚ₊→ℝ₊ (r , 0<r)}
                        {maxᵣ₊ (ℚ₊→ℝ₊ (r , 0<r)) (ℚ₊→ℝ₊ (invℚ₊ (r , 0<r)))}
                     ((sym (maxᵣComm (fst ((ℚ₊→ℝ₊ (r , 0<r))))
                                (fst (ℚ₊→ℝ₊ (invℚ₊ (r , 0<r))))
                      ∙ ≤ᵣ→≡ (≤ℚ→≤ᵣ _ _ ≤r)))))) -- ≤ℚ→≤ᵣ _ _ ≤r

           (λ r≤ → w-r<1 n r 0<r ∙

            cong (flip diff n) (ℝ₊≡
             (invℝ₊-rat _ ∙ sym (≤ᵣ→≡  (≤ℚ→≤ᵣ r _  r≤))))
             )
          (ℚ.≤cases (fst (invℚ₊ (r , 0<r))) r)

      w' : ∀ n z → diff z n ≡ diff (maxᵣ₊ z (invℝ₊ z)) n
      w' n (z , 0<z) =
       ≡ContinuousWithPred
                  pred0< pred0< (openPred< 0) (openPred< 0) _ _ (wC n)
                  (IsContinuousWP∘ pred0< pred0< _ _
                    (λ r x → snd (maxᵣ₊ (r , x) (invℝ₊ (r , x))))  (wC n)
                    ((contDiagNE₂WP maxR _ _ _
                    (AsContinuousWithPred _ _ (IsContinuousId))
                      (snd invℝ'))))
                  (λ r r∈ r∈' → cong (flip diff n) (ℝ₊≡ refl)
                       ∙ w-r n r (ℚ.<→0< _ (<ᵣ→<ℚ _ _ r∈'))
                   ∙ cong (flip diff n)
                    (cong₂ maxᵣ₊
                      (ℝ₊≡ refl)
                      (ℝ₊≡ {_} {_ , snd ((invℝ₊ (fst (ℚ₊→ℝ₊
                       (r , ℚ.<→0< r (<ᵣ→<ℚ [ pos 0 / 1 ] r r∈'))) , r∈')))}
                       (sym (invℝ₊-rat _) ∙ cong (fst ∘ invℝ₊)
                        (ℝ₊≡ refl) ))) )
                  z 0<z 0<z

  -- lnSeq-∼ : (ε : ℚ₊) → ∀ {!!}
  -- lnSeq-∼ = {!!}
  ca-lnSeq : IsCauchySequence' (lnSeq z)
  ca-lnSeq ε =
    fst (seqΔ-δ Z ε) , ℕ.elimBy≤
     (λ x y X u v → isTrans≡<ᵣ _ _ _
       (minusComm-absᵣ _ _) (X v u) )
     λ x y x≤y <y <x →
       isTrans≤<ᵣ _ _ _
        ((isTrans≡≤ᵣ _ _ _
            (absᵣNonPos (lnSeq z y +ᵣ -ᵣ lnSeq z x)
              (fst (x≤y≃x-y≤0 _ _) (lnSeq≤lnSeq z _ _ x≤y))
              ∙ -[x-y]≡y-x _ _)
            (≤ᵣ-o+ _ _ _ (-ᵣ≤ᵣ _ _ (lnSeq'≤lnSeq z x y)))
            ))
        (seqΔ ε _ <x)

--   -- ca-lnSeq' : IsCauchySequence' lnSeq'
--   -- ca-lnSeq' = IsCauchySequence'-via-~seq lnSeq lnSeq' lnSeq~lnSeq' ca-lnSeq
--   -- IsCauchySequence'-via-~seq

  preLn : ℝ
  preLn = fromCauchySequence' _ ca-lnSeq

 -- --  lnSeq'-lim : ?
 -- --  lnSeq'-lim = fromCauchySequence'≡ _ ca-lnSeq
 -- -- -- fromCauchySequence'≡ : ∀ s ics x
 -- -- --          → ((∀ (ε : ℚ₊) →
 -- -- --              ∃[ N ∈ ℕ ] (∀ n → N ℕ.< n →
 -- -- --                   absᵣ ((s n) -ᵣ x) <ᵣ rat (fst ε))))
 -- -- --          → fromCauchySequence' s ics ≡ x

  preLn≤lnSeq : ∀ n → preLn ≤ᵣ (lnSeq z n)
  preLn≤lnSeq n =
    x<y+δ→x≤y  _ _ λ ε →
          let (m , M) = fromCauchySequence'-lim _ ca-lnSeq ε
              ii = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                   (isTrans≡<ᵣ _ _ _
                    (minusComm-absᵣ _ _)
                    (M (ℕ.max (suc m) n) ℕ.left-≤-max))
          in isTrans<≤ᵣ _ _ _
               (a-b<c⇒a<c+b _ _ _ ii)
               (isTrans≤≡ᵣ _ _ _
                 (≤ᵣ-o+ _ _ (rat (fst ε))
                   (lnSeq≤lnSeq z _ _ ℕ.right-≤-max))
                 (+ᵣComm _ _))

  lnSeq'≤preLn : ∀ n →  lnSeq' z n ≤ᵣ preLn
  lnSeq'≤preLn n = x<y+δ→x≤y  _ _ λ ε →
   let (m , M) = fromCauchySequence'-lim _ ca-lnSeq ε

   in isTrans≤<ᵣ _ _ _ (lnSeq'≤lnSeq z n (suc m))
        (isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _
         (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (M (suc m) (ℕ.≤-refl {suc m}))))
           (+ᵣComm (rat (fst ε)) preLn))

  preLn∼ : ∀ n ε → fst (seqΔ-δ Z ε) ℕ.< n → lnSeq z n ∼[ ε ] preLn
  preLn∼ n ε <n = invEq (∼≃abs<ε _ _ _)
    (isTrans≤<ᵣ _ _ _
      (isTrans≡≤ᵣ _ _ _
        (absᵣNonNeg _ (x≤y→0≤y-x _ _ (preLn≤lnSeq n)))
        (≤ᵣ-o+ _ _ _ (-ᵣ≤ᵣ _ _ (lnSeq'≤preLn n))))
     (seqΔ ε n <n))

  0<preLn : 1 <ᵣ fst z → 0 <ᵣ preLn
  0<preLn 1<z = isTrans<≤ᵣ _ _ _
      (ℝ₊· (_ , x<y→0<y-x _ 1
       (^ℚ-StrictMonotoneR {z} 1<z (ℚ.- [ 1 / 2+ 0 ]) 0
         (ℚ.decℚ<? {ℚ.- [ pos 1 / 2+ 0 ]} {0})))
      (fromNat 2))
      (lnSeq'≤preLn 0)

  -- preLn<0 : fst z <ᵣ 1 → preLn <ᵣ 0
  -- preLn<0 z<1 = isTrans≤<ᵣ _ _ _
  --   {!!}
  --   {!!}

 open expPreDer'

 0=preLn : (1≤ : fst 1 ≤ᵣ fromNat (suc (suc Z)))
           (≤1 : rat [ pos 1 / 2+ Z ] ≤ᵣ 1)
           → 0 ≡ preLn 1 1≤ ≤1
 0=preLn 1≤ ≤1 = sym (limConstRat 0 λ _ _ → refl∼ _ _)
  ∙ congLim _ _ _ _ λ q → sym (𝐑'.0LeftAnnihilates' _ _
     (𝐑'.+InvR' (fst (1 ^ℚ [ 1 / 2+ _ ])) 1 (cong fst (1^ℚ≡1 _))))

 preLn-inv : (z : ℝ₊)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
          (1/z≤Z : fst (invℝ₊ z) ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤1/z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst (invℝ₊ z))
           → preLn (invℝ₊ z) 1/z≤Z 1/Z≤1/z ≡ -ᵣ (preLn z z≤Z 1/Z≤z)
 preLn-inv z z≤Z 1/Z≤z 1/z≤Z 1/Z≤1/z =
   fromCauchySequence'≡ _ _ _
     λ ε → ∣ (fst (seqΔ-δ Z ε)) ,
          (λ n <n →
            isTrans≡<ᵣ _ (preLn z z≤Z 1/Z≤z -ᵣ lnSeq' z n) _
              (cong (λ xx → absᵣ (xx -ᵣ -ᵣ preLn z z≤Z 1/Z≤z))
                  (sym (lnSeq'[z]≡lnSeq[1/x] n z))
                ∙ cong absᵣ (sym (L𝐑.lem--083 {preLn z z≤Z 1/Z≤z} {lnSeq' z n}))
                ∙ absᵣNonNeg _ (x≤y→0≤y-x _ _ (lnSeq'≤preLn _ _ _ n )))
              (isTrans≤<ᵣ _ _ _
                (≤ᵣ-+o (preLn z z≤Z 1/Z≤z) _ (-ᵣ lnSeq' z n)
                  (preLn≤lnSeq _ _ _ n))
                (seqΔ z z≤Z 1/Z≤z ε n <n))) ∣₁




 monotonePreLn : (z z' : ℝ₊)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
          (z'≤Z : fst z' ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z' :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z')
          → fst z ≤ᵣ fst z'
          → preLn z z≤Z 1/Z≤z  ≤ᵣ
              preLn z' z'≤Z 1/Z≤z'
 monotonePreLn z z' z≤Z 1/Z≤z z'≤Z 1/Z≤z' z≤z' =
   fromCauchySequence'≤ _ _ _ _
     (lnSeqMonInZ z z' z≤z')




 opaque
  unfolding -ᵣ_

  slope-monotone-preLn : ∀ (a b a' b' : ℝ₊)
     a≤Z 1/Z≤a b≤Z 1/Z≤b a'≤Z 1/Z≤a' b'≤Z 1/Z≤b'
    → (a<b : fst a <ᵣ fst b) → (a'<b' : fst a' <ᵣ fst b')
    → (a≤a' : fst a ≤ᵣ fst a') →  (b≤b' : fst b ≤ᵣ fst b') →
    (((preLn b' b'≤Z 1/Z≤b') -ᵣ (preLn a' a'≤Z 1/Z≤a'))
      ／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
        ≤ᵣ
    (((preLn b b≤Z 1/Z≤b) -ᵣ (preLn a a≤Z 1/Z≤a))
      ／ᵣ₊ (_ , x<y→0<y-x _ _ a<b ))
  slope-monotone-preLn a b a' b'
    a≤Z 1/Z≤a b≤Z 1/Z≤b a'≤Z 1/Z≤a' b'≤Z 1/Z≤b'
      a<b a'<b' a≤a' b≤b' =
        PT.rec2 (isProp≤ᵣ _ _)
                          ww
          (∃Lipschitz-·R (fst (invℝ₊ b'-a')))
          (∃Lipschitz-·R (fst (invℝ₊ b-a)))


    where


     b'-a' : ℝ₊
     b'-a' = (_ , x<y→0<y-x _ _ a'<b' )
     b-a : ℝ₊
     b-a = (_ , x<y→0<y-x _ _ a<b )
     opaque
      unfolding _+ᵣ_
      ww : Σ ℚ₊ (λ L → Lipschitz-ℝ→ℝ L (_·ᵣ fst (invℝ₊ b'-a'))) →
           Σ ℚ₊ (λ L → Lipschitz-ℝ→ℝ L (_·ᵣ fst (invℝ₊ b-a))) →
              ((preLn b' b'≤Z 1/Z≤b' -ᵣ preLn a' a'≤Z 1/Z≤a') ／ᵣ₊
                  (fst b' +ᵣ -ᵣ fst a' , x<y→0<y-x (fst a') (fst b') a'<b'))
                 ≤ᵣ
                 ((preLn b b≤Z 1/Z≤b -ᵣ preLn a a≤Z 1/Z≤a) ／ᵣ₊
                  (fst b +ᵣ -ᵣ fst a , x<y→0<y-x (fst a) (fst b) a<b))
      ww (_ , lip·') (_ , lip·) = subst2 _≤ᵣ_
        (sym (snd (map-fromCauchySequence' _ _ _ _ lip·'))
               ∙ cong (_／ᵣ₊ b'-a')
                   (sym (snd (mapNE-fromCauchySequence' sumR _ _ _ _))
                      ∙ cong ((preLn b' b'≤Z 1/Z≤b') +ᵣ_)
                       (sym (snd (map-fromCauchySequence' _ _ _ _ (snd -ᵣR))))))
        (sym (snd (map-fromCauchySequence' _ _ _ _ lip·))
               ∙ cong (_／ᵣ₊ b-a)
                   (sym (snd (mapNE-fromCauchySequence' sumR _ _ _ _))
                     ∙ cong ((preLn b b≤Z 1/Z≤b) +ᵣ_)
                       (sym (snd (map-fromCauchySequence' _ _ _ _ (snd -ᵣR))))))
            (fromCauchySequence'≤ _ _ _ _ w)

       where



       w : (n : ℕ) →
                (((lnSeq b' n) -ᵣ (lnSeq a' n)) ／ᵣ₊ b'-a')
             ≤ᵣ (((lnSeq b n) -ᵣ (lnSeq a n)) ／ᵣ₊ b-a)
       w n = subst2 _≤ᵣ_
              (·ᵣAssoc _ _ _
                 ∙ cong (_／ᵣ₊ b'-a')
                  ((cong (fromNat (suc (suc n)) ·ᵣ_)
                   (cong₂ _-ᵣ_ (sym (·IdL _)) (sym (·IdL _)) ∙ sym ( L𝐑.lem--075))
                      ∙ ·ᵣComm _ _  ∙ 𝐑'.·DistL- _ _ _)))
              (·ᵣAssoc _ _ _
                  ∙ cong (_／ᵣ₊ b-a) ((cong (fromNat (suc (suc n)) ·ᵣ_)
                    (cong₂ _-ᵣ_ (sym (·IdL _)) (sym (·IdL _)) ∙ sym (L𝐑.lem--075))
                      ∙ ·ᵣComm _ _ ∙ 𝐑'.·DistL- _ _ _)))
              (≤ᵣ-o·ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos _ _))
                (slope-monotone-ₙ√ (suc n) _ _ _ _
                  a<b a'<b' a≤a' b≤b'))

