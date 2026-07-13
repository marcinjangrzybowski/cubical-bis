{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.Approximation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( 0<_ )
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ; x·invℚ[x]; x<y·z→x/y<z)

import Cubical.Algebra.OrderedCommRing.Properties as OCRP
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using (ℚOrderedCommRing)

private
  module ℚO = OCRP.OrderedCommRingTheory ℚOrderedCommRing


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisection
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

ointervalℙ⊆-max : ∀ n m →
           ointervalℙ
           (rat (ℚ.- fromNat (suc n)))
           (rat (fromNat (suc n))) ⊆
           ointervalℙ
           (rat (ℚ.- fromNat (suc (max n m))))
           (rat (fromNat (suc (max n m))))
ointervalℙ⊆-max n m x (≤x , x≤) =
    (isTrans≤<ᵣ _ _ _
    (≤ℚ→≤ᵣ _ _
      (ℚ.minus-≤ _ _
        (≤ℤ→≤ℚ _ _
          (ℤ.ℕ≤→pos-≤-pos _ _
            (ℕ.≤-k+ {_} {_} {1} (ℕ.left-≤-max {n} {m}))))))
    ≤x)
  , isTrans<≤ᵣ _ _ _ x≤
       (≤ℚ→≤ᵣ _ _
         (≤ℤ→≤ℚ _ _
          (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-k+ {_} {_} {1} $ ℕ.left-≤-max {n} {m})))

         )


ointervalℙ⊆-max' : ∀ n m →
           ointervalℙ
           (rat (ℚ.- fromNat (suc m)))
           (rat (fromNat (suc m))) ⊆
           ointervalℙ
           (rat (ℚ.- fromNat (suc (max n m))))
           (rat (fromNat (suc (max n m))))
ointervalℙ⊆-max' n m x (≤x , x≤) =
  (isTrans≤<ᵣ _ _ _
    (≤ℚ→≤ᵣ _ _
      (ℚ.minus-≤ _ _
        (≤ℤ→≤ℚ _ _
          (ℤ.ℕ≤→pos-≤-pos _ _
            (ℕ.≤-k+ {_} {_} {1} (ℕ.right-≤-max {m} {n}))))))
    ≤x)
  , isTrans<≤ᵣ _ _ _ x≤
       (≤ℚ→≤ᵣ _ _ (≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
         (ℕ.≤-k+ {_} {_} {1} $ ℕ.right-≤-max {m} {n}))))


module RestrℝIso (a b fa fb : ℝ)
      (isom :
          Iso (Σ ℝ (_∈ ointervalℙ a b))
              (Σ ℝ (_∈ ointervalℙ fa fb))) where

 open Iso isom

 module _ (monotoneFun : ∀ x y → fst x ≤ᵣ fst y → fst (fun x) ≤ᵣ fst (fun y))
          (monotoneInv : ∀ x y → fst x ≤ᵣ fst y → fst (inv x) ≤ᵣ fst (inv y))
          (a' b' : ℝ) (a'<b' : a' <ᵣ b')
          (a'∈ : a' ∈ ointervalℙ a b)
          (b'∈ : b' ∈ ointervalℙ a b) where

  fa' = fun (a' , a'∈)
  fb' = fun (b' , b'∈)

  restrIso : Iso (Σ ℝ (_∈ intervalℙ a' b'))
                 (Σ ℝ (_∈ intervalℙ (fst fa') (fst fb')))
  restrIso .Iso.fun (x , ≤x , x≤) =
    let X = (x ,
             (isTrans<≤ᵣ _ _ _ (fst a'∈) ≤x)
               , isTrans≤<ᵣ _ _ _ x≤ (snd b'∈))
        (fx , fx∈) = fun X
    in fx , monotoneFun (a' , a'∈) X ≤x
          , monotoneFun X (b' , b'∈) x≤
  restrIso .Iso.inv (x , ≤x , x≤) =
    let X = (x ,
             (isTrans<≤ᵣ _ _ _ (fst (snd fa')) ≤x)
               , isTrans≤<ᵣ _ _ _ x≤ (snd (snd fb')))
        (fx , fx∈) = inv X
    in fx , isTrans≡≤ᵣ _ _ _ (sym (cong fst (Iso.ret isom (a' , a'∈))))
            (monotoneInv fa' X ≤x)
          , isTrans≤≡ᵣ _ _ _ (monotoneInv X fb' x≤)
            (cong fst (Iso.ret isom (b' , b'∈)))
  restrIso .Iso.sec _ =
   Σ≡Prop (∈-isProp (intervalℙ _ _))
     (cong fst
        ((cong fun (Σ≡Prop (∈-isProp (ointervalℙ _ _))
          (refl))) ∙ Iso.sec isom _))

  restrIso .Iso.ret _ =
   Σ≡Prop (∈-isProp (intervalℙ _ _))
     (cong fst
        ((cong inv (Σ≡Prop (∈-isProp (ointervalℙ _ _))
          (refl))) ∙ Iso.ret isom _))


module EquivFromRestr
     (f : ℝ → ℝ)

     (f∈ₙ : ∀ n x → (x ∈ (ointervalℙ
                      (rat (ℚ.- fromNat (suc n)))
                      (rat (fromNat (suc n))))) →
                       f x ∈ (ointervalℙ
                      (f (rat (ℚ.- fromNat (suc n))))
                      (f (rat (fromNat (suc n))))))
     (equiv-restr : ∀ n →
       isEquiv {A = Σ ℝ (_∈ (ointervalℙ
                      (rat (ℚ.- fromNat (suc n)))
                      (rat (fromNat (suc n)))))}
               {B = Σ ℝ (_∈ (ointervalℙ
                      (f (rat (ℚ.- fromNat (suc n))))
                      (f (rat (fromNat (suc n))))))}
                λ (x , x∈) → f x , f∈ₙ n x x∈) where

 clamp' : ∀ x → ∃[ n ∈ ℕ ] (x ∈ (ointervalℙ
                  ((rat (ℚ.- fromNat (suc n))))
                  ((rat (fromNat (suc n))))))
 clamp' x =
   PT.map (λ (1+ n , X) →
        n
     , isTrans<≡ᵣ _ _ _
           (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat  _)) (-ᵣ<ᵣ _ _ (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
           (isTrans≡<ᵣ _ _ _ (sym (-absᵣ _)) X))))

            (-ᵣInvol x)
     , isTrans≤<ᵣ _ _ _ (≤absᵣ _) X)
     (getClamps x)

 Bℙ : ℙ ℝ
 Bℙ x = (∃[ n ∈ ℕ ] (x ∈ (ointervalℙ
                      (f (rat (ℚ.- fromNat (suc n))))
                      (f (rat (fromNat (suc n))))))) , squash₁

 f' : ℝ → Σ ℝ (_∈ Bℙ)
 f' x = f x , PT.map (map-snd (λ {n} → f∈ₙ n x)) (clamp' x)

 f-inj : ∀ w x → f w ≡ f x → w ≡ x
 f-inj w x =
   PT.rec2 (isProp→ (isSetℝ _ _))
     (λ (n , N) (m , M) →
      λ fw=fx →
         cong fst (invEq (congEquiv
       {x = w , ointervalℙ⊆-max n m w N}
       {y = x , ointervalℙ⊆-max' n m x M} (_ , equiv-restr (ℕ.max n m)))
         (Σ≡Prop (∈-isProp _) fw=fx)))
    (clamp' w) (clamp' x)

 isEmbedding-f' : isEmbedding f'
 isEmbedding-f' w x =
  snd (propBiimpl→Equiv (isSetℝ _ _)
      ((isSetΣ isSetℝ (isProp→isSet ∘ ∈-isProp Bℙ)) _ _)
    (cong f')
    (f-inj w x ∘ cong fst))

 isSurjection-f' : isSurjection f'
 isSurjection-f' = λ (x , x∈) →
   PT.map (λ (n , N) →
    let (y , y∈) = invEq (_ , equiv-restr n) (_ , N)
    in y , Σ≡Prop (∈-isProp _) (cong fst (secEq (_ , equiv-restr n) (_ , N))))
    x∈

 equiv-fromRestr : isEquiv f'
 equiv-fromRestr = isEmbedding×isSurjection→isEquiv
  (isEmbedding-f' , isSurjection-f')


ℚApproxℙ''→ℚApproxℙ' : ∀ (P Q : ℙ ℝ) f  →
  (ℚApproxℙ'' P Q f) → (ℚApproxℙ' P Q f)
ℚApproxℙ''→ℚApproxℙ' P Q f X q q∈P =
  (λ ε → fst (X q q∈P (ε /2₊)))
  , (λ ε → fst (snd (X q q∈P (ε /2₊)))) , zz ,

    eqℝ _ _ λ ε →
       let z = triangle∼ {ε = (ε /2₊ +₊ (ε /2₊) /2₊) +₊ (((ε /2₊) /2₊) /2₊)}
                    (lim-rat (λ δ → rat (fst (X q q∈P (δ /2₊)))) _ _
                      ((ε /2₊) /2₊)
                      _ (subst 0<_
                         (sym (Rℚ.plusMinus _ _)
                            ∙ cong (ℚ._- fst ((ε /2₊) /2₊)) (
                               sym (ℚ.+Assoc _ _ _)
                              ∙∙ cong (fst (ε /2₊) ℚ.+_) (ℚ.+Comm _ _)
                               ∙∙ ℚ.+Assoc _ _ _) )
                         (snd ((ε /2₊) +₊ (((ε /2₊) /2₊) /2₊))  )) (refl∼ _ _))

                  (snd (snd (X q q∈P (((ε /2₊) /2₊) /2₊))))
       in subst∼ (sym (ℚ.+Assoc _ _ _)
               ∙∙ cong ((fst (ε /2₊) ℚ.+ fst ((ε /2₊) /2₊)) ℚ.+_)
                     (1/2∈ℚ./2+/2≡id (fst ((ε /2₊) /2₊)))
               ∙∙ (sym (ℚ.+Assoc _ _ _)
                ∙∙ cong (fst (ε /2₊) ℚ.+_) (1/2∈ℚ./2+/2≡id (fst (ε /2₊)))
                ∙∙ 1/2∈ℚ./2+/2≡id (fst ε))) z
 where
 zz : (δ ε : ℚ₊) →
      rat (fst (X q q∈P (δ /2₊))) ∼[ δ +₊ ε ]
      rat (fst (X q q∈P (ε /2₊)))
 zz δ ε = ∼-monotone< (
       subst (ℚ._< fst (δ +₊ ε)) (ℚ.·DistR+ _ _ _) (/2₊<id (δ +₊ ε)))
   (triangle∼ (snd (snd ((X q q∈P) (δ /2₊)))) --((snd ((X q q∈P) (δ /2₊))))
     (sym∼ _ _ _ (snd ((snd ((X q q∈P) (ε /2₊))))) --((snd ((X q q∈P) (ε /2₊))))
     ))




clamp-abs : ∀ L L' x → L ℚ.≤ L' →
     abs (ℚ.clamp L L' x) ℚ.≤ ℚ.max (abs L) (abs L')
clamp-abs L L' x L≤L' = ⊎.rec
  (λ 0≤ → subst (ℚ._≤ ℚ.max (abs L) (abs L'))
     (sym (ℚO.0≤→abs≡id _ 0≤))
       (ℚ.isTrans≤ _ _ _ (ℚ.clamp≤ L L' x)
        (ℚ.isTrans≤ _ _ _
          (≤abs _) (ℚ.≤max' _ _))))
  (λ <0 →
     subst (ℚ._≤ ℚ.max (abs L) (abs L'))
       (sym (ℚO.<0→abs≡- _ <0))
       (ℚ.isTrans≤ _ _ _
         (ℚ.isTrans≤ _ _ _
          (ℚ.minus-≤ _ _ (ℚ.≤clamp L L' x L≤L'))
          (-≤abs L))
         (ℚ.≤max _ _)))
  (ℚ.Dichotomyℚ 0 (ℚ.clamp L L' x))

module _ (f : ℚ → ℝ) (B : ℕ → ℚ₊)  where

 boundedLipschitz : Type
 boundedLipschitz =
   ∀ n x y
       → abs x ℚ.≤ fromNat (suc n)
       → abs y ℚ.≤ fromNat (suc n)
     →  absᵣ (f y -ᵣ f x) ≤ᵣ rat (fst (B n) ℚ.· abs (y ℚ.- x))

 module BoundedLipsch (bl : boundedLipschitz) where

  clampL clampU : ℕ → ℚ
  clampL n = fromNeg (suc n)
  clampU n = fromNat (suc n)

  clampL≤clampU : ∀ n → clampL n ℚ.≤ clampU n
  clampL≤clampU n = ℚ.neg≤pos (suc n) (suc n)

  clampAbs≤ : ∀ n x → abs (ℚ.clamp (clampL n) (clampU n) x) ℚ.≤ clampU n
  clampAbs≤ n x =
    ℚ.absFrom≤×≤ (clampU n) (ℚ.clamp (clampL n) (clampU n) x)
      (subst (λ z → z ℚ.≤ ℚ.clamp (clampL n) (clampU n) x)
        (ℚ.-fromNat (suc n))
        (ℚ.≤clamp (clampL n) (clampU n) x (clampL≤clampU n)))
      (ℚ.clamp≤ (clampL n) (clampU n) x)

  flₙ : ∀ n → Σ (Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (B n))) (IsContinuous ∘ fst)
  flₙ n = fl , uncurry (Lipschitz→IsContinuous _) fl
   where
   L≤U : clampL n ℚ.≤ clampU n
   L≤U = clampL≤clampU n

   fl = fromLipschitz (B n)
     (f ∘ ℚ.clamp (clampL n) (clampU n) ,
        Lipschitz-ℚ→ℝ'→Lipschitz-ℚ→ℝ _ _
          λ q r →
            isTrans≤ᵣ _ _ _
                (bl n
                  (ℚ.clamp (clampL n) (clampU n) r)
                  (ℚ.clamp (clampL n) (clampU n) q)
                  (clampAbs≤ n r)
                  (clampAbs≤ n q))
              (≤ℚ→≤ᵣ _ _
                (ℚ.≤-o· _ _ _ (ℚ.0≤ℚ₊ (B n))
                  (ℚ.clampDist _ _ _ _))))

  flₙ-rat : ∀ n q →
    fst (fst (flₙ n)) (rat q) ≡
    f (ℚ.clamp (clampL n) (clampU n) q)
  flₙ-rat n q = fromLipschitz-rat


  Seq⊆→Power : Seq⊆→ ℝ Seq⊆-abs<N
  Seq⊆→Power .Seq⊆→.fun x n _ = fst (fst (flₙ n)) x
  Seq⊆→Power .Seq⊆→.fun⊆ x n m x∈ x'∈ n<m = ww
   where

   fₙ fₘ : ℝ → ℝ
   fₙ = fst (fst (flₙ n))
   fₘ = fst (fst (flₙ m))

   rat∈clampInterval : ∀ k r →
     rat r ∈ ointervalℙ (fromNeg (suc k)) (fromNat (suc k)) →
     r ∈ ℚ.ℚintervalℙ (clampL k) (clampU k)
   rat∈clampInterval k r (L<r , r<U) =
     ∈intervalℙ→∈ℚintervalℙ _ _ r
       (<ᵣWeaken≤ᵣ _ _ L<r , <ᵣWeaken≤ᵣ _ _ r<U)

   agree-rat : ∀ r r∈ r∈' → fₙ (rat r) ≡ fₘ (rat r)
   agree-rat r r∈ r∈' =
       flₙ-rat n r
     ∙ cong f
         (sym (ℚ.∈ℚintervalℙ→clam≡ _ _ r
           (rat∈clampInterval n r r∈)))
     ∙ cong f
         (ℚ.∈ℚintervalℙ→clam≡ _ _ r
           (rat∈clampInterval m r r∈'))
     ∙ sym (flₙ-rat m r)

   ww : fst (fst (flₙ n)) x ≡ fst (fst (flₙ m)) x
   ww =
     ≡ContinuousWithPred (ointervalℙ _ _) (ointervalℙ _ _)
       (openIintervalℙ _ _) (openIintervalℙ _ _)
       (λ x _ → fₙ x) (λ x _ → fₘ x)
       (AsContinuousWithPred (ointervalℙ (fromNeg (suc n)) (fromNat (suc n)))
         _ (snd (flₙ n)))
       (AsContinuousWithPred (ointervalℙ (fromNeg (suc m)) (fromNat (suc m)))
         _ (snd (flₙ m)))
       agree-rat
       x x∈ x'∈


  open Seq⊆→.FromIntersection Seq⊆→Power
    isSetℝ (λ _ → Unit , isPropUnit) Seq⊆-abs<N-s⊇-⊤Pred public

  𝒇 : ℝ → ℝ
  𝒇 x = ∩$ x _




  𝒇-rat : ∀ q → 𝒇 (rat q) ≡ f q
  𝒇-rat q = PT.rec (isSetℝ _ _) (λ y → snd (snd y) ∙ flₙ-rat (fst y) q ∙ cong f
        (sym (ℚ.∈ℚintervalℙ→clam≡ _ _ _
          (∈intervalℙ→∈ℚintervalℙ _ _ _
             (<ᵣWeaken≤ᵣ _ _ (fst (fst (snd y))) ,
              <ᵣWeaken≤ᵣ _ _ (snd (fst (snd y))))))))
    (∩$-lem (rat q) _)

  𝒇-cont : IsContinuous 𝒇
  𝒇-cont = contDropPred 𝒇 (∩$-cont _ _ (λ _ → openIintervalℙ _ _)
     _ _ λ n → AsContinuousWithPred (λ _ → _ ,
         isProp× _ _)
                 (fst (fst (flₙ n)))
                  (snd (flₙ n)))
  module Equiv𝒇₊ (f∈ : ∀ n x x∈ → fst (fst (flₙ n)) x ∈
                   ointervalℙ (𝒇 (fromNeg (suc n)))
                             (𝒇 (fromNat (suc n))))
           (isEquivFₙ : ∀ n →
           isEquiv
              {A = Σ _ (_∈ ointervalℙ (fromNeg (suc n)) (fromNat (suc n)))}
              {B = Σ _ (_∈ ointervalℙ (𝒇 (fromNeg (suc n)))
                                      (𝒇 (fromNat (suc n))))}
             λ (x , x∈) →
                ((fst (fst (flₙ n))) x) ,
                  f∈ n x x∈)
           (exN' : ∀ b → 0 <ᵣ b → ∃[ n ∈ ℕ ]
                  b ∈
                   ointervalℙ (𝒇 (fromNeg (suc n)))
                             (𝒇 (fromNat (suc n))))
           (𝒇-pos : ∀ x → 0 <ᵣ 𝒇 x)
      where

   𝒇₊ : ℝ → ℝ₊
   𝒇₊ x = 𝒇 x , 𝒇-pos x

   isEmbedding-𝒇 : isEmbedding {A = ℝ} {B = ℝ₊} 𝒇₊
   isEmbedding-𝒇 w x =
    snd
     (propBiimpl→Equiv (isSetℝ _ _) (isSetℝ₊ _ _)
      (cong 𝒇₊)
      ((∩$-elimProp2 w _ x _ {λ u v → u ≡ v → w ≡ x}
       (λ _ _ → isProp→ (isSetℝ _ _))
        λ n w∈ x∈ p → cong fst
          (invEq (congEquiv {x = _ , w∈} {y = _ , x∈}
            (_ , isEquivFₙ n))
            (Σ≡Prop (∈-isProp
             (ointervalℙ
               (𝒇 (fromNeg (suc n)))
               (𝒇 (fromNat (suc n))))) p)) ) ∘ cong fst)
               )

   isSurjection-𝒇 : isSurjection 𝒇₊
   isSurjection-𝒇 (b , b∈') =
     PT.map (λ (n , b∈) →
       let (y , y∈) = invEq (_ , isEquivFₙ n) (b , b∈)
       in y , ℝ₊≡
            (∩$-∈ₙ _ _ n y∈
           ∙ cong fst (secEq (_ , isEquivFₙ n) (b , b∈))))
       (exN' b b∈')

   𝒇₊-equiv : isEquiv 𝒇₊
   𝒇₊-equiv = isEmbedding×isSurjection→isEquiv
     (isEmbedding-𝒇 , isSurjection-𝒇)

  lipFₙ : ∀ n → Lipschitz-ℝ→ℝℙ (B n)
       (intervalℙ (rat (clampL n)) (rat (clampU n)))
       (λ x _ → fst (fst (flₙ n)) x)
  lipFₙ n u _ v _ = snd (fst (flₙ n)) u v

  module _ (K : ℕ → ℚ₊) where
   boundedInvLipschitz : Type
   boundedInvLipschitz =
     ∀ n x y
         → abs x ℚ.≤ fromNat (suc n)
         → abs y ℚ.≤ fromNat (suc n)
       →  rat (abs (y ℚ.- x)) ≤ᵣ rat (fst (K n)) ·ᵣ absᵣ (f y -ᵣ f x)

   module BoundedInvLipsch (ibl : boundedInvLipschitz)
              -- (𝒇-pos : ∀ x → 0 <ᵣ 𝒇 x)
              -- (aprox : ℚApproxℙ' ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
              --     λ x _ → 𝒇 x , 𝒇-pos x)
              where
    invLipFₙ : ∀ n → Invlipschitz-ℝ→ℝℙ (K n)
      (intervalℙ (rat (clampL n)) (rat (clampU n)))
      (λ x _ → fst (fst (flₙ n)) x)
    invLipFₙ n u u∈ v v∈ ε X =
     let X' = fst (∼≃abs<ε _ _ _) X


     in invEq (∼≃abs<ε _ _ _)
          (isTrans≤<ᵣ _ _ _
            bil-clamp
            (isTrans<≡ᵣ _ _ _
              (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ (K n)) X')
              (sym (rat·ᵣrat _ _))))

        where

         u' = clampᵣ (rat (clampL n)) (rat (clampU n)) u
         v' = clampᵣ (rat (clampL n)) (rat (clampU n)) v

         opaque
          unfolding _+ᵣ_ maxᵣ
          bil-clamp : absᵣ (u +ᵣ -ᵣ v) ≤ᵣ
                       fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
                       absᵣ (fst (fst (flₙ n)) u +ᵣ -ᵣ fst (fst (flₙ n)) v)
          bil-clamp =
            subst2 {x = u'} {z = v'} (λ u v → absᵣ (u +ᵣ -ᵣ v) ≤ᵣ
               fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
               absᵣ (fst (fst (flₙ n)) u +ᵣ -ᵣ fst (fst (flₙ n)) v))
               (sym (∈ℚintervalℙ→clampᵣ≡ (rat (clampL n)) (rat (clampU n))
                   u ((fst u∈) , snd u∈)))
               (sym (∈ℚintervalℙ→clampᵣ≡ (rat (clampL n)) (rat (clampU n))
                   v (fst v∈ , snd v∈)))
               (≤Cont₂ {λ u v →
                         absᵣ (clampᵣ (rat (clampL n))
                 (rat (clampU n)) u -ᵣ
                           clampᵣ (rat (clampL n))
                 (rat (clampU n)) v)}
                       {λ u v →
                         fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
                       absᵣ (fst (fst (flₙ n)) (clampᵣ (rat (clampL n))
                 (rat (clampU n)) u)
                          -ᵣ fst (fst (flₙ n)) (clampᵣ (rat (clampL n))
                 (rat (clampU n)) v))}
                  (cont∘₂ IsContinuousAbsᵣ
                      (cont₂∘ (contNE₂ sumR)
                        (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n)) )
                        (IsContinuous∘ _ _ IsContinuous-ᵣ
                           (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))))
                  (cont∘₂ (IsContinuous·ᵣL _)
                     (cont∘₂ IsContinuousAbsᵣ
                        (cont₂∘ (contNE₂ sumR)
                            (IsContinuous∘ _ _
                              (snd (flₙ n))
                             (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))
                            (IsContinuous∘ _ _ IsContinuous-ᵣ
                              (IsContinuous∘ _ _
                              (snd (flₙ n))
                             (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))))))
                    (λ u v →
                        subst2 _≤ᵣ_
                            (sym (absᵣ-rat _) ∙
                             cong absᵣ (sym (-ᵣ-rat₂ _ _)) ∙
                             cong₂ (λ x y → absᵣ (x -ᵣ y))
                               (sym (clampᵣ-rat
                                 (clampL n) (clampU n) u))
                               (sym (clampᵣ-rat
                                 (clampL n) (clampU n) v)))
                            (cong₂ (λ fu fv → rat (fst (K n)) ·ᵣ
                              absᵣ (fu -ᵣ fv))
                               (cong f
                                 (ℚ.∈ℚintervalℙ→clam≡ _ _
                                   (ℚ.clamp (clampL n) (clampU n) u)
                                   (ℚ.clam∈ℚintervalℙ _ _
                                     (clampL≤clampU n) u))
                                ∙ sym (flₙ-rat n
                                  (ℚ.clamp (clampL n) (clampU n) u))
                                ∙ cong (fst (fst (flₙ n)))
                                  (sym (clampᵣ-rat
                                    (clampL n) (clampU n) u)))
                               (cong f
                                 (ℚ.∈ℚintervalℙ→clam≡ _ _
                                   (ℚ.clamp (clampL n) (clampU n) v)
                                   (ℚ.clam∈ℚintervalℙ _ _
                                     (clampL≤clampU n) v))
                                ∙ sym (flₙ-rat n
                                  (ℚ.clamp (clampL n) (clampU n) v))
                                ∙ cong (fst (fst (flₙ n)))
                                  (sym (clampᵣ-rat
                                    (clampL n) (clampU n) v))))
                           (ibl n
                           (ℚ.clamp (clampL n) (clampU n) v)
                           (ℚ.clamp (clampL n) (clampU n) u)
                               (clampAbs≤ n v)
                               (clampAbs≤ n u)) )
                    u v)


boundedLipsch-coh : (f : ℚ → ℝ) (B B' : ℕ → ℚ₊)
    (bl : boundedLipschitz f B)
    (bl' : boundedLipschitz f B')
    → ∀ x →  BoundedLipsch.𝒇 f B bl x
           ≡ BoundedLipsch.𝒇 f B' bl' x
boundedLipsch-coh f B B' bl bl' =
                  ≡Continuous _ _
                   (BoundedLipsch.𝒇-cont f B bl)
                   (BoundedLipsch.𝒇-cont f B' bl')
                    λ r →
                      BoundedLipsch.𝒇-rat f B bl r ∙
                        sym (BoundedLipsch.𝒇-rat f B' bl' r)
