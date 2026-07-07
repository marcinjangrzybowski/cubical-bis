{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.MeanValue where

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
open import Cubical.Data.Int.Fast.Base as ℤ using (pos; ℕ₊₁→ℤ; _·_; _-_)
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
open import Cubical.HITs.CauchyReals.Summation
open import Cubical.HITs.CauchyReals.Partition
open import Cubical.HITs.CauchyReals.Integration

open import Cubical.HITs.CauchyReals.RationalsImports

open import Cubical.Tactics.CommRingSolver.Specialised.Reals




Bishop-Proposition7 : ∀ n (f : Fin n → ℝ)
 → 0 <ᵣ foldlFin {n = n} (λ a k → a +ᵣ f k) 0 (idfun (Fin n))
 → ∃[ k ∈ Fin n ] 0 <ᵣ f k
Bishop-Proposition7 zero f x = ⊥.rec (isIrrefl<ᵣ 0 x)
Bishop-Proposition7 (suc n) f x =
  PT.rec squash₁
  (λ (ε , 0<ε , ε<∑) →
    let ε₊ = (ε , ℚ<→0< ε (<ᵣ→<ℚ 0 ε 0<ε))
    in PT.rec squash₁
          (⊎.rec
            (λ f0<ε/2 →
              let tail = foldlFin {n = n} (λ a y → a +ᵣ f y) 0 fsuc
                  tail-cancel :
                    -ᵣ (f fzero) +ᵣ (f fzero +ᵣ tail)
                      ≡ foldlFin {n = n} (λ a y → a +ᵣ f y) 0 (fsuc ∘ idfun (Fin n))
                  tail-cancel =
                    +ᵣAssoc (-ᵣ (f fzero)) (f fzero) tail
                    ∙ cong (_+ᵣ tail)
                        (+ᵣComm (-ᵣ (f fzero)) (f fzero) ∙ +-ᵣ (f fzero))
                    ∙ +IdL tail
                    ∙ cong (foldlFin {n = n} (λ a y → a +ᵣ f y) 0)
                        (funExt λ k → refl)
                  zz : 0 <ᵣ foldlFin {n = n}
                    (λ a k → a +ᵣ (f ∘ fsuc) k) 0 (idfun (Fin n))
                  zz = isTrans<≡ᵣ _ _ _ (isTrans<ᵣ _ _ _
                       (snd (ℚ₊→ℝ₊ (ε₊ /2₊))) (isTrans≡<ᵣ _ _ _
                        (ℝ! ∙
                          cong₂ _+ᵣ_ refl (+ᵣ-rat (fst (ε₊ /2₊)) (fst (ε₊ /2₊))
                           ∙ cong rat (ε/2+ε/2≡ε ε)))
                        (<ᵣMonotone+ᵣ _ _ _ _
                         (-ᵣ<ᵣ _ _ f0<ε/2)
                          (isTrans<≡ᵣ _ _ _ ε<∑
                            (foldFin+0ᵣ n fsuc f (0 +ᵣ f fzero)
                             ∙ cong₂ _+ᵣ_ (+IdL (f fzero)) refl)))))
                          (tail-cancel ∙ foldFin+map n 0 f fsuc (idfun (Fin n)))
                  z = Bishop-Proposition7 n (f ∘ fsuc) zz
              in PT.map ((_ ,_) ∘ snd) z)
            (∣_∣₁ ∘ (_ ,_)))
        ((Dichotomyℝ' 0 (f fzero) (rat (fst (ε₊ /2₊))) (snd (ℚ₊→ℝ₊ (ε₊ /2₊))) )))
  (denseℚinℝ 0
    (foldlFin {n = suc n} (λ a k → a +ᵣ f k) 0 (idfun (Fin (suc n))))
    x)



Fin-∀A⊎∃B : ∀ n → (A B : Fin n → Type₀)
           → (∀ k → ∥ A k ⊎ B k ∥₁)
           → ∥ (∀ k → A k) ⊎ Σ (Fin n) B ∥₁

Fin-∀A⊎∃B zero A B ab? = ∣ inl (⊥.rec ∘ ¬Fin0) ∣₁
Fin-∀A⊎∃B (suc n) A B ab? =
  PT.map2
     (⊎.rec (λ a0 →
       ⊎.map (λ ∀kA →
              λ x → ⊎.rec
                (λ p → subst A p a0)
                (λ (k , p) → subst A p (∀kA k))
                (fsplit x))
        λ (k , bk) → fsuc k , bk) (λ b0 _ → inr (fzero , b0)))
    (ab? fzero)
    (Fin-∀A⊎∃B n (A ∘ fsuc) (B ∘ fsuc) (ab? ∘ fsuc))

ε<abs→ε<⊎<-ε : ∀ (ε : ℝ₊) x → fst ε <ᵣ absᵣ x →
                        (x <ᵣ -ᵣ (fst ε)) ⊎ (fst ε <ᵣ x)
ε<abs→ε<⊎<-ε ε x ε<∣x∣ =

   ⊎.map (λ x<0 → isTrans≡<ᵣ _ _ _
        (sym (-ᵣInvol _) ∙
         cong -ᵣ_ (sym (absᵣNeg _ x<0))) (-ᵣ<ᵣ _ _ ε<∣x∣))
      (λ 0<x → isTrans<≡ᵣ _ _ _ ε<∣x∣ (absᵣPos _ 0<x))
   (invEq (＃≃0<dist x 0)
      (isTrans<≡ᵣ _ _ _
        (isTrans<ᵣ _ _ _ (snd ε) ε<∣x∣)
        (cong absᵣ (sym (Rℝ.+IdR' _ _ (-ᵣ-rat 0))))))

equalPartitionStrict∃ : ∀ a b → a <ᵣ b → (ε : ℚ₊) →
 ∃[ pa ∈ Partition[ a , b ] ] (isStrictPartition pa × mesh≤ᵣ pa (rat (fst ε)))
equalPartitionStrict∃ a b a<b ε =
  PT.map
    (λ (x' , b-a<x' , _) →
      let x'₊ : ℚ₊
          x'₊ = (x' , ℚ<→0< x'
                (<ᵣ→<ℚ 0 x' (isTrans≤<ᵣ 0 (b -ᵣ a) (rat x')
                  (x≤y→0≤y-x a b a≤b) b-a<x')))
          (1+ N , p) = ℚ.ceilℚ₊ (invℚ₊ ε ℚ₊· x'₊)
          ww : fst (x'₊ ℚ₊· invℚ₊ ε) ℚ.≤ fromNat (suc N)
          ww = ℚ.<Weaken≤ _ _
            (subst (ℚ._< fromNat (suc N))
              (ℚ.·Comm (fst (invℚ₊ ε)) x') p)

      in ∫ab.equalPartition N ,
          ∫ab.isStrictEqualPartition a<b N ,
          λ k → isTrans≤ᵣ _ _ _ (∫ab.equalPartition-mesh N k)
            (isTrans≤ᵣ _ _ _
              (isTrans≤≡ᵣ _ _ _ (≤ᵣ-·ᵣo _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos 1 (1+ N)))
                (<ᵣWeaken≤ᵣ _ _ b-a<x'))
                (sym (rat·ᵣrat x' _)))
              (let N₂ : ℚ₊
                   N₂ = fromNat (suc N)
                   x'≤ε·N₂ : x' ℚ.≤ fst ε ℚ.· fst N₂
                   x'≤ε·N₂ = x·invℚ₊y≤z→x≤y·z x' (fst N₂) ε ww
                   x'·invN₂≤ε : x' ℚ.· fst (invℚ₊ N₂) ℚ.≤ fst ε
                   x'·invN₂≤ε = x≤y·z→x·invℚ₊y≤z x' N₂ (fst ε) x'≤ε·N₂
               in ≤ℚ→≤ᵣ _ _
                 (subst (λ q → x' ℚ.· q ℚ.≤ fst ε)
                   (invℚ₊-fromNat N)
                   x'·invN₂≤ε))))
    (denseℚinℝ (b -ᵣ a) ((b -ᵣ a) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 (b -ᵣ a) decℚ<ᵣ?)))
  where
  a≤b : a ≤ᵣ b
  a≤b = <ᵣWeaken≤ᵣ a b a<b

  module ∫ab = EqualPartition a b a≤b


allOnOneSideLemma : ∀ n (ε : ℝ₊) (f : Fin (suc n) → ℝ)
            → (∀ k → absᵣ (f (fsuc k) -ᵣ f (finj k)) <ᵣ fst ε )
            → (∀ k → (f k <ᵣ -ᵣ (fst ε  ·ᵣ rat (fst [ 1 / 2 ]₊)))
                ⊎ (fst ε ·ᵣ rat (fst [ 1 / 2 ]₊) <ᵣ f k))

            → (∀ k → f k <ᵣ -ᵣ (fst ε  ·ᵣ rat (fst [ 1 / 2 ]₊))) ⊎
              (∀ k → fst ε  ·ᵣ rat (fst [ 1 / 2 ]₊) <ᵣ f k)
allOnOneSideLemma zero ε f fΔ f⊎ =
  ⊎.map
    (λ f0 k → isTrans≡<ᵣ _ _ _ (cong f (sym (snd (isContrFin1) k) )) f0)
    (λ f0 k → isTrans<≡ᵣ _ _ _ f0 (cong f (snd (isContrFin1) k)))
    (f⊎ fzero)
allOnOneSideLemma (suc n) ε f fΔ f⊎ =
  ⊎.map
    (λ fs → ⊎.rec
           (λ f0< →
             λ { (zero , p) →
                   isTrans≡<ᵣ _ _ _ (cong f (toℕ-injective {k = suc (suc n)} refl)) f0<
               ; (suc k , p) →
                  isTrans≡<ᵣ _ _ _ (cong f (toℕ-injective {k = suc (suc n)} refl))
                   (fs (k , p))})
           (λ <f0 _ →
              ⊥.rec
                 (isAsym<ᵣ (fst ε)
                           (absᵣ (f (fsuc fzero) -ᵣ f (finj fzero)))
                   (isTrans<≤ᵣ _ _ _
                     (isTrans≡<ᵣ _ _ _
                     ((sym (Rℝ.·IdR'
                       (fst ε)
                       (rat (fst [ 1 / 2 ]₊) +ᵣ rat (fst [ 1 / 2 ]₊))
                       (+ᵣ-rat (fst [ 1 / 2 ]₊) (fst [ 1 / 2 ]₊)
                        ∙ decℚ≡ᵣ?
                          {x = fst [ 1 / 2 ]₊ ℚ.+ fst [ 1 / 2 ]₊}
                          {y = 1}))
                      ∙ ·DistL+ _ _ _ )
                      ∙ cong₂ _+ᵣ_
                        (sym (-ᵣInvol _))
                        refl)
                      (<ᵣMonotone+ᵣ _ _ _ _ (-ᵣ<ᵣ _ _ (fs fzero)) (<f0)))
                      (isTrans≤≡ᵣ _ _ _
                        (≤absᵣ _)
                        (cong absᵣ (+ᵣComm _ _)
                          ∙ minusComm-absᵣ _ _)))
                     (fΔ fzero)
                     ))
       (f⊎ (finj fzero)))
    (λ fs → ⊎.rec
           (λ f0< → ⊥.rec
                 ((isAsym<ᵣ (fst ε)
                           (absᵣ (f (fsuc fzero) -ᵣ f (finj fzero)))
                  ((isTrans<≤ᵣ _ _ _
                     (isTrans≡<ᵣ _ _ _
                     ((sym (Rℝ.·IdR'
                       (fst ε)
                       (rat (fst [ 1 / 2 ]₊) +ᵣ rat (fst [ 1 / 2 ]₊))
                       (+ᵣ-rat (fst [ 1 / 2 ]₊) (fst [ 1 / 2 ]₊)
                        ∙ decℚ≡ᵣ?
                          {x = fst [ 1 / 2 ]₊ ℚ.+ fst [ 1 / 2 ]₊}
                          {y = 1}))
                      ∙ ·DistL+ _ _ _ )
                      ∙ cong₂ _+ᵣ_ refl
                              (sym (-ᵣInvol _))
                        )
                          (isTrans<≡ᵣ _ _ _
                           (<ᵣMonotone+ᵣ _ _ _ _
                           (fs fzero) (-ᵣ<ᵣ _ _  (f0<)))
                           (+ᵣComm _ _ ∙
                             cong₂ _+ᵣ_
                              (cong (-ᵣ_ ∘ f) (toℕ-injective {k = suc (suc n)} refl))
                               refl)))
                      (isTrans≤≡ᵣ _ _ _
                        (≤absᵣ _)
                        (cong absᵣ (+ᵣComm _ _))))))
                           (fΔ fzero)))
           (λ <f0 →
               λ { (zero , p) →
                     isTrans<≡ᵣ _ _ _ <f0 (cong f (toℕ-injective {k = suc (suc n)} refl))
                 ; (suc k , p) →
                   isTrans<≡ᵣ _ _ _ (fs (k , p))
                      (cong f (toℕ-injective {k = suc (suc n)} refl))})
       (f⊎ fzero))
    (allOnOneSideLemma n ε (f ∘ fsuc)
      ((λ {a} → isTrans≡<ᵣ _ _ _
       (cong (λ ffa → absᵣ (f (fsuc (fsuc a)) -ᵣ f ffa))
        (toℕ-injective {k = suc (suc n)} refl) ))
       ∘ (fΔ ∘ fsuc))
       (f⊎ ∘ fsuc))


Rolle'sTheorem : ∀ a b → a <ᵣ b → ∀ a∈ b∈ f f'
  → IsUContinuousℙ (intervalℙ a b) f'
  → uDerivativeOfℙ (intervalℙ a b) , f is f'
  → f a a∈ ≡ f b b∈
  → ∀ (ε : ℚ₊) → ∃[ (x₀ , x∈) ∈ Σ ℝ (_∈ intervalℙ a b) ]
            absᵣ (f' x₀ x∈) <ᵣ rat (fst ε)
Rolle'sTheorem a b a<b a∈ b∈ f f' ucf udf fa≡fb ε =
  PT.rec squash₁ (w (ucf ε)) (udf (ε /2₊))

 where
 w : (Σ[ δ ∈ ℚ₊ ]
        (∀ u v u∈ v∈ → u ∼[ δ ] v → f' u u∈ ∼[ ε ] f' v v∈))
   → (Σ[ δ' ∈ ℚ₊ ]
        ((x : ℝ) (x∈ : x ∈ intervalℙ a b) (h : ℝ)
         (h∈ : x +ᵣ h ∈ intervalℙ a b)
         (0＃h : rat [ pos 0 / 1+ 0 ] ＃ h) →
         absᵣ h <ᵣ rat (fst δ') →
         absᵣ (f' x x∈ -ᵣ differenceAtℙ (intervalℙ a b) f x h 0＃h x∈ h∈)
           <ᵣ rat (fst (ε /2₊))))
   → ∃[ (x₀ , x∈) ∈ Σ ℝ (_∈ intervalℙ a b) ]
        absᵣ (f' x₀ x∈) <ᵣ rat (fst ε)
 w (δ , X) (δ' , X') = PT.rec squash₁ ww
   (equalPartitionStrict∃ a b a<b δ⊓δ')
  where
  δ⊓δ' = min₊ (δ /2₊) (δ' /2₊)


  ww : (Σ[ pa ∈ Partition[ a , b ] ]
         (isStrictPartition pa × mesh≤ᵣ pa (rat (fst δ⊓δ')))) →
       ∃[ (x₀ , x∈) ∈ Σ ℝ (_∈ intervalℙ a b) ]
        absᵣ (f' x₀ x∈) <ᵣ rat (fst ε)
  ww (pa , str-pa , mesh-pa) =
    PT.rec squash₁
      (⊎.rec
        (λ ∀ε/2<abs → ∀case λ k →
          ε<abs→ε<⊎<-ε (ℚ₊→ℝ₊ (ε /2₊))
            (f' (Pa.pts' k) (Pa.a≤pts' k , Pa.pts'≤b k))
            (∀ε/2<abs k))
             (∣_∣₁ ∘ (_ ,_) ∘ snd))
     (Fin-∀A⊎∃B (suc (suc Pa.len))
       (λ k → rat (fst (ε /2₊)) <ᵣ absᵣ (f' (Pa.pts' k)
         (Pa.a≤pts' k , Pa.pts'≤b k)))
       (λ k → absᵣ (f' (Pa.pts' k)
         (Pa.a≤pts' k , Pa.pts'≤b k)) <ᵣ rat (fst ε))
        λ k → PT.map (Iso.fun ⊎-swap-Iso) (Dichotomyℝ'
                   (rat (fst (ε /2₊)))
                   (absᵣ (f' (Pa.pts' k)
                     (Pa.a≤pts' k , Pa.pts'≤b k)))
                   ((rat (fst ε)))
                   (<ℚ→<ᵣ _ _ (x/2<x ε))))
   where
   module Pa = Partition[_,_] pa



   z : ∀ f f' → f a a∈ ≡ f b b∈ →
          ((x : ℝ) (x∈ : x ∈ intervalℙ a b) (h : ℝ)
           (h∈ : x +ᵣ h ∈ intervalℙ a b) (0＃h : rat [ pos 0 / 1+ 0 ] ＃ h) →
           absᵣ h <ᵣ rat (fst δ') →
           absᵣ (f' x x∈ -ᵣ differenceAtℙ (intervalℙ a b) f x h 0＃h x∈ h∈) <ᵣ
           rat (fst (ε /2₊)))
        → ∃-syntax (Fin (suc Pa.len))
        (λ k → (-ᵣ rat (fst ε))
          <ᵣ f' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k)))
   z f f' fa≡fb X' = PT.map
          (map-snd
           λ {l} X → 0<y-x→x<y _ _
             (isTrans<≡ᵣ _ _ _
              (isTrans≡<ᵣ _ _ _ (sym (Rℝ.0LeftAnnihilates _))
              (invEq (z/y<x₊≃z<y₊·x
                (f' (Pa.pts' (finj l))
                  (Pa.a≤pts' (finj l) , Pa.pts'≤b (finj l))
                  +ᵣ rat (fst ε))
                0
                (Pa.pts' (fsuc l) -ᵣ Pa.pts' (finj l) ,
                  x<y→0<y-x _ _ (str-pa l)))
                (isTrans<≡ᵣ _ _ _ X
                (·ᵣComm _ _))))
                (cong₂ _+ᵣ_ refl
                 (sym (-ᵣInvol _)))))
        (Bishop-Proposition7 (suc Pa.len)
        (λ k → (f' (Pa.pts' (finj k))
                     (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
                    +ᵣ rat (fst ε))
             ·ᵣ (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k)))
        z-pos)

    where
    <f : (k : Fin (suc Pa.len)) →
          f (Pa.pts' (fsuc k))
            (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k))
          -ᵣ
          f (Pa.pts' (finj k))
            (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
          <ᵣ
          (f' (Pa.pts' (finj k))
            (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
            +ᵣ rat (fst ε))
          ·ᵣ
          (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
    <f k = isTrans<ᵣ _ _ _ (isTrans<≡ᵣ _ _ _
      (fst (z/y<x₊≃z<y₊·x
        (f' (Pa.pts' (finj k))
          (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
          +ᵣ rat (fst (ε /2₊)))
        (f (Pa.pts' (fsuc k))
          (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k))
          -ᵣ f (Pa.pts' (finj k))
          (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k)))
        (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k) ,
          x<y→0<y-x _ _ (str-pa k)))
        fromX') (·ᵣComm _ _))
           (<ᵣ-·ᵣo _ _
             (_ , x<y→0<y-x _ _ (str-pa k))
            (<ᵣ-o+ _ _ _ (<ℚ→<ᵣ _ _ (x/2<x ε))))
     where
     fromX' :
       (f (Pa.pts' (fsuc k))
         (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k))
        -ᵣ f (Pa.pts' (finj k))
         (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k)))
       ·ᵣ fst (invℝ₊
         (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k) ,
          x<y→0<y-x _ _ (str-pa k)))
       <ᵣ
       f' (Pa.pts' (finj k))
         (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
       +ᵣ rat (fst (ε /2₊))
     fromX' = (isTrans≡<ᵣ _ _ _
       (cong₂ _·ᵣ_
         (cong₂ _-ᵣ_
           (cong (uncurry f)
             (Σ≡Prop (∈-isProp (intervalℙ a b))
               (sym (u+[v-u]≡v (Pa.pts' (finj k)) (Pa.pts' (fsuc k))))) )
           refl)
        (invℝ₊≡invℝ (_ , x<y→0<y-x _ _ (str-pa k)) _))
       (isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _
        (isTrans≤<ᵣ _ _ _
         (≤absᵣ _)
         (isTrans≡<ᵣ _ _ _
          (minusComm-absᵣ _ _)
            (X' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
        (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
        (subst-∈ (intervalℙ a b)
          (sym (u+[v-u]≡v (Pa.pts' (finj k)) (Pa.pts' (fsuc k))))
           (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k)))
        (invEq (＃Δ _ _) (inl (str-pa k)))
        (isTrans≡<ᵣ _ _ _
          (absᵣNonNeg _ (x≤y→0≤y-x _ _ (Pa.pts'≤pts' k)))
          (isTrans≤<ᵣ _ _ _
            (isTrans≤ᵣ _ _ _
              (mesh-pa k)
              (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst (δ' /2₊))
                (ℚ.min≤' (fst (δ /2₊)) (fst (δ' /2₊)))))
            (<ℚ→<ᵣ _ _ (x/2<x δ'))))))))
            (+ᵣComm _ _)))

    Δ : Fin (suc Pa.len) → ℝ
    Δ k =
      f (Pa.pts' (fsuc k))
        (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k))
      -ᵣ f (Pa.pts' (finj k))
        (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))

    G : Fin (suc Pa.len) → ℝ
    G k =
      (f' (Pa.pts' (finj k))
        (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
        +ᵣ rat (fst ε))
      ·ᵣ (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))

    sumΔ sumG : ℝ
    sumΔ = foldlFin {n = suc Pa.len}
      (λ acc k → acc +ᵣ Δ k) 0 (idfun (Fin (suc Pa.len)))
    sumG = foldlFin {n = suc Pa.len}
      (λ acc k → acc +ᵣ G k) 0 (idfun (Fin (suc Pa.len)))

    z-sum-path : 0 ≡ sumΔ
    z-sum-path =
      sym (Rℝ.+InvR' (f b b∈) (f a a∈) (sym fa≡fb))
      ∙ cong₂ _-ᵣ_
          (cong (uncurry f)
            (Σ≡Prop (∈-isProp (intervalℙ a b)) (sym Pa.pts'-last)))
          (cong (uncurry f)
            (Σ≡Prop (∈-isProp (intervalℙ a b)) refl))
      ∙ sym (deltas-sum (suc Pa.len)
        λ k → f (Pa.pts' k) (Pa.a≤pts' k , Pa.pts'≤b k))

    z-fold-pos : sumΔ <ᵣ sumG
    z-fold-pos =
      foldFin+< Pa.len 0 0
        Δ G
        (idfun (Fin (suc Pa.len))) (idfun (Fin (suc Pa.len)))
        (≤ᵣ-refl 0)
        <f

    z-pos : 0 <ᵣ sumG
    z-pos = isTrans≡<ᵣ 0 sumΔ sumG z-sum-path z-fold-pos


   z' : ∃-syntax (Fin (suc Pa.len))
        (λ k → f' (Pa.pts' (finj k))
          (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
          <ᵣ rat (fst ε))
   z' = PT.map (map-snd (<ᵣ-ᵣ _ _))
          (z (λ x x∈ → -ᵣ (f x x∈))
               (λ x x∈ → -ᵣ (f' x x∈))
                (cong -ᵣ_ fa≡fb)
                 λ x x∈ h h∈ 0＃h h<δ' →
                  isTrans≡<ᵣ _ _ _
                     (cong absᵣ (sym (-ᵣDistr _ _)) ∙
                      sym (-absᵣ _)
                        ∙ cong (absᵣ ∘ (f' x x∈ +ᵣ_))
                          (cong (_·ᵣ invℝ h 0＃h)
                            (sym (-ᵣDistr _ _))
                            ∙ -ᵣ· _ _) )
                     (X' x x∈ h h∈ 0＃h h<δ'))


   ∀case : ((a₁ : Fin (suc (suc Pa.len))) →
            (f' (Pa.pts' a₁) (Pa.a≤pts' a₁ , Pa.pts'≤b a₁)
              <ᵣ -ᵣ fst (ℚ₊→ℝ₊ (ε /2₊)))
            ⊎
            (fst (ℚ₊→ℝ₊ (ε /2₊))
              <ᵣ f' (Pa.pts' a₁) (Pa.a≤pts' a₁ , Pa.pts'≤b a₁))) →
            ∃ (Σ ℝ (_∈ intervalℙ a b))
            (λ v → absᵣ (f' (v .fst) (v .snd)) <ᵣ rat (fst ε))
   ∀case =
        ⊎.rec
          (λ ∀f< → PT.map
              (λ (k , U) →
                (Pa.pts' (finj k) ,
                  (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))) ,
                 isTrans≡<ᵣ _ _ _
                   (abs-max _)
                    (max<-lem _ _ _
                      (isTrans<ᵣ _ _ _ (∀f< (finj k))
                        (isTrans<ᵣ _ 0 _
                          (isTrans<≡ᵣ _ _ _
                            (-ᵣ<ᵣ _ _
                              (snd ((ℚ₊→ℝ₊ ε) ₊·ᵣ ℚ₊→ℝ₊ [ 1 / 2 ]₊)))
                           (-ᵣ-rat 0)) (snd (ℚ₊→ℝ₊ ε))))
                      (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ U) (-ᵣInvol _))))
              (z f f' fa≡fb X'))
          (λ ∀<f → PT.map
             (λ (k , U) →
                (Pa.pts' (finj k) ,
                  (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))) ,
                 isTrans≡<ᵣ _ _ _
                   (abs-max _)
                    (max<-lem _ _ _ U
                      (isTrans<ᵣ _ _ _
                        (-ᵣ<ᵣ _ _ (∀<f (finj k)))
                        ((isTrans<ᵣ _ 0 _
                          (isTrans<≡ᵣ _ _ _
                            (-ᵣ<ᵣ _ _
                              (snd ((ℚ₊→ℝ₊ ε) ₊·ᵣ ℚ₊→ℝ₊ [ 1 / 2 ]₊)))
                           (-ᵣ-rat 0)) (snd (ℚ₊→ℝ₊ ε)))))))
             z')
     ∘  allOnOneSideLemma (suc Pa.len) (ℚ₊→ℝ₊ ε)
             (λ k → f' (Pa.pts' k) (Pa.a≤pts' k , Pa.pts'≤b k))
             (λ k → fst (∼≃abs<ε
               (f' (Pa.pts' (fsuc k))
                 (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k)))
               (f' (Pa.pts' (finj k))
                 (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k)))
               ε)
               (X (Pa.pts' (fsuc k)) (Pa.pts' (finj k))
                (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k))
                (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
                (invEq (∼≃abs<ε (Pa.pts' (fsuc k)) (Pa.pts' (finj k)) δ)
                  (isTrans≤<ᵣ _ _ _
                    (isTrans≡≤ᵣ _ _ _
                      (absᵣPos _ (x<y→0<y-x _ _ (str-pa k)))
                      (mesh-pa k))
                    (<ℚ→<ᵣ _ _
                     (ℚ.isTrans≤< (fst δ⊓δ') _ _
                       (ℚ.min≤ (fst (δ /2₊)) (fst (δ' /2₊)))
                       (x/2<x δ))
                     )))))
     ∘ (⊎.map (flip (isTrans<≡ᵣ _ _ _) (cong -ᵣ_ (rat·ᵣrat (fst ε) _)))
              (isTrans≡<ᵣ _ _ _ (sym (rat·ᵣrat (fst ε) _)))
         ∘_)

meanValue : ∀ a b → a <ᵣ b → ∀ a∈ b∈ f f'
       →  IsUContinuousℙ (intervalℙ a b) f'
       →  uDerivativeOfℙ (intervalℙ a b) , f is f'
       → (ε : ℚ₊) →
          ∃[ (x₀ , x∈) ∈ Σ ℝ (_∈ intervalℙ a b) ]
           absᵣ ((f b b∈ -ᵣ f a a∈)  -ᵣ f' x₀ x∈ ·ᵣ (b -ᵣ a)) <ᵣ rat (fst ε)
meanValue a b a<b a∈ b∈ f f' ucf udf =
  PT.rec (isPropΠ λ _ → squash₁) (λ uch' → Rolle'sTheorem a b a<b a∈ b∈
     h h' uch' udh ha≡hb)
      uch


 where
  h h' : (x : ℝ) → x ∈ intervalℙ a b → ℝ
  h x x∈ = ((x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈))
                -ᵣ f x x∈ ·ᵣ (b -ᵣ a)

  h' x x∈ = (f b b∈ -ᵣ f a a∈) -ᵣ f' x x∈ ·ᵣ (b -ᵣ a)

  uch : ∥ IsUContinuousℙ (intervalℙ a b) h' ∥₁
  uch = PT.map (λ z → IsUContinuous∘ℙ (intervalℙ a b)
       (IsUContinuous∘ (IsUContinuous+ᵣL (f b b∈ -ᵣ f a a∈))
          (subst IsUContinuous (funExt λ x → ·-ᵣ _ _)
            z))
       ucf) (IsUContinuous·ᵣR (-ᵣ (b -ᵣ a)))

  udh0 :
    uDerivativeOfℙ (intervalℙ a b) ,
      (λ x x∈ → (x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈)
        +ᵣ (-ᵣ (b -ᵣ a)) ·ᵣ f x x∈)
      is
      (λ x x∈ → (f b b∈ -ᵣ f a a∈)
        +ᵣ (-ᵣ (b -ᵣ a)) ·ᵣ f' x x∈)
  udh0 = +uDerivativeℙ (intervalℙ a b)
    (λ x _ → ((x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈)))
     (λ _ _ → (f b b∈ -ᵣ f a a∈))
    (λ x x∈ → (-ᵣ (b -ᵣ a)) ·ᵣ f x x∈)
    (λ x x∈ → (-ᵣ (b -ᵣ a)) ·ᵣ f' x x∈)
    (subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
      (funExt₂ λ x x∈ → ·ᵣComm _ _)
      (funExt₂ λ x x∈ → Rℝ.·IdR' _ _ (+IdR 1))
      (C·uDerivativeℙ (intervalℙ a b)
       (f b b∈ -ᵣ f a a∈)
       (λ x x∈ → x -ᵣ a)
       (λ x x∈ → 1 +ᵣ 0)
       (+uDerivativeℙ (intervalℙ a b)
        (λ x x∈ → x)
        (λ x x∈ → 1)
        (λ x x∈ → -ᵣ a)
        (λ x x∈ → 0)
        (uDerivativeℙ-id (intervalℙ a b))
        (uDerivativeℙ-const (intervalℙ a b) (-ᵣ a))) ))
    (C·uDerivativeℙ (intervalℙ a b) (-ᵣ (b -ᵣ a))
     (λ x x∈ → f x x∈)
     (λ x x∈ → f' x x∈)
     udf)

  udh : uDerivativeOfℙ (intervalℙ a b) , h is h'
  udh = subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
           (funExt₂ λ x x∈ →
            cong₂ _+ᵣ_ refl (-ᵣ· _ _ ∙ cong -ᵣ_ (·ᵣComm _ _)))
           (funExt₂ λ x x∈ →
            cong₂ _+ᵣ_ refl (-ᵣ· _ _ ∙ cong -ᵣ_ (·ᵣComm _ _)))
           udh0


  ha≡hb : h a a∈ ≡ h b b∈
  ha≡hb = Rℝ.+IdL' _ _ (Rℝ.0LeftAnnihilates' _ _ (+-ᵣ a))
    ∙ sym (-ᵣ· _ _)
    ∙ cong (_·ᵣ (b -ᵣ a)) (sym ℝ!)
    ∙ Rℝ.·DistL- (f b b∈ -ᵣ f a a∈) (f b b∈) (b -ᵣ a)
    ∙ cong₂ _-ᵣ_ (·ᵣComm _ _) refl

nullDerivative→const : ∀ a b a∈ b∈ → a <ᵣ b → ∀ f
       → uDerivativeOfℙ (intervalℙ a b) , f is (λ _ _ → 0)
       → f a a∈ ≡ f b b∈
nullDerivative→const a b a∈ b∈ a<b f udf  =
  eqℝ _ _ λ ε →
    PT.rec (isProp∼ _ _ _)
      (λ (_ , X) →
        sym∼ _ _ _ (invEq (∼≃abs<ε _ _ ε)
          (isTrans≡<ᵣ _ _ _
            (cong absᵣ
              (sym (Rℝ.+IdR' _ _
                (cong -ᵣ_ (Rℝ.0LeftAnnihilates (b -ᵣ a))
                 ∙ -ᵣ-rat 0))))
            X)))
      (meanValue a b a<b a∈ b∈ f
        (λ _ _ → 0) (λ ε₁ → 1 , λ _ _ _ _ _ → refl∼ 0 ε₁) udf ε)
