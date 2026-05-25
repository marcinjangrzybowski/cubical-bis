
module Cubical.HITs.CauchyReals.Alternating where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Relation.Nullary

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
-- open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
-- open import Cubical.HITs.CauchyReals.Integration
-- open import Cubical.HITs.CauchyReals.IntegrationMore
-- open import Cubical.HITs.CauchyReals.MeanValue
-- open import Cubical.HITs.CauchyReals.Exponentiation


open import Cubical.HITs.CauchyReals.LiftingExpr


open import Cubical.HITs.CauchyReals.RationalsImports 


open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Aproximations

open import Cubical.Algebra.Ring.BigOps 

open import Cubical.Data.Rationals.Bisection

-- isPropOpositeSigns : ∀ a b → isProp (((a ℚ.< 0) × (0 ℚ.< b)) ⊎ (((0  ℚ.< a) × (b ℚ.< 0))))
-- isPropOpositeSigns a b (inl x) (inl x₁) = {!isProp× (ℚ.isProp< a 0) ((ℚ.isProp< 0 a) !}
-- isPropOpositeSigns a b (inl x) (inr x₁) = {!!}
-- isPropOpositeSigns a b (inr x) (inl x₁) = {!!}
-- isPropOpositeSigns a b (inr x) (inr x₁) = {!!}

-- isAlternatingℚ : (ℕ → ℚ) → Type
-- isAlternatingℚ seq  = ∀ k →
--   ((seq k ℚ.< 0) × (0 ℚ.< (seq (suc k)))) ⊎ (((0  ℚ.< seq k) × ((seq (suc k)) ℚ.< 0)))

-- open Sum Rℚ.ℚRing 


isAlternatingℚ : (ℕ → ℚ) → Type
isAlternatingℚ s = ∀ k → (0 ℚ.< s (k ℕ.· 2)) × (s (suc (k ℕ.· 2)) ℚ.< 0)  

_∣2 : ℕ → ℕ
_∣2 = ℕ._mod 2

∣2-cases : ∀ k → ((k ∣2 ≡ 0) × ((suc k) ∣2 ≡ 1) × (Σ[ k' ∈ ℕ ] (k' ℕ.· 2 ≡ k)))
               ⊎.⊎ ((k ∣2 ≡ 1) × ((suc k) ∣2 ≡ 0) × (Σ[ k' ∈ ℕ ] (suc (k' ℕ.· 2) ≡ k)) ) 
∣2-cases zero = inl (refl , refl , (0 , refl))
∣2-cases (suc zero) = inr (refl , refl ,(0 , refl))
∣2-cases (suc (suc k)) = ⊎.map (map-snd (map-snd (λ (k' , p) → (suc k') , cong (suc ∘ suc) p)))
    ((map-snd (map-snd (λ (k' , p) → (suc k') , cong (suc ∘ suc) p)))) (∣2-cases k)

-- ∣2-cases' : ∀ k → ((k ∣2 ≡ 0) × (Σ[ k' ∈ ℕ ] (k' ℕ.· 2 ≡ k)))
--                ⊎.⊎ ((k ∣2 ≡ 1) × (Σ[ k' ∈ ℕ ] (suc (k' ℕ.· 2) ≡ k)) ) 
-- ∣2-cases' = ?

striclyDecrAltSeq : (ℕ → ℚ) → Type
striclyDecrAltSeq s = ∀ k → ((ℚ.- (s (suc (k ℕ.· 2))) ℚ.< s (k ℕ.· 2))
     × (s (suc (suc (k ℕ.· 2)))  ℚ.< (ℚ.- s (suc (k ℕ.· 2)))))


cutoffReduce : ℚ₊ → ℚ → ℚ
cutoffReduce ε q =
  [ integralPart / 1 ] ℚ.· (fst ε/2)
 where
  ε/2 = ε /2₊
  open ℚ.Floor ((ℚ.floorℚ (q ℚ.／₊ ε/2)))

module AlternatingSeries s
        (as : isAlternatingℚ s)
        (sd : striclyDecrAltSeq s)
        where

 altΣboundedByEven : ∀ k → ℚ.seqΣ s k ℚ.≤ ℚ.seqΣ s (k ℕ.∸ ((suc k) ∣2))
 altΣboundedByEven zero = ℚ.isRefl≤ _
 altΣboundedByEven (suc zero) = ℚ.isRefl≤ _
 altΣboundedByEven (suc (suc k)) =  ⊎.rec
      (λ { (p , _ , zero , v) → ⊥.rec (znots v) ;
        (p , _ , suc k' , v) →
           let v' = cong ℕ.predℕ v
           in subst2 ℚ._≤_
                     (λ i → ℚ.seqΣ s (suc (v i)))
                     (λ i → ℚ.seqSumUpTo' s ((suc (v i)) ℕ.∸ (p (~ i))))

                    (ℚ.isRefl≤ _) })
      (λ (p , _ , k' , v) →
        let v' = cong ℕ.predℕ v
        in subst2 ℚ._≤_
              (λ i → ℚ.seqSumUpTo' s k ℚ.+ s k ℚ.+ s (v i))
              (λ i → ℚ.seqΣ s (suc (suc k) ℕ.∸ (p (~ i))))
                (<≤ℚ![ snd (as k') ]))
       (∣2-cases (suc k))

 oddΣIncr : ∀ k m → ℚ.seqΣ s (k ℕ.∸ (k ∣2)) ℚ.≤ ℚ.seqΣ s ((m ℕ.+ k) ℕ.∸ ((m ℕ.+ k) ∣2))
 oddΣIncr  k zero = ℚ.isRefl≤ _
 oddΣIncr k (suc zero) = ⊎.rec
   (λ (p , q , k' , v) →
     subst2 ℚ._≤_
       (λ i → ℚ.seqΣ s (k ∸ (p (~ i))))
       (λ i → ℚ.seqΣ s (suc k ∸ (q (~ i))))
       (ℚ.isRefl≤ _ ))
   (λ (p , q , k' , v) →
     subst2 ℚ._≤_
       (λ i → ℚ.seqΣ s ((v i) ∸ (p (~ i))))
       (λ i → ℚ.seqΣ s (suc (v i) ∸ (q (~ i))))
         ( <≤ℚ![ fst (sd k') ]))
   (∣2-cases k)
 oddΣIncr  k (suc (suc m)) =
     ℚ.isTrans≤ _ (ℚ.seqΣ s (suc k ∸ (suc k ∣2))) _
       (oddΣIncr  k 1)
       (subst (_ ℚ.≤_)
         (λ i → ℚ.seqΣ s (suc (ℕ.+-suc m k i ) ∸ (suc (ℕ.+-suc m k i) ∣2)))
          (oddΣIncr  (suc k) (suc m)))


 evenΣDecr : ∀ k m → 0 ℕ.< k → 
     ℚ.seqΣ s ((m ℕ.+ k) ℕ.∸ ((suc (m ℕ.+ k) ∣2)))
      ℚ.≤ ℚ.seqΣ s (k ℕ.∸ ((suc k) ∣2))
 evenΣDecr  k zero _ = ℚ.isRefl≤ _
 evenΣDecr  k (suc zero) (k* , p*) =
   ⊎.rec
   (λ (p , q , k' , v) →
     subst2 ℚ._≤_
       (λ i → ℚ.seqΣ s (suc k ∸ (q (~ i))))
       (λ i → ℚ.seqΣ s (k ∸ (p (~ i))))
     (ℚ.isRefl≤ _)
       )
   (λ {  (p , q , zero , v) →
         let v' = cong predℕ v
         in transport  (λ i → let k = (v' i) in
                         ℚ.seqΣ s (suc k ∸ (k ∣2))
                          ℚ.≤ ℚ.seqΣ s (k ∸ ((suc k) ∣2)))
          (⊥.rec (znots (v' ∙ sym p* ∙  (ℕ.+-suc k* zero))))
       ; (p , q , (suc k') , v) →
      let v' = cong predℕ v
      in subst2 ℚ._≤_
              (λ i → ℚ.seqΣ s (suc (v' i) ℕ.∸ (q (~ i))))
              (λ i → ℚ.seqΣ s (v' i ℕ.∸ (p (~ i))))
            (<≤ℚ![ snd (sd k') ]) })
   (∣2-cases (suc k))
 evenΣDecr k (suc (suc m)) 0<k =
      ℚ.isTrans≤ _ (ℚ.seqΣ s (suc k ∸ (suc (suc k) ∣2))) _
       (subst (ℚ._≤ _) (λ i → ℚ.seqΣ s (suc (ℕ.+-suc m k i ) ∸ (suc (suc (ℕ.+-suc m k i)) ∣2)))
        (evenΣDecr (suc k) (suc m) (ℕ.≤-suc {1} {k} 0<k)))
       (evenΣDecr  k 1 0<k)

 abs≡⊔-⊓ : ∀ x y → ℚ.max x y ℚ.- ℚ.min x y ≡ abs (x ℚ.- y)  
 abs≡⊔-⊓ = ℚ.elimBy≤
   (λ x y X →
     ( (cong₂ ℚ._-_ (ℚ.maxComm y x) (ℚ.minComm y x)))
        ∙∙ X ∙∙
       ℚ.absComm- x y)
   λ x y x≤y →
     sym (ℚ.absNonNeg _ (ℚ.-≤ (ℚ.min x y) (ℚ.max x y)
        (ℚ.isTrans≤ _ _ _ (ℚ.min≤ x y) (ℚ.≤max x y)))) ∙ cong abs
       (cong₂ ℚ._-_
         (ℚ.≤→max _ _ x≤y) (ℚ.≤→min _ _ x≤y))
      ∙ ℚ.absComm- y x


 distBroaden : ∀ x y a b 
   → b ℚ.≤ x → b ℚ.≤ y → x ℚ.≤ a → y ℚ.≤ a  
   → abs (x ℚ.- y) ℚ.≤ abs (a ℚ.- b)
 distBroaden x y a b b≤x b≤y x≤a y≤a =
  subst2 ℚ._≤_
       (abs≡⊔-⊓ x y)
       (sym (ℚ.absNonNeg (a ℚ.- b) (ℚ.-≤ b a (ℚ.isTrans≤ _ _ _ b≤y y≤a))))
         (+Mono≤ (ℚ.max x y) a (ℚ.- (ℚ.min x y)) (ℚ.- b)
          (subst (_ ℚ.≤_) (ℚ.maxIdem a) (ℚ.≤MonotoneMax x a y a x≤a y≤a))
           (ℚ.minus-≤ b (ℚ.min x y)
            ((subst (ℚ._≤ _) (ℚ.minIdem b) (ℚ.≤MonotoneMin b x b y b≤x b≤y)))))

 altΣboundedByOdd : ∀ k → ℚ.seqΣ s (k ℕ.∸ (k ∣2)) ℚ.≤ ℚ.seqΣ s k 
 altΣboundedByOdd  zero = ℚ.isRefl≤ _
 altΣboundedByOdd  (suc k) = ⊎.rec
      (λ { (p , _ ,  zero , v) → ⊥.rec (znots v) ;
        (p , _ , suc k' , v) →
           let v' = cong ℕ.predℕ v
           in subst2 ℚ._≤_
                     (λ i → ℚ.seqΣ s (suc k ∸ (p (~ i))))
                     refl
                     (ℚ.isRefl≤ _)})
      (λ (p , _ , k' , v) →
        let v' = cong ℕ.predℕ v
        in subst2 ℚ._≤_
              (λ i → ℚ.seqΣ s (v i ∸ (p (~ i))))
              (λ i → ℚ.seqΣ s (v i))
              (<≤ℚ![ fst (as k') ]))
       (∣2-cases (suc k))

 even-odd-Σ-dist : ∀ N → 0 ℕ.< N → abs (ℚ.seqΣ s (N ∸ (N ∣2)) ℚ.- ℚ.seqΣ s (N ∸ (suc N ∣2))) ≡
        abs (s (predℕ N))
 even-odd-Σ-dist zero x = ⊥.rec (ℕ.¬-<-zero x)
 even-odd-Σ-dist  (suc N) x =
      ⊎.rec
       (λ { (p , _ ,  zero , v) → ⊥.rec (znots v) ;
        (p , q , suc k' , v) →
           let v' = cong ℕ.predℕ v
           in cong abs ((λ i → ℚ.seqΣ s (v (~ i) ∸ (p (i))) ℚ.-
                        ℚ.seqΣ s (v (~ i) ∸ (q (i))))
                     ∙∙  ℚ!!
                     ∙∙ cong (s ∘ predℕ) v)})
      (λ (p , q , k' , v) →
        let v' = cong ℕ.predℕ v
        in (λ i → abs (ℚ.seqΣ s (v (~ i) ∸ p i) ℚ.-
                ℚ.seqΣ s (v (~ i) ∸ q i)))
              ∙∙ cong {x = (ℚ.seqΣ s (v (~ i1) ∸ p i1) ℚ.-
                ℚ.seqΣ s (v (~ i1) ∸ q i1))}
                   {y = ℚ.- s (k' ℕ.· 2)} abs ℚ!!
              ∙∙ λ i → abs- (s (v' (i))) (i))
       (∣2-cases (suc N))

 cauchyByAlt' : 
                   ∀ N → 0 ℕ.< N → ∀ n m →   
                      abs (ℚ.seqΣ s (n ℕ.+ N) ℚ.- ℚ.seqΣ s (m ℕ.+ N)) ℚ.≤
                         abs (s (predℕ N)) 
 cauchyByAlt'  N 0<N n m  =
   ℚ.isTrans≤ _ _ _
     (distBroaden _ _ _ _
       (ℚ.isTrans≤ _ _ _ 
         (oddΣIncr  N n)
         (altΣboundedByOdd (n ℕ.+ N)))
       ((ℚ.isTrans≤ _ _ _ 
         (oddΣIncr  N m)
         (altΣboundedByOdd (m ℕ.+ N))))
      (ℚ.isTrans≤ _ _ _ (altΣboundedByEven  (n ℕ.+ N))
         (evenΣDecr N n 0<N))
      ((ℚ.isTrans≤ _ _ _ (altΣboundedByEven (m ℕ.+ N))
         (evenΣDecr N m 0<N))))
     (ℚ.≡Weaken≤ _ _ (ℚ.absComm- (ℚ.seqΣ s (N ∸ (suc N ∣2))) (ℚ.seqΣ s (N ∸ (N ∣2))) ∙ (even-odd-Σ-dist N 0<N)))

 cauchyByAlt : ∀ N n m → N ℕ.< m → N ℕ.< n →    
                      abs (ℚ.seqΣ s n ℚ.- ℚ.seqΣ s m) ℚ.≤
                         abs (s N) 

 cauchyByAlt N zero _ N<m N<n = ⊥.rec (ℕ.¬-<-zero N<n)
 cauchyByAlt N _ zero N<m N<n = ⊥.rec (ℕ.¬-<-zero N<m)
 cauchyByAlt N (suc n) (suc m) (m' , p) (n' , q) = 
   subst (ℚ._≤ _) (λ i → abs (ℚ.seqΣ s (q i) ℚ.- ℚ.seqΣ s (p i)))
    (cauchyByAlt' (suc N) ℕ.zero-<-suc n' m')

 module WithLim (s→0 : (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n → abs (s n) ℚ.< fst ε)) where
  isCauchyAltSeries : IsCauchySequence' (rat ∘ ℚ.seqΣ s)
  isCauchyAltSeries ε =
    let N , cs = s→0 ε
    in suc N , λ n m <n <m →
       isTrans≡<ᵣ _ _ _
         (cong absᵣ ( -ᵣ-rat₂ (ℚ.seqΣ s m) (ℚ.seqΣ s n)) ∙ absᵣ-rat (ℚ.seqΣ s m ℚ.- ℚ.seqΣ s n))
          (<ℚ→<ᵣ _ _ (ℚ.isTrans≤< _ _ _ (cauchyByAlt (suc N) m n <m <n)
          (cs (suc N) ℕ.≤-refl)))

module MkAlternating (s : ℕ → ℚ₊)
      (s-decr : ∀ k → fst (s (suc k)) ℚ.< fst (s k))
      (s→0 : (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n →  (fst (s n)) ℚ.< fst ε))
         where
 s' : ℕ → ℚ        
 s' k = ℚ.-1ⁿ· k (fst (s k))
 as : isAlternatingℚ s'
 as k = subst (0 ℚ.<_) (sym (ℚ.-1ⁿ·-·2 k (fst (s _)))) (snd (s _)) ,
    subst (ℚ._< 0) (cong ℚ.-_ (sym (ℚ.-1ⁿ·-·2 k (fst (s (suc (k ℕ.· 2)))))) ∙
            sym (ℚ.-1ⁿ·-suc (k ℕ.· 2) _)) 
     (ℚ.minus-< _ _ (snd (s _)))

 -- sd : striclyDecrAltSeq s'
 -- sd k = {!!} , {!!}
 
 -- open AlternatingSeries s' as sd
 -- open WithLim ( (λ {a} → map-snd (λ {N} X n N<n → subst (ℚ._< fst a)
 --  (sym (ℚ.absPos _ (snd (s n))) ∙ sym (ℚ.absᵣ∘-1ⁿ· n (fst (s n)))) (X n N<n)))
 --                    ∘ s→0)

module FueleldSum (s : ℕ → ℚ) where
 defaultFuel : Fuel
 defaultFuel = 10000000000000000000

 module _ (ε : ℤ.ℤ × ℕ₊₁) where
  seqΣAltᶠ : Fuel → ℕ  → ℚ → ℚ →  (ℕ × ℚ) 
  seqΣAltᶠ zero _ _ _ = 0 , 0
  seqΣAltᶠ (suc x) n  sum s-n with ℚ.<Dec (s-n) [ ε ]
  ... | (yes _) = n , sum
  ... | (no _) = seqΣAltᶠ x (suc n) (ℚ.reduce (sum ℚ.+ ℚ.-1ⁿ· n (s-n))) (s (suc n))
  

 seqΣAlt : ℚ → (ℕ × ℚ)
 seqΣAlt ε = seqΣAltᶠ (fst (ℚ.reduced ε)) defaultFuel 0 0 (s 0)

 -- seqΣAlt : ℚ → (ℕ × ℚ)
 -- seqΣAlt ε = seqΣAltᶠ (fst (ℚ.reduced ε)) defaultFuel 0 0 (s 0)


module Trig where
 module _ (x : ℚ) where
  expℚseq : ℕ → ℚ
  expℚseq n = (x ℚ.^ⁿ n) ℚ.／₊ !₊ n 

  sinℚseq : ℕ → ℚ
  sinℚseq n = expℚseq (suc (n ℕ.· 2))

  cosℚseq : ℕ → ℚ
  cosℚseq n = expℚseq (n ℕ.· 2)

  tan⁻¹ℚseq : ℕ → ℚ
  tan⁻¹ℚseq n = (x ℚ.^ⁿ (suc (n ℕ.· 2))) ℚ.·  [ 1 / 1+ (n ℕ.· 2) ]


  

  sinᶠ : (ε : ℚ) → ℕ × ℚ
  sinᶠ = FueleldSum.seqΣAlt (sinℚseq)

  cosᶠ : (ε : ℚ) → ℕ × ℚ
  cosᶠ = FueleldSum.seqΣAlt (cosℚseq)

 pi-tan⁻¹ℚseq : ℕ → ℚ
 pi-tan⁻¹ℚseq n = (16 ℚ.· tan⁻¹ℚseq [ 1 / 5 ] n) ℚ.- (4 ℚ.· tan⁻¹ℚseq [ 1 / 239 ] n)

 piByTans : (ε : ℚ) → ℕ × ℚ
 piByTans = FueleldSum.seqΣAlt pi-tan⁻¹ℚseq 

-- 16 tan−1
-- (1/5) − 4 tan−1
-- (1/239).

 bishop-π/2S : ℕ₊₁ → ℕ → ℚ → ℚ
 bishop-π/2S d zero q = q 
 bishop-π/2S d (suc n) q =
   let N = 32
       ε = [ 1 / (d ·₊₁ N) ]₊ 
       (_ , v) = cosᶠ (cutoffReduce ε q) (fst ε ℚ.· [ 1 / 2 ] )
       (d' , d'') = fst (ℚ.reduced v)
       d''' =( ℕ₊₁→ℕ d'') ℕ.mod (ℤ.abs d') 
       q' = q ℚ.+ v 
   in bishop-π/2S (1+ d''') n q'
   -- ℚ.reduce (q ℚ.+ v) ℚ.+ ℚ.reduce (bishop-π/2S d n q')
   -- q' ℚ.+ v 
  
 eee : ℕ × (ℕ × ℕ)
 eee = map-snd (digits 50) (piByTans [ 1 / 100000000000000000000000000000000000000000000000000000 ])

 _ : _
 _ = ?
 --37 , 3 , 14159265358979323846264338327950288419716939937510
      --  3 . 14159265358979323846264338327950288419716939937510

 

 bishop-π/2 : ℕ₊₁ → ℕ → (ℕ × ℕ) 
 bishop-π/2 m s = digits 40 (2 ℚ.· ( (bishop-π/2S m s 1)))
 
 _ : _
 _ = {!bishop-π/2 10 3!}
 --  3.  14159265358979323846264338327950288419716939937510

--   -- open MkAlternating sinℚseq {!!} {!!}  
-- -- -- -- -- alternating×cauchy→convSeries : ∀ seq
-- -- -- -- --     → isAlternatingℚ seq → IsCauchySequence' (rat ∘ seq)
-- -- -- -- --     → IsConvSeries' (rat ∘ seq)
-- -- -- -- -- alternating×cauchy→convSeries seq alt cauchy = {!!}


-- -- -- -- --  -- where
-- -- -- -- --  --  ?

-- -- -- -- ℚ.seqSumUpTo' s k ℚ.+ s k ℚ.+
-- -- -- --  s (suc k) ℚ.≤
-- -- -- --       ℚ.seqSumUpTo' s (k ℕ.+ Agda.Builtin.Nat.mod-helper 1 1 k 0) ℚ.+
-- -- -- --       s (k ℕ.+ Agda.Builtin.Nat.mod-helper 1 1 k 0)
-- -- -- --       ℚ.+ s (suc (k ℕ.+ Agda.Builtin.Nat.mod-helper 1 1 k 0))
-- -- -- -- Have: ℚ.seqSumUpTo' s k ℚ.+ s k ℚ.≤
-- -- -- --       ℚ.seqSumUpTo' s (k ℕ.+ Agda.Builtin.Nat.mod-helper 0 1 k 1) ℚ.+
-- -- -- --       s (k ℕ.+ Agda.Builtin.Nat.mod-helper 0 1 k 1)
