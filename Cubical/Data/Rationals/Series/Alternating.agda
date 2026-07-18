module Cubical.Data.Rationals.Series.Alternating where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.IsEven as Parity
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Properties
open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

AlternatesPositiveFirst : (ℕ → ℚ) → Type
AlternatesPositiveFirst s =
  ∀ k → (0 ℚ.< s (k ℕ.· 2)) × (s (suc (k ℕ.· 2)) ℚ.< 0)

_∣2 : ℕ → ℕ
_∣2 = Parity.mod2

∣2-cases : ∀ k → ((k ∣2 ≡ 0) × ((suc k) ∣2 ≡ 1) × (Σ[ k' ∈ ℕ ] (k' ℕ.· 2 ≡ k)))
               ⊎.⊎ ((k ∣2 ≡ 1) × ((suc k) ∣2 ≡ 0) × (Σ[ k' ∈ ℕ ] (suc (k' ℕ.· 2) ≡ k)))
∣2-cases = Parity.mod2-cases

StrictlyDecreasingAlternating : (ℕ → ℚ) → Type
StrictlyDecreasingAlternating s = ∀ k → ((ℚ.- (s (suc (k ℕ.· 2))) ℚ.< s (k ℕ.· 2))
     × (s (suc (suc (k ℕ.· 2))) ℚ.< (ℚ.- s (suc (k ℕ.· 2)))))


module AlternatingSeries s
        (as : AlternatesPositiveFirst s)
        (sd : StrictlyDecreasingAlternating s)
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
         (<≤ℚ![ fst (sd k') ]))
   (∣2-cases k)
 oddΣIncr  k (suc (suc m)) =
     ℚ.isTrans≤ _ (ℚ.seqΣ s (suc k ∸ (suc k ∣2))) _
       (oddΣIncr  k 1)
       (subst (_ ℚ.≤_)
         (λ i → ℚ.seqΣ s (suc (ℕ.+-suc m k i) ∸ (suc (ℕ.+-suc m k i) ∣2)))
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
          (⊥.rec (znots (v' ∙ sym p* ∙ (ℕ.+-suc k* zero))))
       ; (p , q , (suc k') , v) →
      let v' = cong predℕ v
      in subst2 ℚ._≤_
              (λ i → ℚ.seqΣ s (suc (v' i) ℕ.∸ (q (~ i))))
              (λ i → ℚ.seqΣ s (v' i ℕ.∸ (p (~ i))))
            (<≤ℚ![ snd (sd k') ]) })
   (∣2-cases (suc k))
 evenΣDecr k (suc (suc m)) 0<k =
      ℚ.isTrans≤ _ (ℚ.seqΣ s (suc k ∸ (suc (suc k) ∣2))) _
       (subst (ℚ._≤ _) (λ i → ℚ.seqΣ s (suc (ℕ.+-suc m k i) ∸ (suc (suc (ℕ.+-suc m k i)) ∣2)))
        (evenΣDecr (suc k) (suc m) (ℕ.≤-suc {1} {k} 0<k)))
       (evenΣDecr  k 1 0<k)

 abs≡⊔-⊓ : ∀ x y → ℚ.max x y ℚ.- ℚ.min x y ≡ abs (x ℚ.- y)
 abs≡⊔-⊓ = ℚ.elimBy≤
   (λ x y X →
     ( (cong₂ ℚ._-_ (ℚ.maxComm y x) (ℚ.minComm y x)))
        ∙∙ X ∙∙
       abs-Comm x y)
   λ x y x≤y →
     sym (0≤→abs≡id _ (ℚ.-≤ (ℚ.min x y) (ℚ.max x y)
        (ℚ.isTrans≤ _ _ _ (ℚ.min≤ x y) (ℚ.≤max x y)))) ∙ cong abs
       (cong₂ ℚ._-_
         (ℚ.≤→max _ _ x≤y) (ℚ.≤→min _ _ x≤y))
      ∙ abs-Comm y x


 distBroaden : ∀ x y a b
   → b ℚ.≤ x → b ℚ.≤ y → x ℚ.≤ a → y ℚ.≤ a
   → abs (x ℚ.- y) ℚ.≤ abs (a ℚ.- b)
 distBroaden x y a b b≤x b≤y x≤a y≤a =
  subst2 ℚ._≤_
       (abs≡⊔-⊓ x y)
       (sym (0≤→abs≡id (a ℚ.- b) (ℚ.-≤ b a (ℚ.isTrans≤ _ _ _ b≤y y≤a))))
         (+Mono≤ (ℚ.max x y) a (ℚ.- (ℚ.min x y)) (ℚ.- b)
          (subst (_ ℚ.≤_) (ℚ.maxIdem a) (ℚ.≤MonotoneMax x a y a x≤a y≤a))
           (ℚ.minus-≤ b (ℚ.min x y)
            ((subst (ℚ._≤ _) (ℚ.minIdem b) (ℚ.≤MonotoneMin b x b y b≤x b≤y)))))

 altΣboundedByOdd : ∀ k → ℚ.seqΣ s (k ℕ.∸ (k ∣2)) ℚ.≤ ℚ.seqΣ s k
 altΣboundedByOdd  zero = ℚ.isRefl≤ _
 altΣboundedByOdd  (suc k) = ⊎.rec
      (λ { (p , _ , zero , v) → ⊥.rec (znots v) ;
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
       (λ { (p , _ , zero , v) → ⊥.rec (znots v) ;
        (p , q , suc k' , v) →
           let v' = cong ℕ.predℕ v
           in cong abs ((λ i → ℚ.seqΣ s (v (~ i) ∸ (p i)) ℚ.-
                        ℚ.seqΣ s (v (~ i) ∸ (q i)))
                     ∙∙ ℚ!!
                     ∙∙ cong (s ∘ predℕ) v)})
      (λ (p , q , k' , v) →
        let v' = cong ℕ.predℕ v
        in (λ i → abs (ℚ.seqΣ s (v (~ i) ∸ p i) ℚ.-
                ℚ.seqΣ s (v (~ i) ∸ q i)))
              ∙∙ cong {x = (ℚ.seqΣ s (v (~ i1) ∸ p i1) ℚ.-
                ℚ.seqΣ s (v (~ i1) ∸ q i1))}
                   {y = ℚ.- s (k' ℕ.· 2)} abs ℚ!!
              ∙∙ λ i → abs- (s (v' i)) i)
       (∣2-cases (suc N))

 cauchyByAlt' :
                   ∀ N → 0 ℕ.< N → ∀ n m →
                      abs (ℚ.seqΣ s (n ℕ.+ N) ℚ.- ℚ.seqΣ s (m ℕ.+ N)) ℚ.≤
                         abs (s (predℕ N))
 cauchyByAlt'  N 0<N n m =
   ℚ.isTrans≤ _ _ _
     (distBroaden _ _ _ _
       (ℚ.isTrans≤ _ _ _
         (oddΣIncr  N n)
         (altΣboundedByOdd (n ℕ.+ N)))
       (ℚ.isTrans≤ _ _ _
         (oddΣIncr  N m)
         (altΣboundedByOdd (m ℕ.+ N)))
      (ℚ.isTrans≤ _ _ _ (altΣboundedByEven  (n ℕ.+ N))
         (evenΣDecr N n 0<N))
      (ℚ.isTrans≤ _ _ _ (altΣboundedByEven (m ℕ.+ N))
         (evenΣDecr N m 0<N)))
     (ℚ.≡Weaken≤ _ _ (abs-Comm (ℚ.seqΣ s (N ∸ (suc N ∣2))) (ℚ.seqΣ s (N ∸ (N ∣2))) ∙ (even-odd-Σ-dist N 0<N)))

 cauchyByAlt : ∀ N n m → N ℕ.< m → N ℕ.< n →
                      abs (ℚ.seqΣ s n ℚ.- ℚ.seqΣ s m) ℚ.≤
                         abs (s N)

 cauchyByAlt N zero _ N<m N<n = ⊥.rec (ℕ.¬-<-zero N<n)
 cauchyByAlt N _ zero N<m N<n = ⊥.rec (ℕ.¬-<-zero N<m)
 cauchyByAlt N (suc n) (suc m) (m' , p) (n' , q) =
   subst (ℚ._≤ _) (λ i → abs (ℚ.seqΣ s (q i) ℚ.- ℚ.seqΣ s (p i)))
    (cauchyByAlt' (suc N) ℕ.zero-<-suc n' m')

module AlternatingFromMagnitudes (s : ℕ → ℚ₊)
      (decreases : ∀ k → fst (s (suc k)) ℚ.< fst (s k))
      where

  terms : ℕ → ℚ
  terms k = ℚ.-1ⁿ· k (fst (s k))

  alternates : AlternatesPositiveFirst terms
  alternates k =
    subst (0 ℚ.<_) (sym (ℚ.-1ⁿ·-·2 k (fst (s _)))) (snd (s _))
    , subst (ℚ._< 0)
        (cong ℚ.-_
          (sym (ℚ.-1ⁿ·-·2 k (fst (s (suc (k ℕ.· 2))))))
          ∙ sym (ℚ.-1ⁿ·-suc (k ℕ.· 2) _))
        (ℚ.minus-< _ _ (snd (s _)))

  strictlyDecreasing : StrictlyDecreasingAlternating terms
  strictlyDecreasing k =
    subst2 ℚ._<_ (sym negOdd≡oddMagnitude) (sym evenTerm≡evenMagnitude)
      (decreases (k ℕ.· 2))
    , subst2 ℚ._<_ (sym nextEvenTerm≡nextEvenMagnitude)
        (sym negOdd≡oddMagnitude)
        (decreases (suc (k ℕ.· 2)))
    where
    negOdd≡oddMagnitude :
      ℚ.- terms (suc (k ℕ.· 2)) ≡ fst (s (suc (k ℕ.· 2)))
    negOdd≡oddMagnitude =
      cong ℚ.-_
        (ℚ.-1ⁿ·-suc (k ℕ.· 2) (fst (s (suc (k ℕ.· 2)))))
      ∙ ℚ.-Invol (ℚ.-1ⁿ· (k ℕ.· 2) (fst (s (suc (k ℕ.· 2)))))
      ∙ ℚ.-1ⁿ·-·2 k (fst (s (suc (k ℕ.· 2))))

    evenTerm≡evenMagnitude :
      terms (k ℕ.· 2) ≡ fst (s (k ℕ.· 2))
    evenTerm≡evenMagnitude =
      ℚ.-1ⁿ·-·2 k (fst (s (k ℕ.· 2)))

    nextEvenTerm≡nextEvenMagnitude :
      terms (suc (suc (k ℕ.· 2))) ≡ fst (s (suc (suc (k ℕ.· 2))))
    nextEvenTerm≡nextEvenMagnitude =
      ℚ.-1ⁿ·-·2 (suc k) (fst (s (suc (suc (k ℕ.· 2)))))

  terms→0 :
    ((ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n → fst (s n) ℚ.< fst ε))
    → (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n → abs (terms n) ℚ.< fst ε)
  terms→0 s→0 ε =
    map-snd
      (λ converges n N<n →
        subst (ℚ._< fst ε)
          (sym (0<→abs≡id _ (snd (s n)))
            ∙ sym (ℚ.absᵣ∘-1ⁿ· n (fst (s n))))
          (converges n N<n))
      (s→0 ε)

  module Series = AlternatingSeries terms alternates strictlyDecreasing
