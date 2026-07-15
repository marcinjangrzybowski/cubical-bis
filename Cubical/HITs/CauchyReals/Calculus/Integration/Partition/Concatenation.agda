module Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Concatenation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order.Inductive as ℕᵗ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Summation
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base

pred<ᵗ-from-suc<ᵗ : ∀ {j m} → suc j ℕᵗ.<ᵗ m → j ℕᵗ.<ᵗ predℕ m
pred<ᵗ-from-suc<ᵗ {m = zero} ()
pred<ᵗ-from-suc<ᵗ {m = suc m} p = p

concatPartitionLen : ∀ {a b c} →
  Partition[ a , b ] → Partition[ b , c ] → ℕ
concatPartitionLen p-ab p-bc = p-ab .len ℕ.+ suc (p-bc .len)

concatPartitionPtsΣ-left : ∀ a b c → b ≤ᵣ c →
  (p-ab : Partition[ a , b ]) →
  Fin (p-ab .len) → Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ c)
concatPartitionPtsΣ-left a b c b≤c p-ab i =
  p-ab .pts i ,
  p-ab .a≤pts i ,
  isTrans≤ᵣ _ _ _ (p-ab .pts≤b i) b≤c

concatPartitionPtsΣ-right : ∀ a b c → a ≤ᵣ b → b ≤ᵣ c →
  (p-bc : Partition[ b , c ]) →
  Fin (suc (p-bc .len)) → Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ c)
concatPartitionPtsΣ-right a b c a≤b b≤c p-bc (zero , _) =
  b , a≤b , b≤c
concatPartitionPtsΣ-right a b c a≤b b≤c p-bc (suc j , j<m) =
  p-bc .pts (j , j<m) ,
  isTrans≤ᵣ _ _ _ a≤b (p-bc .a≤pts (j , j<m)) ,
  p-bc .pts≤b (j , j<m)

concatPartitionPtsΣ : ∀ a b c → a ≤ᵣ b → b ≤ᵣ c →
  (p-ab : Partition[ a , b ]) →
  (p-bc : Partition[ b , c ]) →
  Fin (concatPartitionLen p-ab p-bc) →
  Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ c)
concatPartitionPtsΣ a b c a≤b b≤c p-ab p-bc =
  ⊎.rec (concatPartitionPtsΣ-left a b c b≤c p-ab)
        (concatPartitionPtsΣ-right a b c a≤b b≤c p-bc)
  ∘ Fin+→⊎ (p-ab .len) (suc (p-bc .len))

concatPartitionPts : ∀ a b c → a ≤ᵣ b → b ≤ᵣ c →
  (p-ab : Partition[ a , b ]) →
  (p-bc : Partition[ b , c ]) →
  Fin (concatPartitionLen p-ab p-bc) → ℝ
concatPartitionPts a b c a≤b b≤c p-ab p-bc =
  fst ∘ concatPartitionPtsΣ a b c a≤b b≤c p-ab p-bc

concatPartitionPts-inl : ∀ a b c (a≤b : a ≤ᵣ b) (b≤c : b ≤ᵣ c)
  (p-ab : Partition[ a , b ]) (p-bc : Partition[ b , c ]) →
  ∀ i →
  concatPartitionPts a b c a≤b b≤c p-ab p-bc
    (injectFin+' {m = suc (p-bc .len)} {n = p-ab .len} i)
  ≡ p-ab .pts i
concatPartitionPts-inl a b c a≤b b≤c p-ab p-bc i =
  cong (fst ∘ ⊎.rec
          (concatPartitionPtsΣ-left a b c b≤c p-ab)
          (concatPartitionPtsΣ-right a b c a≤b b≤c p-bc))
    (sym (Fin+→⊎∘injectFin+' (p-ab .len) (suc (p-bc .len)) i))

concatPartitionPts-inr-fzero : ∀ a b c (a≤b : a ≤ᵣ b) (b≤c : b ≤ᵣ c)
  (p-ab : Partition[ a , b ]) (p-bc : Partition[ b , c ]) →
  concatPartitionPts a b c a≤b b≤c p-ab p-bc
    (injectFin+ {m = suc (p-bc .len)} {n = p-ab .len} fzero)
  ≡ b
concatPartitionPts-inr-fzero a b c a≤b b≤c p-ab p-bc =
  cong (fst ∘ ⊎.rec
          (concatPartitionPtsΣ-left a b c b≤c p-ab)
          (concatPartitionPtsΣ-right a b c a≤b b≤c p-bc))
    (sym (Fin+→⊎∘injectFin+ (p-ab .len) (suc (p-bc .len)) fzero))

concatPartitionPts-inr-fsuc : ∀ a b c (a≤b : a ≤ᵣ b) (b≤c : b ≤ᵣ c)
  (p-ab : Partition[ a , b ]) (p-bc : Partition[ b , c ]) →
  ∀ i →
  concatPartitionPts a b c a≤b b≤c p-ab p-bc
    (injectFin+ {m = suc (p-bc .len)} {n = p-ab .len} (fsuc i))
  ≡ p-bc .pts i
concatPartitionPts-inr-fsuc a b c a≤b b≤c p-ab p-bc i =
  cong (fst ∘ ⊎.rec
          (concatPartitionPtsΣ-left a b c b≤c p-ab)
          (concatPartitionPtsΣ-right a b c a≤b b≤c p-bc))
    (sym (Fin+→⊎∘injectFin+ (p-ab .len) (suc (p-bc .len)) (fsuc i)))

concatPartitionPts≤pts : ∀ a b c → (a≤b : a ≤ᵣ b) → (b≤c : b ≤ᵣ c) →
  (p-ab : Partition[ a , b ]) →
  (p-bc : Partition[ b , c ]) →
  (k : Fin (predℕ (concatPartitionLen p-ab p-bc))) →
  concatPartitionPts a b c a≤b b≤c p-ab p-bc
    (finj-pred {n = concatPartitionLen p-ab p-bc} k)
  ≤ᵣ
  concatPartitionPts a b c a≤b b≤c p-ab p-bc
    (fsuc-pred {n = concatPartitionLen p-ab p-bc} k)
concatPartitionPts≤pts a b c a≤b b≤c
  p-ab@record { len = zero }
  p-bc@record { len = zero } ()
concatPartitionPts≤pts a b c a≤b b≤c
  p-ab@record { len = zero }
  p-bc@record { len = suc m } (zero , _) =
  p-bc .a≤pts fzero
concatPartitionPts≤pts a b c a≤b b≤c
  p-ab@record { len = zero }
  p-bc@record { len = suc m } (suc j , j<m) =
  p-bc .pts≤pts (j , j<m)
concatPartitionPts≤pts a b c a≤b b≤c
  p-ab@record { len = suc n }
  p-bc@record { len = m } k
  with Fin+→⊎ n (suc m) k UsingEq
... | inl i , splitEq =
  subst2 _≤ᵣ_ (sym lowerEq) (sym upperEq) (p-ab .pts≤pts i)
  where
  kEq : injectFin+' {m = suc m} {n = n} i ≡ k
  kEq =
    sym (cong (⊎.rec (injectFin+' {m = suc m} {n = n})
                      (injectFin+ {m = suc m} {n = n}))
              splitEq)
    ∙ Iso-Fin+⊎-leftInv n (suc m) k

  lowerIdxEq :
    finj-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+' {m = suc m} {n = suc n} (finj i)
  lowerIdxEq =
    sym (cong finj kEq)
    ∙ finj∘inj' {n = n} {m = suc m} i

  upperIdxEq :
    fsuc-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+' {m = suc m} {n = suc n} (fsuc i)
  upperIdxEq =
    sym (cong fsuc kEq)
    ∙ fsuc∘inj' {n = n} {m = m} i

  lowerEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (finj-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ p-ab .pts (finj-pred {n = p-ab .len} i)
  lowerEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) lowerIdxEq
    ∙ concatPartitionPts-inl a b c a≤b b≤c p-ab p-bc (finj i)

  upperEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (fsuc-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ p-ab .pts (fsuc-pred {n = p-ab .len} i)
  upperEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) upperIdxEq
    ∙ concatPartitionPts-inl a b c a≤b b≤c p-ab p-bc (fsuc i)
... | inr (zero , r<) , splitEq =
  subst2 _≤ᵣ_ (sym lowerEq) (sym upperEq) (p-ab .pts≤b flast)
  where
  r : Fin (suc m)
  r = zero , r<

  kEq : injectFin+ {m = suc m} {n = n} r ≡ k
  kEq =
    sym (cong (⊎.rec (injectFin+' {m = suc m} {n = n})
                      (injectFin+ {m = suc m} {n = n}))
              splitEq)
    ∙ Iso-Fin+⊎-leftInv n (suc m) k

  lowerIdxEq :
    finj-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+' {m = suc m} {n = suc n} flast
  lowerIdxEq =
    toℕ-injective {k = suc n ℕ.+ suc m}
      {fj = finj-pred {n = concatPartitionLen p-ab p-bc} k}
      {fk = injectFin+' {m = suc m} {n = suc n} flast}
      (cong fst (sym kEq) ∙ +-zero n)

  upperIdxEq :
    fsuc-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+ {m = suc m} {n = suc n} fzero
  upperIdxEq =
    toℕ-injective {k = suc n ℕ.+ suc m}
      {fj = fsuc-pred {n = concatPartitionLen p-ab p-bc} k}
      {fk = injectFin+ {m = suc m} {n = suc n} fzero}
      (cong suc (cong fst (sym kEq) ∙ +-zero n)
       ∙ sym (+-zero (suc n)))

  lowerEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (finj-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ p-ab .pts flast
  lowerEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) lowerIdxEq
    ∙ concatPartitionPts-inl a b c a≤b b≤c p-ab p-bc flast

  upperEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (fsuc-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ b
  upperEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) upperIdxEq
    ∙ concatPartitionPts-inr-fzero a b c a≤b b≤c p-ab p-bc
... | inr (suc zero , 0<m) , splitEq =
  subst2 _≤ᵣ_ (sym lowerEq) (sym upperEq) (p-bc .a≤pts j)
  where
  r : Fin (suc m)
  r = suc zero , 0<m

  j : Fin m
  j = zero , 0<m

  kEq : injectFin+ {m = suc m} {n = n} r ≡ k
  kEq =
    sym (cong (⊎.rec (injectFin+' {m = suc m} {n = n})
                      (injectFin+ {m = suc m} {n = n}))
              splitEq)
    ∙ Iso-Fin+⊎-leftInv n (suc m) k

  n+1≡sn : n ℕ.+ suc zero ≡ suc n
  n+1≡sn = +-suc n zero ∙ cong suc (+-zero n)

  sn+1≡ssn : suc n ℕ.+ suc zero ≡ suc (suc n)
  sn+1≡ssn = +-suc (suc n) zero ∙ cong suc (+-zero (suc n))

  lowerIdxEq :
    finj-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+ {m = suc m} {n = suc n} fzero
  lowerIdxEq =
    toℕ-injective {k = suc n ℕ.+ suc m}
      {fj = finj-pred {n = concatPartitionLen p-ab p-bc} k}
      {fk = injectFin+ {m = suc m} {n = suc n} fzero}
      (cong fst (sym kEq)
       ∙ n+1≡sn
       ∙ sym (+-zero (suc n)))

  upperIdxEq :
    fsuc-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+ {m = suc m} {n = suc n} (fsuc j)
  upperIdxEq =
    toℕ-injective {k = suc n ℕ.+ suc m}
      {fj = fsuc-pred {n = concatPartitionLen p-ab p-bc} k}
      {fk = injectFin+ {m = suc m} {n = suc n} (fsuc j)}
      (cong suc (cong fst (sym kEq) ∙ n+1≡sn)
       ∙ sym sn+1≡ssn)

  lowerEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (finj-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ b
  lowerEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) lowerIdxEq
    ∙ concatPartitionPts-inr-fzero a b c a≤b b≤c p-ab p-bc

  upperEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (fsuc-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ p-bc .pts j
  upperEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) upperIdxEq
    ∙ concatPartitionPts-inr-fsuc a b c a≤b b≤c p-ab p-bc j
... | inr (suc (suc j) , sj<m) , splitEq =
  subst2 _≤ᵣ_ (sym lowerEq) (sym upperEq) (p-bc .pts≤pts jPred)
  where
  r : Fin (suc m)
  r = suc (suc j) , sj<m

  jPred : Fin (predℕ m)
  jPred = j , pred<ᵗ-from-suc<ᵗ {j = j} {m = m} sj<m

  kEq : injectFin+ {m = suc m} {n = n} r ≡ k
  kEq =
    sym (cong (⊎.rec (injectFin+' {m = suc m} {n = n})
                      (injectFin+ {m = suc m} {n = n}))
              splitEq)
    ∙ Iso-Fin+⊎-leftInv n (suc m) k

  lowerIdxEq :
    finj-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+ {m = suc m} {n = suc n} (fsuc (finj-pred {n = m} jPred))
  lowerIdxEq =
    toℕ-injective {k = suc n ℕ.+ suc m}
      {fj = finj-pred {n = concatPartitionLen p-ab p-bc} k}
      {fk = injectFin+ {m = suc m} {n = suc n} (fsuc (finj-pred {n = m} jPred))}
      (cong fst (sym kEq)
       ∙ +-suc n (suc j)
       ∙ cong (λ u → suc n ℕ.+ suc u)
           (sym (toℕ-finj-pred {n = m} jPred)))

  upperIdxEq :
    fsuc-pred {n = concatPartitionLen p-ab p-bc} k
    ≡ injectFin+ {m = suc m} {n = suc n} (fsuc (fsuc-pred {n = m} jPred))
  upperIdxEq =
    toℕ-injective {k = suc n ℕ.+ suc m}
      {fj = fsuc-pred {n = concatPartitionLen p-ab p-bc} k}
      {fk = injectFin+ {m = suc m} {n = suc n} (fsuc (fsuc-pred {n = m} jPred))}
      (cong suc (cong fst (sym kEq))
       ∙ cong (λ u → suc n ℕ.+ suc u)
           (sym (toℕ-fsuc-pred {n = m} jPred)))

  lowerEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (finj-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ p-bc .pts (finj-pred {n = m} jPred)
  lowerEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) lowerIdxEq
    ∙ concatPartitionPts-inr-fsuc a b c a≤b b≤c p-ab p-bc
        (finj-pred {n = m} jPred)

  upperEq :
    concatPartitionPts a b c a≤b b≤c p-ab p-bc
      (fsuc-pred {n = concatPartitionLen p-ab p-bc} k)
    ≡ p-bc .pts (fsuc-pred {n = m} jPred)
  upperEq =
    cong (concatPartitionPts a b c a≤b b≤c p-ab p-bc) upperIdxEq
    ∙ concatPartitionPts-inr-fsuc a b c a≤b b≤c p-ab p-bc
        (fsuc-pred {n = m} jPred)

concatTaggedPartition : ∀ a b c → a ≤ᵣ b → b ≤ᵣ c
                → (tp-ab : TaggedPartition[ a , b ])
                → (tp-bc : TaggedPartition[ b , c ])
                → Σ[ tp-ac ∈ TaggedPartition[ a , c ] ]
                  ((∀ f → riemannSum' (snd tp-ab) f +ᵣ riemannSum' (snd tp-bc) f ≡
                          riemannSum' (snd tp-ac) f)
                  × (∀ δ → mesh≤ᵣ (fst tp-ab) δ → mesh≤ᵣ (fst tp-bc) δ → mesh≤ᵣ (fst tp-ac) δ ))
concatTaggedPartition a b c a≤b b≤c
  (p-ab@record { len = n } , s-ab)
  (p-bc@record { len = m } , s-bc) =
  (pAC , sampleAC) , rsConcat , mesh-concat
 where

 lenAC : ℕ
 lenAC = concatPartitionLen p-ab p-bc

 ptsACΣ : Fin lenAC → Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ c)
 ptsACΣ = concatPartitionPtsΣ a b c a≤b b≤c p-ab p-bc

 ptsAC : Fin lenAC → ℝ
 ptsAC = concatPartitionPts a b c a≤b b≤c p-ab p-bc

 a≤ptsAC : ∀ k → a ≤ᵣ ptsAC k
 a≤ptsAC = fst ∘ snd ∘ ptsACΣ

 ptsAC≤c : ∀ k → ptsAC k ≤ᵣ c
 ptsAC≤c = snd ∘ snd ∘ ptsACΣ

 ptsAC≤ptsAC : (k : Fin (predℕ lenAC)) →
   ptsAC (finj-pred {n = lenAC} k) ≤ᵣ ptsAC (fsuc-pred {n = lenAC} k)
 ptsAC≤ptsAC =
   concatPartitionPts≤pts a b c a≤b b≤c p-ab p-bc

 pAC : Partition[ a , c ]
 pAC .len = lenAC
 pAC .pts = ptsAC
 pAC .endpoints≤ = isTrans≤ᵣ _ _ _ a≤b b≤c
 pAC .a≤pts = a≤ptsAC
 pAC .pts≤b = ptsAC≤c
 pAC .pts≤pts = ptsAC≤ptsAC

 ptsAC-inl : ∀ i → ptsAC (injectFin+' {m = suc m} {n = n} i) ≡ p-ab .pts i
 ptsAC-inl =
   concatPartitionPts-inl a b c a≤b b≤c p-ab p-bc

 ptsAC-inr-fzero : ptsAC (injectFin+ {m = suc m} {n = n} fzero) ≡ b
 ptsAC-inr-fzero =
   concatPartitionPts-inr-fzero a b c a≤b b≤c p-ab p-bc

 ptsAC-inr-fsuc : ∀ i → ptsAC (injectFin+ {m = suc m} {n = n} (fsuc i)) ≡ p-bc .pts i
 ptsAC-inr-fsuc =
   concatPartitionPts-inr-fsuc a b c a≤b b≤c p-ab p-bc

 pts'-inl : ∀ x → pts' p-ab x ≡ pts' pAC (injectFin+' {m = suc m} {n = 2 ℕ.+ n} x)
 pts'-inl (zero , _) = refl
 pts'-inl x@(suc k , q) =
   ℕᵗ.split<ᵗ-suc-elim {k = k} {len = n}
     {C = pts' p-ab x
          ≡ pts' pAC (injectFin+' {m = suc m} {n = 2 ℕ.+ n} x)}
     q
     (λ k<n →
           let j : Fin n
               j = k , k<n
               x≡mid : x ≡ fsuc (finj j)
               x≡mid =
                 toℕ-injective {k = 2 ℕ.+ n}
                   {fj = x}
                   {fk = fsuc (finj j)}
                   refl
               target≡mid :
                 injectFin+' {m = suc m} {n = 2 ℕ.+ n} x
                 ≡ fsuc (finj (injectFin+' {m = suc m} {n = n} j))
               target≡mid =
                 toℕ-injective {k = 2 ℕ.+ lenAC}
                   {fj = injectFin+' {m = suc m} {n = 2 ℕ.+ n} x}
                   {fk = fsuc (finj (injectFin+' {m = suc m} {n = n} j))}
                   refl
               lhsMid : pts' p-ab x ≡ p-ab .pts j
               lhsMid = cong (pts' p-ab) x≡mid ∙ pts'-mid p-ab j
               rhsMid :
                 pts' pAC (injectFin+' {m = suc m} {n = 2 ℕ.+ n} x)
                 ≡ p-ab .pts j
               rhsMid =
                 cong (pts' pAC) target≡mid
                 ∙ pts'-mid pAC (injectFin+' {m = suc m} {n = n} j)
                 ∙ ptsAC-inl j
       in lhsMid ∙ sym rhsMid)
     (λ k≡n →
           let idxB : Fin lenAC
               idxB = injectFin+ {m = suc m} {n = n} fzero
               x≡last : x ≡ flast {k = 1 ℕ.+ n}
               x≡last =
                 toℕ-injective {k = 2 ℕ.+ n}
                   {fj = x}
                   {fk = flast {k = 1 ℕ.+ n}}
                   (cong suc k≡n)
               target≡mid :
                 injectFin+' {m = suc m} {n = 2 ℕ.+ n} x
                 ≡ fsuc (finj idxB)
               target≡mid =
                 toℕ-injective {k = 2 ℕ.+ lenAC}
                   {fj = injectFin+' {m = suc m} {n = 2 ℕ.+ n} x}
                   {fk = fsuc (finj idxB)}
                   (cong suc (k≡n ∙ sym (+-zero n)))
               lhsLast : pts' p-ab x ≡ b
               lhsLast = cong (pts' p-ab) x≡last ∙ pts'-last p-ab
               rhsMid :
                 pts' pAC (injectFin+' {m = suc m} {n = 2 ℕ.+ n} x)
                 ≡ b
               rhsMid =
                 cong (pts' pAC) target≡mid
                 ∙ pts'-mid pAC idxB
                 ∙ ptsAC-inr-fzero
       in lhsLast ∙ sym rhsMid)

 pts'-inr-fsuc : ∀ x → pts' p-bc (fsuc x) ≡ pts' pAC (injectFin+ {m = suc m} {n = 2 ℕ.+ n} x)
 pts'-inr-fsuc x@(k , q) =
   ℕᵗ.split<ᵗ-suc-elim {k = k} {len = m}
     {C = pts' p-bc (fsuc x)
          ≡ pts' pAC (injectFin+ {m = suc m} {n = 2 ℕ.+ n} x)}
     q
     (λ k<m →
           let j : Fin m
               j = k , k<m
               x≡mid : fsuc x ≡ fsuc (finj j)
               x≡mid =
                 toℕ-injective {k = 2 ℕ.+ m}
                   {fj = fsuc x}
                   {fk = fsuc (finj j)}
                   refl
               idx : Fin lenAC
               idx = injectFin+ {m = suc m} {n = n} (fsuc j)
               target≡mid :
                 injectFin+ {m = suc m} {n = 2 ℕ.+ n} x
                 ≡ fsuc (finj idx)
               target≡mid =
                 toℕ-injective {k = 2 ℕ.+ lenAC}
                   {fj = injectFin+ {m = suc m} {n = 2 ℕ.+ n} x}
                   {fk = fsuc (finj idx)}
                   (cong suc (sym (+-suc n k)))
               lhsMid : pts' p-bc (fsuc x) ≡ p-bc .pts j
               lhsMid = cong (pts' p-bc) x≡mid ∙ pts'-mid p-bc j
               rhsMid :
                 pts' pAC (injectFin+ {m = suc m} {n = 2 ℕ.+ n} x)
                 ≡ p-bc .pts j
               rhsMid =
                 cong (pts' pAC) target≡mid
                 ∙ pts'-mid pAC idx
                 ∙ ptsAC-inr-fsuc j
       in lhsMid ∙ sym rhsMid)
     (λ k≡m →
           let x≡last : fsuc x ≡ flast {k = 1 ℕ.+ m}
               x≡last =
                 toℕ-injective {k = 2 ℕ.+ m}
                   {fj = fsuc x}
                   {fk = flast {k = 1 ℕ.+ m}}
                   (cong suc k≡m)
               target≡last :
                 injectFin+ {m = suc m} {n = 2 ℕ.+ n} x
                 ≡ flast {k = 1 ℕ.+ lenAC}
               target≡last =
                 toℕ-injective {k = 2 ℕ.+ lenAC}
                   {fj = injectFin+ {m = suc m} {n = 2 ℕ.+ n} x}
                   {fk = flast {k = 1 ℕ.+ lenAC}}
                   (cong (λ t → (2 ℕ.+ n) ℕ.+ t) k≡m
                    ∙ cong suc (sym (+-suc n m)))
               lhsLast : pts' p-bc (fsuc x) ≡ c
               lhsLast = cong (pts' p-bc) x≡last ∙ pts'-last p-bc
               rhsLast :
                 pts' pAC (injectFin+ {m = suc m} {n = 2 ℕ.+ n} x)
                 ≡ c
               rhsLast = cong (pts' pAC) target≡last ∙ pts'-last pAC
       in lhsLast ∙ sym rhsLast)

 left-lower : ∀ i →
   pts' p-ab (finj i)
   ≡ pts' pAC (finj (injectFin+' {m = suc m} {n = suc n} i))
 left-lower i =
   pts'-inl (finj i)
   ∙ cong (pts' pAC)
     (sym (toℕ-injective {k = 2 ℕ.+ lenAC}
                           {fj = finj (injectFin+' {m = suc m} {n = suc n} i)}
                           {fk = injectFin+' {m = suc m} {n = 2 ℕ.+ n} (finj i)}
                           refl))

 left-upper : ∀ i →
   pts' p-ab (fsuc i)
   ≡ pts' pAC (fsuc (injectFin+' {m = suc m} {n = suc n} i))
 left-upper i =
   pts'-inl (fsuc i)
   ∙ cong (pts' pAC)
     (sym (toℕ-injective {k = 2 ℕ.+ lenAC}
                           {fj = fsuc (injectFin+' {m = suc m} {n = suc n} i)}
                           {fk = injectFin+' {m = suc m} {n = 2 ℕ.+ n} (fsuc i)}
                           refl))

 right-lower : ∀ j →
   pts' p-bc (finj j)
   ≡ pts' pAC (finj (injectFin+ {m = suc m} {n = suc n} j))
 right-lower (zero , _) =
   sym (pts'-last p-ab)
   ∙ pts'-inl flast
   ∙ cong (pts' pAC)
     (toℕ-injective {k = 2 ℕ.+ lenAC}
       {fj = injectFin+' {m = suc m} {n = 2 ℕ.+ n} flast}
       {fk = finj (injectFin+ {m = suc m} {n = suc n} fzero)}
       (sym (+-zero (suc n))))
 right-lower (suc r , r<m) =
   pts'-inr-fsuc (finj rFin)
   ∙ cong (pts' pAC)
     (toℕ-injective {k = 2 ℕ.+ lenAC}
       {fj = injectFin+ {m = suc m} {n = 2 ℕ.+ n} (finj rFin)}
       {fk = finj (injectFin+ {m = suc m} {n = suc n} (fsuc rFin))}
       (cong suc (sym (+-suc n r))))
  where
  rFin : Fin m
  rFin = r , r<m

 right-upper : ∀ j →
   pts' p-bc (fsuc j)
   ≡ pts' pAC (fsuc (injectFin+ {m = suc m} {n = suc n} j))
 right-upper j =
   pts'-inr-fsuc j
   ∙ cong (pts' pAC)
     (sym (toℕ-injective {k = 2 ℕ.+ lenAC}
                           {fj = fsuc (injectFin+ {m = suc m} {n = suc n} j)}
                           {fk = injectFin+ {m = suc m} {n = 2 ℕ.+ n} j}
                           refl))

 split-left-eq : ∀ {k} i →
   Fin+→⊎ (suc n) (suc m) k ≡ inl i →
   injectFin+' {m = suc m} {n = suc n} i ≡ k
 split-left-eq {k} i splitEq =
   sym (cong (⊎.rec (injectFin+' {m = suc m} {n = suc n})
                     (injectFin+ {m = suc m} {n = suc n}))
             splitEq)
   ∙ Iso-Fin+⊎-leftInv (suc n) (suc m) k

 split-right-eq : ∀ {k} j →
   Fin+→⊎ (suc n) (suc m) k ≡ inr j →
   injectFin+ {m = suc m} {n = suc n} j ≡ k
 split-right-eq {k} j splitEq =
   sym (cong (⊎.rec (injectFin+' {m = suc m} {n = suc n})
                     (injectFin+ {m = suc m} {n = suc n}))
             splitEq)
   ∙ Iso-Fin+⊎-leftInv (suc n) (suc m) k

 sampleAC : Sample pAC
 sampleAC .samples =
   ⊎.rec (samples s-ab) (samples s-bc)
     ∘ Fin+→⊎ (suc n) (suc m)
 sampleAC .pts'≤samples k with Fin+→⊎ (suc n) (suc m) k UsingEq
 ... | inl i , splitEq =
   isTrans≡≤ᵣ _ _ _
     (cong (pts' pAC)
      (cong finj (sym kEq))
      ∙ sym (left-lower i))
     (isTrans≤≡ᵣ _ _ _
       (s-ab .pts'≤samples i)
       sampleEq)
  where
  kEq : injectFin+' {m = suc m} {n = suc n} i ≡ k
  kEq = split-left-eq i splitEq

  sampleEq : samples s-ab i ≡ sampleAC .samples k
  sampleEq = sym (cong (⊎.rec (samples s-ab) (samples s-bc)) splitEq)
 sampleAC .pts'≤samples k | inr j , splitEq =
   isTrans≡≤ᵣ _ _ _
     (cong (pts' pAC)
      (cong finj (sym kEq))
      ∙ sym (right-lower j))
     (isTrans≤≡ᵣ _ _ _
       (s-bc .pts'≤samples j)
       sampleEq)
  where
  kEq : injectFin+ {m = suc m} {n = suc n} j ≡ k
  kEq = split-right-eq j splitEq

  sampleEq : samples s-bc j ≡ sampleAC .samples k
  sampleEq = sym (cong (⊎.rec (samples s-ab) (samples s-bc)) splitEq)
 sampleAC .samples≤pts' k with Fin+→⊎ (suc n) (suc m) k UsingEq
 ... | inl i , splitEq =
   isTrans≡≤ᵣ _ _ _
     sampleEq
     (isTrans≤≡ᵣ _ _ _
       (s-ab .samples≤pts' i)
       (left-upper i
        ∙ cong (pts' pAC)
          (cong fsuc kEq)))
  where
  kEq : injectFin+' {m = suc m} {n = suc n} i ≡ k
  kEq = split-left-eq i splitEq

  sampleEq : sampleAC .samples k ≡ samples s-ab i
  sampleEq = cong (⊎.rec (samples s-ab) (samples s-bc)) splitEq
 sampleAC .samples≤pts' k | inr j , splitEq =
   isTrans≡≤ᵣ _ _ _
     sampleEq
     (isTrans≤≡ᵣ _ _ _
       (s-bc .samples≤pts' j)
       (right-upper j
        ∙ cong (pts' pAC)
          (cong fsuc kEq)))
  where
  kEq : injectFin+ {m = suc m} {n = suc n} j ≡ k
  kEq = split-right-eq j splitEq

  sampleEq : sampleAC .samples k ≡ samples s-bc j
  sampleEq = cong (⊎.rec (samples s-ab) (samples s-bc)) splitEq

 riemann-split : ∀ f →
   riemannSum' sampleAC f
   ≡
   foldlFin {n = suc n ℕ.+ suc m}
     (λ S k → S +ᵣ
       ((pts' pAC (fsuc k) -ᵣ pts' pAC (finj k))
        ·ᵣ f (sampleAC .samples k)))
     0 (idfun _)
 riemann-split f = riemannSum'-alt-lem sampleAC f

 rsConcat : (f : ℝ → ℝ) →
      riemannSum' s-ab f +ᵣ riemannSum' s-bc f ≡ riemannSum' sampleAC f
 rsConcat f =
   cong₂ _+ᵣ_
     (riemannSum'-alt-lem s-ab f
      ∙ congS {A = Fin (suc n) → ℝ}
        (λ g → foldlFin {n = suc n} (λ S k → S +ᵣ g k) 0 (idfun _))
        (funExt λ i →
          cong₂ _·ᵣ_
            (cong₂ _-ᵣ_
              (left-upper i)
              (left-lower i))
            (cong f (sym (rec⊎-injectFin+' {m = suc m} {n = suc n}
                            (samples s-ab) (samples s-bc) i)))))
     (riemannSum'-alt-lem s-bc f
      ∙ congS {A = Fin (suc m) → ℝ}
        (λ g → foldlFin {n = suc m} (λ S k → S +ᵣ g k) 0 (idfun _))
        (funExt λ j →
          cong₂ _·ᵣ_
            (cong₂ _-ᵣ_
              (right-upper j)
              (right-lower j))
            (cong f (sym (rec⊎-injectFin+ {m = suc m} {n = suc n}
                            (samples s-ab) (samples s-bc) j)))))
   ∙ sym (foldFin-sum-concat (suc n) (suc m) _)
   ∙ sym (riemannSum'-alt-lem sampleAC f)

 mesh-concat : (δ : ℝ) → mesh≤ᵣ p-ab δ → mesh≤ᵣ p-bc δ →
     mesh≤ᵣ pAC δ
 mesh-concat δ mesh-ab mesh-bc k with Fin+→⊎ (suc n) (suc m) k UsingEq
 ... | inl i , splitEq =
   isTrans≡≤ᵣ _ _ _
     (cong₂ _-ᵣ_
        (sym (left-upper i
         ∙ cong (pts' pAC)
           (cong fsuc kEq)))
        (sym (left-lower i
         ∙ cong (pts' pAC)
           (cong finj kEq))))
     (mesh-ab i)
  where
  kEq : injectFin+' {m = suc m} {n = suc n} i ≡ k
  kEq = split-left-eq i splitEq
 mesh-concat δ mesh-ab mesh-bc k | inr j , splitEq =
   isTrans≡≤ᵣ _ _ _
     (cong₂ _-ᵣ_
        (sym (right-upper j
         ∙ cong (pts' pAC)
           (cong fsuc kEq)))
        (sym (right-lower j
         ∙ cong (pts' pAC)
           (cong finj kEq))))
     (mesh-bc j)
  where
  kEq : injectFin+ {m = suc m} {n = suc n} j ≡ k
  kEq = split-right-eq j splitEq
