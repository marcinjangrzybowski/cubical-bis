module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary where

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
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (seqΣ ; seqΣ' ; _^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using
  ( invℚ
  ; _⁻¹₊
  ; x/y<z→x<y·z
  )

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Convexity

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.CommRing.Properties as CR

module 𝐙' = RingTheory (CR.CommRing→Ring ℤCRing.ℤCommRing )

ℚ≤→<+₊ : ∀ x y (ε : ℚ₊) → x ℚ.≤ y → x ℚ.< y ℚ.+ fst ε
ℚ≤→<+₊ x y ε x≤y =
  subst (λ z → z ℚ.< y ℚ.+ fst ε) (ℚ.+IdR x)
    (ℚ.≤<Monotone+ x y 0 (fst ε) x≤y (snd ε))

private
  2ℝ₊ : ℝ₊
  2ℝ₊ = fromNat 2

  2₊ : ℚ₊
  2₊ = fromNat 2

open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Bernoulli
  using (bernoulli's-ineq-^ℚⁿ)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Inequalities

invℚ-unitFrac : ∀ d p → ℚ.invℚ [ pos 1 / d ] p ≡ [ ℤ.ℕ₊₁→ℤ d / 1 ]
invℚ-unitFrac d p = ℚ.eq/ _ _ ℤ!

fromNatInvℚ₊≡step : ∀ n → fst ((fromNat (suc (suc n))) ⁻¹₊) ≡ [ 1 / 2+ n ]
fromNatInvℚ₊≡step n =
  sym (ℚ.invℚ₊≡invℚ (fromNat (suc (suc n))) (inl (ℚ.0<pos (suc n) 1)))
  ∙ ℚ.fromNat-invℚ (suc n) (inl (ℚ.0<pos (suc n) 1))

stepℚ₊ : ℕ → ℚ₊
stepℚ₊ n = [ 1 / 2+ n ] , ℚ.0<pos 0 (2+ n)

fromSucℚ₊ : ℕ → ℚ₊
fromSucℚ₊ n = [ pos (suc n) / 1 ] , ℚ.0<pos n 1

posStepWidth : ℕ → ℚ₊
posStepWidth n = ℚ.<→ℚ₊ 0 [ 1 / 2+ n ] (ℚ.0<pos 0 (2+ n))

negStepWidth : ℕ → ℚ₊
negStepWidth n =
  ℚ.<→ℚ₊ (ℚ.- [ 1 / 2+ n ]) 0
    (ℚ.minus-< 0 [ 1 / 2+ n ] (ℚ.0<pos 0 (2+ n)))

posStepWidth≡fromNatInv : ∀ n → posStepWidth n ≡ (fromNat (suc (suc n))) ⁻¹₊
posStepWidth≡fromNatInv n =
  ℚ₊≡ (ℚ.+IdR [ 1 / 2+ n ] ∙ sym (fromNatInvℚ₊≡step n))

negStepWidth≡fromNatInv : ∀ n → negStepWidth n ≡ (fromNat (suc (suc n))) ⁻¹₊
negStepWidth≡fromNatInv n =
  ℚ₊≡ (ℚ.+IdL (ℚ.- (ℚ.- [ 1 / 2+ n ])) ∙
    ℚ.-Invol [ 1 / 2+ n ] ∙ sym (fromNatInvℚ₊≡step n))

lnSeq : ℝ₊ → ℕ → ℝ
lnSeq z n =  (fst (z ^ℚ [ 1 / 2+ n ]) -ᵣ 1)  ·ᵣ fromNat (suc (suc n))

opaque
 lnSeq-one : ∀ n → lnSeq 1 n ≡ 0
 lnSeq-one n =
   Rℝ.0LeftAnnihilates'
     (fst (1 ^ℚ fst (stepℚ₊ n)) -ᵣ 1)
     (fromNat (suc (suc n)))
     (Rℝ.+InvR'
       (fst (1 ^ℚ fst (stepℚ₊ n)))
       1
       (cong fst (1^ℚ≡1 (fst (stepℚ₊ n)))))


opaque
 unfolding -ᵣ_
 lnSeqMonStrictInZ : (z z' : ℝ₊)
                → fst z <ᵣ fst z'
                → ∀ n → lnSeq z n <ᵣ lnSeq z' n
 lnSeqMonStrictInZ z z' z<z' n =
   <ᵣ-·ᵣo (fst (z ^ℚ [ 1 / 2+ n ]) -ᵣ 1)
     (fst (z' ^ℚ [ 1 / 2+ n ]) -ᵣ 1) (fromNat (suc (suc n)))
    $ <ᵣ-+o (fst (z ^ℚ [ 1 / 2+ n ])) (fst (z' ^ℚ [ 1 / 2+ n ])) -1
      (^ℚ-StrictMonotone {z} {z'} (stepℚ₊ n) z<z')

 lnSeqMonInZ : (z z' : ℝ₊)
                → fst z ≤ᵣ fst z'
                → ∀ n → lnSeq z n ≤ᵣ lnSeq z' n
 lnSeqMonInZ z z' z≤z' n =
   ≤ᵣ-·ᵣo (fst (z ^ℚ [ 1 / 2+ n ]) -ᵣ 1)
     (fst (z' ^ℚ [ 1 / 2+ n ]) -ᵣ 1) (fromNat (suc (suc n)))
     (≤ℚ→≤ᵣ 0 [ pos (suc (suc n)) / 1 ] (ℚ.0≤pos (suc (suc n)) 1))
    $ ≤ᵣ-+o (fst (z ^ℚ [ 1 / 2+ n ])) (fst (z' ^ℚ [ 1 / 2+ n ])) -1
      (^ℚ-Monotone {z} {z'} (stepℚ₊ n) z≤z')

 lnSeq-nonnegative : ∀ z → 1 ≤ᵣ fst z → ∀ n → 0 ≤ᵣ lnSeq z n
 lnSeq-nonnegative z 1≤z n =
   isTrans≡≤ᵣ
     0
     (0 ·ᵣ 0)
     (root-difference ·ᵣ fromNat (suc (suc n)))
     (rat·ᵣrat 0 0)
     (≤ᵣ₊Monotone·ᵣ
       0 root-difference 0 (fromNat (suc (suc n)))
       root-difference-nonnegative
       (≤ᵣ-refl 0)
       root-difference-nonnegative
       (≤ℚ→≤ᵣ
         0 [ pos (suc (suc n)) / 1 ]
         (ℚ.0≤pos (suc (suc n)) 1)))
  where
  root-difference : ℝ
  root-difference = fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1

  root-difference-nonnegative : 0 ≤ᵣ root-difference
  root-difference-nonnegative =
    fst
      (x≤y≃0≤y-x 1 (fst (z ^ℚ fst (stepℚ₊ n))))
      (1≤^ℚ z (stepℚ₊ n) 1≤z)



 lnSeqCont : ∀ n → IsContinuousWithPred pred0<
              (λ z 0<z → lnSeq (z , 0<z) n)
 lnSeqCont n = IsContinuousWP∘' pred0<
      (λ x → (x -ᵣ 1) ·ᵣ fromNat (suc (suc n)))
      (λ z 0<z → fst ((z , 0<z) ^ℚ [ 1 / 2+ n ]))
      (IsContinuous∘
        (λ x → x ·ᵣ fromNat (suc (suc n)))
        (λ x → x -ᵣ 1)
        (IsContinuous·ᵣR (fromNat (suc (suc n))))
        (IsContinuous+ᵣR -1))
      (IsContinuous^ℚ [ 1 / 2+ n ])


lnSeq' : ℝ₊ → ℕ → ℝ
lnSeq' z n = (1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ])))  ·ᵣ fromNat (suc (suc n))


lnSeq'Cont : ∀ n → IsContinuousWithPred pred0<
             (λ z 0<z → lnSeq' (z , 0<z) n)
lnSeq'Cont n = IsContinuousWP∘' pred0<
     (λ x → (1 -ᵣ x) ·ᵣ fromNat (suc (suc n)))
     (λ z 0<z → fst ((z , 0<z) ^ℚ (ℚ.- [ 1 / 2+ n ])))
     (IsContinuous∘
       (λ x → x ·ᵣ fromNat (suc (suc n)))
       (λ x → 1 -ᵣ x)
       (IsContinuous·ᵣR (fromNat (suc (suc n))))
       (IsContinuous∘
         (λ x → 1 +ᵣ x)
         (λ x → -ᵣ x)
         (IsContinuous+ᵣL 1)
         IsContinuous-ᵣ))
     (IsContinuous^ℚ (ℚ.- [ 1 / 2+ n ]))

lnSeq'[z]≡lnSeq[1/x] : ∀ n z → -ᵣ lnSeq' z n ≡ lnSeq (invℝ₊ z) n
lnSeq'[z]≡lnSeq[1/x] n z =
  sym (-ᵣ· (1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ]))) (fromNat (suc (suc n))))
  ∙ cong (_·ᵣ fromNat (suc (suc n)))
    (-[x-y]≡y-x 1 (fst (z ^ℚ (ℚ.- [ 1 / 2+ n ]))) ∙
     cong (_-ᵣ 1)
      (cong fst (^ℚ-minus' z [ 1 / 2+ n ])))

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
       ℚ.isTrans< (fromNat m) (fromNat (suc N) ℚ.· fst ε) (((fst ε) ℚ.+ 1) ℚ^ⁿ suc (suc n))
         (subst (fromNat m ℚ.<_)
           (ℚ.·Comm (fst ε) (fromNat (suc N)))
              (ℚ.isTrans< (fromNat m) (fromNat (suc m)) (fst ε ℚ.· fromNat (suc N))
             (<ℤ→<ℚ (pos m) (pos (suc m)) (ℤ.≤→<suc (ℤ.isRefl≤ {pos m})))
              (ℚ.x/y<z→x<y·z (fromNat (suc m)) ε (fromNat (suc N)) X)))
          (ℚ.isTrans< (fromNat (suc N) ℚ.· fst ε)
            (fromNat (suc (suc n)) ℚ.· fst ε)
            (((fst ε) ℚ.+ 1) ℚ^ⁿ suc (suc n))
            (ℚ.<-·o
             (fromNat (suc N))
             (fromNat (suc (suc n))) (fst ε) (snd ε)
             (<ℤ→<ℚ (pos (suc N)) (pos (suc (suc n)))
               (ℤ.ℕ<→pos-<-pos (suc N) (suc (suc n)) <ssn)))
            (let
               k = fromNat (suc (suc n))
               εq = fst ε
               x = εq ℚ.+ 1
               left<lower : k ℚ.· εq ℚ.< (k ℚ.· (x ℚ.- 1)) ℚ.+ 1
               left<lower =
                 subst (k ℚ.· εq ℚ.<_) ℚ!
                   (ℚ≤→<+₊ (k ℚ.· εq) (k ℚ.· εq) 1 (ℚ.isRefl≤ (k ℚ.· εq)))
             in ℚ.isTrans< (k ℚ.· εq) ((k ℚ.· (x ℚ.- 1)) ℚ.+ 1) (x ℚ^ⁿ suc (suc n)) left<lower
             (bernoulli's-ineq-^ℚⁿ x n
               (subst (1 ℚ.<_) (ℚ.+Comm 1 εq)
                (ℚ≤→<+₊ 1 1 ε (ℚ.isRefl≤ 1))))))
      }


module _ (z : ℝ₊) where

 lnSeq=diff : ∀ n → ((fst (z ^ℚ (0 ℚ.+ [ 1 / 2+ n ])) -ᵣ
                fst (z ^ℚ 0)) ／ᵣ[ rat [ 1 / 2+ n ] , inl (snd (ℚ₊→ℝ₊ (stepℚ₊ n))) ])
                 ≡ lnSeq z n
 lnSeq=diff n = cong₂ _·ᵣ_ (cong₂ _-ᵣ_ (cong (fst ∘ (z ^ℚ_)) (ℚ.+IdL [ 1 / 2+ n ])) refl )
  (invℝ-rat [ 1 / 2+ n ] (inl (snd (ℚ₊→ℝ₊ (stepℚ₊ n)))) (inl (ℚ.0<pos 0 (2+ n)))
    ∙ cong rat (invℚ-unitFrac (2+ n) (inl (ℚ.0<pos 0 (2+ n)))))

 lnSeq≤ : ∀ n → lnSeq z n ≤ᵣ fst z -ᵣ 1
 lnSeq≤ n = subst2 _≤ᵣ_
   (cong ((fst (z ^ℚ ([ 1 / 2+ n ])) -ᵣ 1) ·ᵣ_)
     (invℝ₊-rat (posStepWidth n) ∙ cong rat (cong (fst ∘ invℚ₊)
    (posStepWidth≡fromNatInv n) ∙
      ℚ.invℚ₊-invol (fromNat (suc (suc n))))))

  (Rℝ.·IdR' (fst (z ^ℚ 1) -ᵣ 1)
    (fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 (ℚ.0<pos 0 1)))))
    (cong (fst ∘ invℝ₊) (ℝ₊≡ (cong rat ℚ!)) ∙ cong fst invℝ₊1)
    ∙ cong (_-ᵣ 1) (cong fst (^ℚ-1 z)))
   (slope-incr z 0 [ 1 / 2+ n ] 1
      (ℚ.0<pos 0 (2+ n))
      ((ℚ.invℚ₊≤invℚ₊ (fromNat (suc (suc n))) 1
        (≤ℤ→≤ℚ 1 (pos (suc (suc n)))
          (ℤ.ℕ≤→pos-≤-pos 1 (suc (suc n))
            (ℕ.suc-≤-suc (ℕ.zero-≤ {suc n}))))))

      (ℚ.0<pos 0 1))



 lnSeq≤lnSeq : ∀ n m → m ℕ.≤ n → lnSeq z n ≤ᵣ lnSeq z m
 lnSeq≤lnSeq n m m≤n =
   subst2 _≤ᵣ_
     (cong ((fst (z ^ℚ ([ 1 / 2+ n ])) -ᵣ 1) ·ᵣ_)
       (invℝ₊-rat (posStepWidth n) ∙ cong rat (cong (fst ∘ invℚ₊)
      (posStepWidth≡fromNatInv n) ∙
        ℚ.invℚ₊-invol (fromNat (suc (suc n))))))
     (cong ((fst (z ^ℚ ([ 1 / 2+ m ])) -ᵣ 1) ·ᵣ_)
       (invℝ₊-rat (posStepWidth m) ∙ cong rat (cong (fst ∘ invℚ₊)
      (posStepWidth≡fromNatInv m) ∙
        ℚ.invℚ₊-invol (fromNat (suc (suc m))))))
     (slope-monotone z 0 [ 1 / 2+ n ] 0 [ 1 / 2+ m ]
           (ℚ.0<pos 0 (2+ n)) (ℚ.0<pos 0 (2+ m)) (ℚ.0≤pos 0 1)
             (ℚ.invℚ₊≤invℚ₊ (fromNat (suc (suc n))) (fromNat (suc (suc m)))
              (≤ℤ→≤ℚ (pos (suc (suc m))) (pos (suc (suc n)))
                (ℤ.ℕ≤→pos-≤-pos (suc (suc m)) (suc (suc n)) (ℕ.≤-k+ {k = 2} m≤n)))))

 lnSeq'≤lnSeq' : ∀ m n → m ℕ.≤ n → lnSeq' z m ≤ᵣ lnSeq' z n
 lnSeq'≤lnSeq' m n m<n =
   subst2 _≤ᵣ_
     (cong ((1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ m ]))) ·ᵣ_)
       (invℝ₊-rat (negStepWidth m) ∙ cong rat (cong (fst ∘ invℚ₊)
        (negStepWidth≡fromNatInv m) ∙
          ℚ.invℚ₊-invol (fromNat (suc (suc m))))))
     (cong ((1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ]))) ·ᵣ_)
       (invℝ₊-rat (negStepWidth n) ∙ cong rat (cong (fst ∘ invℚ₊)
        (negStepWidth≡fromNatInv n) ∙
          ℚ.invℚ₊-invol (fromNat (suc (suc n))))))
     mono
  where
  a = ℚ.- [ 1 / 2+ m ]
  a' = ℚ.- [ 1 / 2+ n ]

  a<0 : a ℚ.< 0
  a<0 = ℚ.minus-< 0 [ 1 / 2+ m ] (ℚ.0<pos 0 (2+ m))

  a'<0 : a' ℚ.< 0
  a'<0 = ℚ.minus-< 0 [ 1 / 2+ n ] (ℚ.0<pos 0 (2+ n))

  a≤a' : a ℚ.≤ a'
  a≤a' =
    ℚ.minus-≤ [ 1 / 2+ n ] [ 1 / 2+ m ]
      (ℚ.invℚ₊≤invℚ₊ (fromNat (suc (suc n))) (fromNat (suc (suc m)))
        (≤ℤ→≤ℚ (pos (suc (suc m))) (pos (suc (suc n)))
          (ℤ.ℕ≤→pos-≤-pos (suc (suc m)) (suc (suc n)) (ℕ.≤-k+ {k = 2} m<n))))

  mono = slope-monotone z a 0 a' 0 a<0 a'<0 a≤a' (ℚ.isRefl≤ 0)


 lnSeq'≤lnSeq : ∀ n m → lnSeq' z n ≤ᵣ lnSeq z m
 lnSeq'≤lnSeq n m =
   subst2 _≤ᵣ_
     (cong ((1 -ᵣ fst (z ^ℚ (ℚ.- [ 1 / 2+ n ]))) ·ᵣ_)
      (invℝ₊-rat (negStepWidth n) ∙ cong rat (cong (fst ∘ invℚ₊)
     (negStepWidth≡fromNatInv n) ∙
       ℚ.invℚ₊-invol (fromNat (suc (suc n))))))
     (cong ((fst (z ^ℚ ([ 1 / 2+ m ])) -ᵣ 1) ·ᵣ_)
       (invℝ₊-rat (posStepWidth m) ∙ cong rat (cong (fst ∘ invℚ₊)
     (posStepWidth≡fromNatInv m) ∙
       ℚ.invℚ₊-invol (fromNat (suc (suc m))))))
     (slope-monotone z (ℚ.- [ 1 / 2+ n ]) 0 0 [ 1 / 2+ m ]
           (ℚ.minus-< 0 [ pos 1 / 2+ n ] (ℚ.0<pos 0 (2+ n))) (ℚ.0<pos 0 (2+ m))
          (ℚ.minus-≤ 0 [ pos 1 / 2+ n ] (ℚ.0≤pos 1 (2+ n))) (ℚ.0≤pos 1 (2+ m)))


seqΔ-δ : (Z : ℕ) → (ε : ℚ₊) → Σ ℕ λ N → (n : ℕ) →
            N ℕ.< n →
            fromNat (suc (suc Z)) ℚ.<
            ((fst (ε ℚ₊· invℚ₊ (fromNat (suc Z) ℚ₊· 2)) ℚ.+ 1) ℚ^ⁿ
             n)
seqΔ-δ Z ε = x^→∞ (suc (suc Z))
         (ε ℚ₊· (invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)))
