module Cubical.HITs.CauchyReals.Exponentiation.LogSequence where

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
open import Cubical.HITs.CauchyReals.Partition using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.CauchyReals.Exponentiation.Core
open import Cubical.HITs.CauchyReals.Exponentiation.Convexity

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

open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceBase
open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceElementary
open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceDelta

module expPreDer (Z : ℕ) where
 module expPreDer' (z : ℝ₊)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z) where



  private
   diff : ℝ₊ → ℕ → ℝ
   diff u n = lnSeq u n -ᵣ lnSeq' u n

   z⊔z⁻¹ : ℝ₊
   z⊔z⁻¹ = maxᵣ₊ z (invℝ₊ z)

   z⊔z⁻¹≤Z : fst z⊔z⁻¹ ≤ᵣ fromNat (suc (suc Z))
   z⊔z⁻¹≤Z =
    max≤-lem
      (fst z) (fst (invℝ₊ z)) (fromNat (suc (suc Z)))
      z≤Z
      (subst2 _≤ᵣ_
        (·IdR _) (·IdR _)
        (fst
          (z/y'≤x/y≃y₊·z≤y'₊·x
            1 1 (invℝ₊ z) (fromNat (suc (suc Z))))
          (subst2 _≤ᵣ_
            ((sym (invℝ₊-rat (fromNat (suc (suc Z))))
            ∙ cong (fst ∘ invℝ₊) (ℝ₊≡ refl))
            ∙ sym (·IdLᵣ _))
            (cong fst (sym (invℝ₊Invol z)) ∙ sym (·IdLᵣ _))
            1/Z≤z)))

   opaque
    unfolding _+ᵣ_
    diff-continuous : ∀ n →
      IsContinuousWithPred pred0<
        (λ u 0<u → diff (u , 0<u) n)
    diff-continuous n =
      contDiagNE₂WP
        sumR pred0<
        (λ u 0<u → lnSeq (u , 0<u) n)
        (λ u 0<u → -ᵣ lnSeq' (u , 0<u) n)
        (lnSeqCont n)
        (IsContinuousWP∘'
          pred0<
          -ᵣ_
          (λ u 0<u → lnSeq' (u , 0<u) n)
          IsContinuous-ᵣ
          (lnSeq'Cont n))

   diff-rational-inverse : ∀ n r 0<r →
     diff (ℚ₊→ℝ₊ (r , 0<r)) n ≡
       diff (invℝ₊ (ℚ₊→ℝ₊ (r , 0<r))) n
   diff-rational-inverse n r 0<r =
     +ᵣComm _ _
     ∙ cong₂ _+ᵣ_
         (lnSeq'[z]≡lnSeq[1/x] n (ℚ₊→ℝ₊ (r , 0<r)))
         (lnSeq[z]≡lnSeq'[1/x] n (ℚ₊→ℝ₊ (r , 0<r)))

   opaque
    unfolding maxᵣ
    diff-rational-max : ∀ n r 0<r →
      diff (ℚ₊→ℝ₊ (r , 0<r)) n ≡
        diff
          (maxᵣ₊
            (ℚ₊→ℝ₊ (r , 0<r))
            (ℚ₊→ℝ₊ (invℚ₊ (r , 0<r))))
          n
    diff-rational-max n r 0<r =
      ⊎.rec
        (λ inverse≤r →
          cong (flip diff n)
            (ℝ₊≡
              {ℚ₊→ℝ₊ (r , 0<r)}
              {maxᵣ₊
                (ℚ₊→ℝ₊ (r , 0<r))
                (ℚ₊→ℝ₊ (invℚ₊ (r , 0<r)))}
              (sym
                (maxᵣComm
                  (fst (ℚ₊→ℝ₊ (r , 0<r)))
                  (fst (ℚ₊→ℝ₊ (invℚ₊ (r , 0<r))))
                ∙ ≤ᵣ→≡
                  (≤ℚ→≤ᵣ
                    (fst (invℚ₊ (r , 0<r))) r inverse≤r)))))
        (λ r≤inverse →
          diff-rational-inverse n r 0<r
          ∙ cong (flip diff n)
              (ℝ₊≡
                (invℝ₊-rat (r , 0<r)
                ∙ sym
                    (≤ᵣ→≡
                      (≤ℚ→≤ᵣ
                        r (fst (invℚ₊ (r , 0<r))) r≤inverse)))))
        (ℚ.≤cases (fst (invℚ₊ (r , 0<r))) r)

   diff-max : ∀ n u →
     diff u n ≡ diff (maxᵣ₊ u (invℝ₊ u)) n
   diff-max n (u , 0<u) =
     ≡ContinuousWithPred
       pred0< pred0<
       (openPred< 0) (openPred< 0)
       (λ r 0<r → diff (r , 0<r) n)
       (λ r 0<r →
         diff (maxᵣ₊ (r , 0<r) (invℝ₊ (r , 0<r))) n)
       (diff-continuous n)
       max-diff-continuous
       rational-case
       u 0<u 0<u
    where
    max-function : (r : ℝ) → 0 <ᵣ r → ℝ
    max-function r 0<r =
      fst (maxᵣ₊ (r , 0<r) (invℝ₊ (r , 0<r)))

    max-positive : ∀ r 0<r → 0 <ᵣ max-function r 0<r
    max-positive r 0<r =
      snd (maxᵣ₊ (r , 0<r) (invℝ₊ (r , 0<r)))

    opaque
     unfolding maxᵣ
     max-continuous : IsContinuousWithPred pred0< max-function
     max-continuous =
       contDiagNE₂WP
         maxR pred0<
         (λ r _ → r)
         (λ r 0<r → fst (invℝ₊ (r , 0<r)))
         (AsContinuousWithPred pred0< (λ r → r) IsContinuousId)
         IsContinuousWithPred-invℝ₊

    max-diff-continuous :
      IsContinuousWithPred pred0<
        (λ r 0<r →
          diff (maxᵣ₊ (r , 0<r) (invℝ₊ (r , 0<r))) n)
    max-diff-continuous =
      IsContinuousWP∘
        pred0< pred0<
        (λ r 0<r → diff (r , 0<r) n)
        max-function
        max-positive
        (diff-continuous n)
        max-continuous

    rational-case : ∀ r r∈ r∈' →
      diff (rat r , r∈) n ≡
        diff (maxᵣ₊ (rat r , r∈') (invℝ₊ (rat r , r∈'))) n
    rational-case r r∈ r∈' =
      cong (flip diff n)
        (ℝ₊≡
          {(rat r , r∈)}
          {ℚ₊→ℝ₊ r₊}
          refl)
      ∙ diff-rational-max n r 0<r
      ∙ cong (flip diff n)
          (cong₂ maxᵣ₊
            (ℝ₊≡
              {ℚ₊→ℝ₊ r₊}
              {(rat r , r∈')}
              refl)
            (ℝ₊≡
              {ℚ₊→ℝ₊ (invℚ₊ r₊)}
              {invℝ₊ (rat r , r∈')}
              (sym (invℝ₊-rat r₊)
              ∙ cong (fst ∘ invℝ₊)
                  (ℝ₊≡ {ℚ₊→ℝ₊ r₊} {(rat r , r∈')} refl))))
     where
     0<r : 0 ℚ.< r
     0<r = <ᵣ→<ℚ 0 r r∈'

     r₊ : ℚ₊
     r₊ = r , 0<r

  seqΔ : ∀ (ε : ℚ₊) →
     (∀ n → (fst (seqΔ-δ Z ε)) ℕ.< n →
        lnSeq z n -ᵣ lnSeq' z n <ᵣ (rat (fst ε)))

  seqΔ ε n a<n =
    isTrans≡<ᵣ
      (diff z n)
      (diff z⊔z⁻¹ n)
      (rat (fst ε))
      (diff-max n z)
      (seqΔ-pos
        z⊔z⁻¹ Z z⊔z⁻¹≤Z (1≤x-⊔-x⁻¹ z) ε n a<n)


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

  preLn : ℝ
  preLn = fromCauchySequence' _ ca-lnSeq

  preLn≤lnSeq : ∀ n → preLn ≤ᵣ (lnSeq z n)
  preLn≤lnSeq n =
    x<y+δ→x≤y  _ _ λ ε →
          let (m , M) = fromCauchySequence'-lim _ ca-lnSeq ε

              index : ℕ
              index = ℕ.max (suc m) n

              m<index : m ℕ.< index
              m<index = ℕ.left-≤-max {suc m} {n}

              n≤index : n ℕ.≤ index
              n≤index = ℕ.right-≤-max {n} {suc m}

              ii = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                   (isTrans≡<ᵣ _ _ _
                    (minusComm-absᵣ _ _)
                    (M index m<index))
          in isTrans<≤ᵣ _ _ _
               (a-b<c⇒a<c+b _ _ _ ii)
               (isTrans≤≡ᵣ _ _ _
                 (≤ᵣ-o+ _ _ (rat (fst ε))
                   (lnSeq≤lnSeq z index n n≤index))
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

 open expPreDer'

 0=preLn : (1≤ : fst 1 ≤ᵣ fromNat (suc (suc Z)))
           (≤1 : rat [ pos 1 / 2+ Z ] ≤ᵣ 1)
           → 0 ≡ preLn 1 1≤ ≤1
 0=preLn 1≤ ≤1 = sym
   (fromCauchySequence'-≡
      (lnSeq 1)
      (λ _ → 0)
      (ca-lnSeq 1 1≤ ≤1)
      (isCauchySequence'-const 0)
      lnSeq-one
    ∙ fromCauchySequence'-const 0 (isCauchySequence'-const 0))

 private
  opaque
   inverse-lnSeq-error-path :
     (z : ℝ₊)
     (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
     (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
     (n : ℕ)
     → absᵣ
         (lnSeq (invℝ₊ z) n -ᵣ -ᵣ preLn z z≤Z 1/Z≤z)
       ≡ preLn z z≤Z 1/Z≤z -ᵣ lnSeq' z n
   inverse-lnSeq-error-path z z≤Z 1/Z≤z n =
     cong
       (λ x → absᵣ (x -ᵣ -ᵣ preLn z z≤Z 1/Z≤z))
       (sym (lnSeq'[z]≡lnSeq[1/x] n z))
     ∙ cong absᵣ
         (cong
            ((-ᵣ lnSeq' z n) +ᵣ_)
            (-ᵣInvol (preLn z z≤Z 1/Z≤z))
         ∙ +ᵣComm
             (-ᵣ lnSeq' z n)
             (preLn z z≤Z 1/Z≤z))
     ∙ absᵣNonNeg
         (preLn z z≤Z 1/Z≤z -ᵣ lnSeq' z n)
         (x≤y→0≤y-x
           (lnSeq' z n)
           (preLn z z≤Z 1/Z≤z)
           (lnSeq'≤preLn z z≤Z 1/Z≤z n))

  opaque
   inverse-lnSeq-error-bound :
     (z : ℝ₊)
     (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
     (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
     (n : ℕ)
     → absᵣ
         (lnSeq (invℝ₊ z) n -ᵣ -ᵣ preLn z z≤Z 1/Z≤z)
       ≤ᵣ lnSeq z n -ᵣ lnSeq' z n
   inverse-lnSeq-error-bound z z≤Z 1/Z≤z n =
     isTrans≡≤ᵣ
       (absᵣ
         (lnSeq (invℝ₊ z) n -ᵣ -ᵣ preLn z z≤Z 1/Z≤z))
       (preLn z z≤Z 1/Z≤z -ᵣ lnSeq' z n)
       (lnSeq z n -ᵣ lnSeq' z n)
       (inverse-lnSeq-error-path z z≤Z 1/Z≤z n)
       (≤ᵣ-+o
         (preLn z z≤Z 1/Z≤z)
         (lnSeq z n)
         (-ᵣ lnSeq' z n)
         (preLn≤lnSeq z z≤Z 1/Z≤z n))

 preLn-inv : (z : ℝ₊)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
          (1/z≤Z : fst (invℝ₊ z) ≤ᵣ fromNat (suc (suc Z)))
           (1/Z≤1/z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst (invℝ₊ z))
           → preLn (invℝ₊ z) 1/z≤Z 1/Z≤1/z ≡ -ᵣ (preLn z z≤Z 1/Z≤z)
 preLn-inv z z≤Z 1/Z≤z 1/z≤Z 1/Z≤1/z =
   fromCauchySequence'≡
     (lnSeq (invℝ₊ z))
     (ca-lnSeq (invℝ₊ z) 1/z≤Z 1/Z≤1/z)
     (-ᵣ preLn z z≤Z 1/Z≤z)
     λ ε →
       ∣ fst (seqΔ-δ Z ε) ,
         (λ n threshold<n →
           isTrans≤<ᵣ
             (absᵣ
               (lnSeq (invℝ₊ z) n -ᵣ -ᵣ preLn z z≤Z 1/Z≤z))
             (lnSeq z n -ᵣ lnSeq' z n)
             (rat (fst ε))
             (inverse-lnSeq-error-bound z z≤Z 1/Z≤z n)
             (seqΔ z z≤Z 1/Z≤z ε n threshold<n)) ∣₁

 preLn<0 : (z : ℝ₊)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
          → fst z <ᵣ 1
          → preLn z z≤Z 1/Z≤z <ᵣ 0
 preLn<0 z z≤Z 1/Z≤z z<1 =
   <ᵣ-ᵣ _ 0
     (isTrans≡<ᵣ _ _ _ (-ᵣ-rat 0)
       (subst (0 <ᵣ_)
         (preLn-inv z z≤Z 1/Z≤z inv-z≤Z 1/Z≤inv-z)
         (expPreDer'.0<preLn (invℝ₊ z) inv-z≤Z 1/Z≤inv-z 1<inv-z)))
  where
  inv-z≤Z : fst (invℝ₊ z) ≤ᵣ fromNat (suc (suc Z))
  inv-z≤Z =
    isTrans≤≡ᵣ _ _ _
      (invEq (invℝ₊-≤-invℝ₊ z (ℚ₊→ℝ₊ (stepℚ₊ Z))) 1/Z≤z)
      (invℝ₊-rat (stepℚ₊ Z))

  1/Z≤inv-z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst (invℝ₊ z)
  1/Z≤inv-z =
    isTrans≡≤ᵣ _ _ _
      (sym (invℝ₊-rat (fromSucℚ₊ (suc Z))))
      (invEq
        (invℝ₊-≤-invℝ₊ (ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))) z)
        z≤Z)

  1<inv-z : 1 <ᵣ fst (invℝ₊ z)
  1<inv-z =
    fst (1/x<1≃1<x (invℝ₊ z))
      (isTrans≡<ᵣ _ _ _ (cong fst (invℝ₊Invol z)) z<1)

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

 private
  positiveIntervalWidth :
    (a b : ℝ₊) → fst a <ᵣ fst b → ℝ₊
  positiveIntervalWidth a b a<b =
    (fst b -ᵣ fst a , x<y→0<y-x (fst a) (fst b) a<b)

  opaque
   lnSeq-difference-shift :
     (u v : ℝ) → u -ᵣ v ≡ (u -ᵣ 1) -ᵣ (v -ᵣ 1)
   lnSeq-difference-shift u v = Simpleℝ.solve!

  opaque
   lnSeq-slope-path : (x y d : ℝ₊) (n : ℕ) →
     fromNat (suc (suc n)) ·ᵣ
       ((fst (root (1+ (suc n)) y) -ᵣ
         fst (root (1+ (suc n)) x)) ／ᵣ₊ d)
       ≡ (lnSeq y n -ᵣ lnSeq x n) ／ᵣ₊ d
   lnSeq-slope-path x y d n =
     ·ᵣAssoc _ _ _
     ∙ cong (_／ᵣ₊ d)
         (cong
            (fromNat (suc (suc n)) ·ᵣ_)
            (cong₂ _-ᵣ_ (sym (·IdR _)) (sym (·IdR _))
            ∙ lnSeq-difference-shift
                (fst (y ^ℚ fst (stepℚ₊ n)))
                (fst (x ^ℚ fst (stepℚ₊ n))))
         ∙ ·ᵣComm _ _
         ∙ Rℝ.·DistL- _ _ _)

  opaque
   lnSeq-slope-antitone :
     (a b a' b' : ℝ₊)
     (a<b : fst a <ᵣ fst b)
     (a'<b' : fst a' <ᵣ fst b')
     (a≤a' : fst a ≤ᵣ fst a')
     (b≤b' : fst b ≤ᵣ fst b')
     (n : ℕ)
     → ((lnSeq b' n -ᵣ lnSeq a' n) ／ᵣ₊
          positiveIntervalWidth a' b' a'<b')
       ≤ᵣ ((lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊
          positiveIntervalWidth a b a<b)
   lnSeq-slope-antitone a b a' b' a<b a'<b' a≤a' b≤b' n =
     subst2 _≤ᵣ_
       (lnSeq-slope-path a' b' (positiveIntervalWidth a' b' a'<b') n)
       (lnSeq-slope-path a b (positiveIntervalWidth a b a<b) n)
       (≤ᵣ-o·ᵣ
         ((fst (root (1+ (suc n)) b') -ᵣ
           fst (root (1+ (suc n)) a')) ／ᵣ₊
             positiveIntervalWidth a' b' a'<b')
         ((fst (root (1+ (suc n)) b) -ᵣ
           fst (root (1+ (suc n)) a)) ／ᵣ₊
             positiveIntervalWidth a b a<b)
         (fromNat (suc (suc n)))
         (≤ℚ→≤ᵣ
           0 [ pos (suc (suc n)) / 1 ]
           (ℚ.0≤pos (suc (suc n)) 1))
         (slope-monotone-ₙ√
           (suc n) a b a' b' a<b a'<b' a≤a' b≤b'))

  opaque
   unfolding _+ᵣ_ -ᵣ_
   preLn-slope-limit-path :
     (a b : ℝ₊)
     (a≤Z : fst a ≤ᵣ fromNat (suc (suc Z)))
     (1/Z≤a : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst a)
     (b≤Z : fst b ≤ᵣ fromNat (suc (suc Z)))
     (1/Z≤b : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst b)
     (a<b : fst a <ᵣ fst b)
     (L : ℚ₊)
     (lip : Lipschitz-ℝ→ℝ L
       (_·ᵣ fst (invℝ₊ (positiveIntervalWidth a b a<b))))
     → Σ[ caSlope ∈ IsCauchySequence'
          (λ n → (lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊
            positiveIntervalWidth a b a<b) ]
         fromCauchySequence'
           (λ n → (lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊
             positiveIntervalWidth a b a<b)
           caSlope
         ≡ (preLn b b≤Z 1/Z≤b -ᵣ preLn a a≤Z 1/Z≤a) ／ᵣ₊
             positiveIntervalWidth a b a<b
   preLn-slope-limit-path a b a≤Z 1/Z≤a b≤Z 1/Z≤b a<b L lip =
     fst slopeMapped ,
       sym (snd slopeMapped)
       ∙ cong (_／ᵣ₊ width)
           (sym (snd differenceMapped)
           ∙ cong
               (preLn b b≤Z 1/Z≤b +ᵣ_)
               (sym (snd negativeMapped)))
    where
    width : ℝ₊
    width = positiveIntervalWidth a b a<b

    negativeMapped :
      Σ[ caNegative ∈ IsCauchySequence' ((-ᵣ_) ∘ lnSeq a) ]
        -ᵣ preLn a a≤Z 1/Z≤a
          ≡ fromCauchySequence' ((-ᵣ_) ∘ lnSeq a) caNegative
    negativeMapped =
      map-fromCauchySequence'
        1 (lnSeq a) (ca-lnSeq a a≤Z 1/Z≤a) -ᵣ_ (snd -ᵣR)

    differenceMapped :
      Σ[ caDifference ∈ IsCauchySequence'
          (λ n → lnSeq b n -ᵣ lnSeq a n) ]
        preLn b b≤Z 1/Z≤b
          +ᵣ fromCauchySequence'
              ((-ᵣ_) ∘ lnSeq a)
              (fst negativeMapped)
          ≡ fromCauchySequence'
              (λ n → lnSeq b n -ᵣ lnSeq a n)
              caDifference
    differenceMapped =
      mapNE-fromCauchySequence'
        sumR
        (lnSeq b) (ca-lnSeq b b≤Z 1/Z≤b)
        ((-ᵣ_) ∘ lnSeq a) (fst negativeMapped)

    slopeMapped :
      Σ[ caSlope ∈ IsCauchySequence'
          (λ n → (lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊ width) ]
        (fromCauchySequence'
          (λ n → lnSeq b n -ᵣ lnSeq a n)
          (fst differenceMapped) ／ᵣ₊ width)
          ≡ fromCauchySequence'
              (λ n → (lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊ width)
              caSlope
    slopeMapped =
      map-fromCauchySequence'
        L
        (λ n → lnSeq b n -ᵣ lnSeq a n)
        (fst differenceMapped)
        (_·ᵣ fst (invℝ₊ width))
        lip

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
        PT.rec2
          (isProp≤ᵣ _ _)
          compareLimits
          (∃Lipschitz-·R (fst (invℝ₊ width')))
          (∃Lipschitz-·R (fst (invℝ₊ width)))
    where
    width' : ℝ₊
    width' = positiveIntervalWidth a' b' a'<b'

    width : ℝ₊
    width = positiveIntervalWidth a b a<b

    compareLimits :
      Σ[ L' ∈ ℚ₊ ] Lipschitz-ℝ→ℝ L'
        (_·ᵣ fst (invℝ₊ width'))
      → Σ[ L ∈ ℚ₊ ] Lipschitz-ℝ→ℝ L
        (_·ᵣ fst (invℝ₊ width))
      → ((preLn b' b'≤Z 1/Z≤b' -ᵣ preLn a' a'≤Z 1/Z≤a')
          ／ᵣ₊ width')
        ≤ᵣ ((preLn b b≤Z 1/Z≤b -ᵣ preLn a a≤Z 1/Z≤a)
          ／ᵣ₊ width)
    compareLimits (L' , lip') (L , lip) =
      subst2 _≤ᵣ_
        (snd leftLimit)
        (snd rightLimit)
        (fromCauchySequence'≤
          (λ n → (lnSeq b' n -ᵣ lnSeq a' n) ／ᵣ₊ width')
          (fst leftLimit)
          (λ n → (lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊ width)
          (fst rightLimit)
          (lnSeq-slope-antitone
            a b a' b' a<b a'<b' a≤a' b≤b'))
     where
     leftLimit :
       Σ[ caSlope ∈ IsCauchySequence'
          (λ n → (lnSeq b' n -ᵣ lnSeq a' n) ／ᵣ₊ width') ]
         fromCauchySequence'
           (λ n → (lnSeq b' n -ᵣ lnSeq a' n) ／ᵣ₊ width')
           caSlope
         ≡ (preLn b' b'≤Z 1/Z≤b' -ᵣ preLn a' a'≤Z 1/Z≤a')
             ／ᵣ₊ width'
     leftLimit =
       preLn-slope-limit-path
         a' b' a'≤Z 1/Z≤a' b'≤Z 1/Z≤b' a'<b' L' lip'

     rightLimit :
       Σ[ caSlope ∈ IsCauchySequence'
          (λ n → (lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊ width) ]
         fromCauchySequence'
           (λ n → (lnSeq b n -ᵣ lnSeq a n) ／ᵣ₊ width)
           caSlope
         ≡ (preLn b b≤Z 1/Z≤b -ᵣ preLn a a≤Z 1/Z≤a)
             ／ᵣ₊ width
     rightLimit =
       preLn-slope-limit-path
         a b a≤Z 1/Z≤a b≤Z 1/Z≤b a<b L lip
