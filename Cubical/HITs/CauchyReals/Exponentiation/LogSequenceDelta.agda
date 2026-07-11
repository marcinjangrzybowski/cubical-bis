{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.LogSequenceDelta where

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
open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceElementary
open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceInequalities

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.CommRing.Properties as CR

opaque
 unfolding -ᵣ_ _+ᵣ_

 seqΔ-pos : ∀ z Z → (z<Z : fst z ≤ᵣ fromNat (suc (suc Z))) →
    1 ≤ᵣ fst z → ∀ (ε : ℚ₊) →
    (∀ n → (fst (seqΔ-δ Z ε)) ℕ.< n →
       lnSeq z n -ᵣ lnSeq' z n <ᵣ (rat (fst ε)))

 seqΔ-pos z Z z≤Z 1≤z ε =
  let (N , X) = x^→∞ (suc (suc Z))
         (ε ℚ₊· (invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)))
  in λ { n N<n →
     let
         X' = X (suc (suc n)) (ℕ.≤-trans N<n (ℕ.≤SumRight {k = 2}) )
         X'' = isTrans<≡ᵣ _ _ _ (a<c+b⇒a-b<c _ _ _
             (isTrans<≡ᵣ _ _ _ (^ℚ-StrictMonotone {fromNat (suc (suc Z)) }
                {ℚ₊→ℝ₊
                  (((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) +₊ 1)
                   ℚ₊^ⁿ (suc (suc n)))}
                 (stepℚ₊ n)
                 (<ℚ→<ᵣ _ _ X'))
                 (cong (fst ∘ _^ℚ [ pos 1 / 1+ (suc n) ])
                   (ℝ₊≡ (sym (^ⁿ-ℚ^ⁿ (suc (suc n))
                     (fst ((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) +₊ 1)))))
                  ∙  cong fst (^ℚ-·
                      (ℚ₊→ℝ₊
                       ((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) +₊ 1))
                       (fromNat (suc (suc n))) [ pos 1 / 1+ (suc n) ])
                       ∙ cong (fst ∘
                          (ℚ₊→ℝ₊ ((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2))
                            +₊ 1) ^ℚ_)) (ℚ.x·invℚ₊[x] (fromNat (suc (suc n))))
                       ∙ cong fst (^ℚ-1
                           (ℚ₊→ℝ₊ ((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) +₊ 1)))
                       ∙ sym (+ᵣ-rat (fst ε ℚ.· fst (invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2))) 1)
                       ∙ cong (_+ᵣ 1)
                           (rat·ᵣrat (fst ε) (fst (invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)))))))
                       (cong (rat (fst ε) ·ᵣ_)
                         (sym (invℝ₊-rat ((fromSucℚ₊ Z) ℚ₊· 2))))
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
        ∙ sym (Rℝ.·DistL- _ _ _))
       (isTrans≤<ᵣ _ _ _
         (isTrans≤≡ᵣ _ _ _ (≤ᵣ-·ᵣo _ _ (fromNat (suc (suc n)))
          (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos _ _))
          ((x+1/x-bound _ (isTrans≤ᵣ _ _ _
             decℚ≤ᵣ?
             (1≤^ℚ z
               (stepℚ₊ n)
               1≤z)
               ))))
          (sym (·ᵣAssoc _ _ _)))
          (isTrans≤<ᵣ _ _ _
           (≤ᵣ₊Monotone·ᵣ _ _ _ _
           (let w = fst (x≤y≃0≤y-x _ _) (1≤^ℚ z (stepℚ₊ n) 1≤z)
            in isTrans≡≤ᵣ _ _ _ (sym (Rℝ.0RightAnnihilates 2) ) (≤ᵣ-o·ᵣ _ _ 2 decℚ≤ᵣ?
                   (x≤y→0≤y-x 1 (fst (fromNat (suc (suc Z)) ^ℚ [ 1 / 2+ n ])) (1≤^ℚ (fromNat (suc (suc Z))) (stepℚ₊ n)
                    (isTrans≤ᵣ _ _ _ 1≤z z≤Z)))))


            (0≤ᵣlnSeq _)
             (≤ᵣ-o·ᵣ _ _ 2 decℚ≤ᵣ?
              (≤ᵣ-+o _ _ -1
               (^ℚ-Monotone {y = fromNat (suc (suc Z))} (stepℚ₊ n) z≤Z)))
             (isTrans≤ᵣ _ _ _ (lnSeq≤ z n)
               (≤ᵣ-+o _ _ -1 z≤Z)))
           (isTrans≡<ᵣ _ _ _ (·ᵣComm _ _ ∙  (·ᵣAssoc _ _ _) ∙
            cong (_·ᵣ (fst (fromNat (suc (suc Z)) ^ℚ [ 1 / 2+ n ]) +ᵣ -1))
             (cong (_·ᵣ 2) (+ᵣ-rat [ pos (suc (suc Z)) / 1 ] (ℚ.- [ pos 1 / 1 ])) ∙
              sym (rat·ᵣrat ([ pos (suc (suc Z)) / 1 ] ℚ.- [ pos 1 / 1 ]) 2)) )
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
      w = fst (x≤y≃0≤y-x _ _) (1≤^ℚ z (stepℚ₊ n) 1≤z)
