{-# OPTIONS --safe --lossy-unification #-}

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
         ∙ sym (·IdLᵣ _)) (cong fst (sym (invℝ₊Invol z)) ∙ sym (·IdLᵣ _))
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
                      IsContinuousWithPred-invℝ₊)))
                  (λ r r∈ r∈' → cong (flip diff n) (ℝ₊≡ refl)
                       ∙ w-r n r (ℚ<→0< _ (<ᵣ→<ℚ _ _ r∈'))
                   ∙ cong (flip diff n)
                    (cong₂ maxᵣ₊
                      (ℝ₊≡ refl)
                      (ℝ₊≡ {_} {_ , snd ((invℝ₊ (fst (ℚ₊→ℝ₊
                       (r , ℚ<→0< r (<ᵣ→<ℚ [ pos 0 / 1 ] r r∈'))) , r∈')))}
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
  ∙ congLim _ _ _ _ λ q → sym (Rℝ.0LeftAnnihilates' _ _
     (Rℝ.+InvR' (fst (1 ^ℚ [ 1 / 2+ _ ])) 1 (cong fst (1^ℚ≡1 _))))

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
                ∙ cong absᵣ
                    (cong ((-ᵣ lnSeq' z n) +ᵣ_)
                      (-ᵣInvol (preLn z z≤Z 1/Z≤z))
                    ∙ +ᵣComm (-ᵣ lnSeq' z n) (preLn z z≤Z 1/Z≤z))
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



       diff-shift-1 : ∀ u v → u -ᵣ v ≡ (u -ᵣ 1) -ᵣ (v -ᵣ 1)
       diff-shift-1 u v = sym (
         cong ((u -ᵣ 1) +ᵣ_)
           (-ᵣDistr v (-ᵣ 1) ∙ cong ((-ᵣ v) +ᵣ_) (-ᵣInvol 1))
         ∙ sym (+ᵣAssoc u (-ᵣ 1) ((-ᵣ v) +ᵣ 1))
         ∙ cong (u +ᵣ_)
             (+ᵣAssoc (-ᵣ 1) (-ᵣ v) 1
             ∙ cong (_+ᵣ 1) (+ᵣComm (-ᵣ 1) (-ᵣ v))
             ∙ sym (+ᵣAssoc (-ᵣ v) (-ᵣ 1) 1)
             ∙ cong ((-ᵣ v) +ᵣ_) (+ᵣComm (-ᵣ 1) 1 ∙ +-ᵣ 1)
             ∙ +IdR (-ᵣ v)))

       lnSeq-slope-rewrite : ∀ x y d n →
         (fromNat (suc (suc n)) ·ᵣ
           ((fst (root (1+ (suc n)) y) -ᵣ fst (root (1+ (suc n)) x)) ／ᵣ₊ d))
           ≡ ((lnSeq y n -ᵣ lnSeq x n) ／ᵣ₊ d)
       lnSeq-slope-rewrite x y d n =
         ·ᵣAssoc _ _ _
           ∙ cong (_／ᵣ₊ d)
             ((cong (fromNat (suc (suc n)) ·ᵣ_)
               (cong₂ _-ᵣ_ (sym (·IdR _)) (sym (·IdR _))
                ∙ diff-shift-1
                    (fst (y ^ℚ [ 1 / 2+ n ]))
                    (fst (x ^ℚ [ 1 / 2+ n ])))
             ∙ ·ᵣComm _ _
             ∙ Rℝ.·DistL- _ _ _))

       w : (n : ℕ) →
                (((lnSeq b' n) -ᵣ (lnSeq a' n)) ／ᵣ₊ b'-a')
             ≤ᵣ (((lnSeq b n) -ᵣ (lnSeq a n)) ／ᵣ₊ b-a)
       w n = subst2 _≤ᵣ_
         (lnSeq-slope-rewrite a' b' b'-a' n)
         (lnSeq-slope-rewrite a b b-a n)
         (≤ᵣ-o·ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos _ _))
           (slope-monotone-ₙ√ (suc n) _ _ _ _
             a<b a'<b' a≤a' b≤b'))
