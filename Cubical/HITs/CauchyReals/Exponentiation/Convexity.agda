{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.Convexity where

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
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.Order public using (pred0< ; pred1<)
open import Cubical.HITs.CauchyReals.Order hiding (pred0< ; pred1<)
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisection
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Exponentiation.Core

fromNatℝ+ : ∀ {x y z} →
    x ℕ.+ y ≡ z →
    HasFromNat.fromNat fromNatℝ x +ᵣ HasFromNat.fromNat fromNatℝ y
      ≡ HasFromNat.fromNat fromNatℝ z
fromNatℝ+ p = +ᵣ-rat _ _ ∙ cong rat (ℚ.ℕ+→ℚ+  _ _ ∙ cong ([_/ 1 ] ∘ pos) p)

square-minus-one-expanded : ∀ t →
  (t -ᵣ 1) ·ᵣ (t -ᵣ 1)
    ≡ (t ·ᵣ t +ᵣ 1 ·ᵣ 1) +ᵣ -ᵣ (t ·ᵣ 1 +ᵣ t ·ᵣ 1)
square-minus-one-expanded t = ℝ!

AM-GM₂ : ∀ z → 1 <ᵣ fst z → ∀ x (Δ : ℚ₊) →
          fst (2 ₊·ᵣ (z ^ℚ x)) <ᵣ
            fst ((z ^ℚ (x ℚ.- fst Δ)) ₊+ᵣ (z ^ℚ (x ℚ.+ fst Δ)))
AM-GM₂ z 1<z x Δ = isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
       (cong (2 ·ᵣ_) (cong (fst ∘ z ^ℚ_) ℚ!
          ∙ sym (cong fst (^ℚ-+ z _ _)))
          ∙ ·ᵣComm _ _ ∙ sym (·ᵣAssoc _ _ _))
       (fst (z<x≃y₊·z<y₊·x _ _ (z ^ℚ (x ℚ.- fst Δ))) (isTrans≡<ᵣ _ _ _
         (cong (fst a ·ᵣ_) (sym (fromNatℝ+ refl))
           ∙ ·DistL+ (fst a) 1 1)
       (invEq (x<y≃0<y-x _ _)
      $ isTrans<≡ᵣ _ _ _ (ℝ₊· (fst a -ᵣ 1 , w') (fst a -ᵣ 1 , w'))
       (square-minus-one-expanded (fst a))))))
        (·DistL+ _ _ _ ∙ +ᵣComm _ _ ∙
          cong₂ _+ᵣ_
          (cong (((z ^ℚ (x ℚ.- fst Δ)) .fst) ·ᵣ_)
              (sym (rat·ᵣrat _ _)) ∙ ·IdR _)
              (cong (((z ^ℚ (x ℚ.- fst Δ)) .fst) ·ᵣ_)
                (cong fst (^ℚ-+ z _ _)) ∙
                  (cong fst (^ℚ-+ z _ _)) ∙
                    cong (fst ∘ z ^ℚ_)
                      ℚ!))


 where
 a = z ^ℚ (fst Δ)
 w' = fst (x<y≃0<y-x _ _) (1<^ℚ z Δ 1<z)

invℚ₊-fromNat : ∀ m → fst (invℚ₊ (fromNat (suc m))) ≡ [ pos 1 / 1+ m ]
invℚ₊-fromNat m =
  sym (ℚ.·IdL [ pos 1 / 1+ m ]) ∙
  cong₂ [_/_] (ℤ.·IdR (pos 1)) (·₊₁-identityˡ (1+ m))

invℚ₊-[/] : ∀ n m → [ n / 1 ] ℚ.· fst (invℚ₊ (fromNat (suc m))) ≡ [ n / 1+ m ]
invℚ₊-[/] n m =
  cong ([ n / 1 ] ℚ.·_) (invℚ₊-fromNat m)
  ∙ sym (ℚ.[/]≡· n (1+ m))

[2+N]/[1+N]=2-N/[1+N] : ∀ n →
   [ pos (2 ℕ.+ n) , (1+ n) ] ≡ (fromNat 2) ℚ.- [ pos n / 1+ n ]
[2+N]/[1+N]=2-N/[1+N] n = eq/ _ _ ℤ!

module AM-GM-hlp (b : ℝ₊) (1<b : 1 <ᵣ (fst b)) (x₀ : ℚ) (s : ℚ₊) where

 x : ℕ → ℚ
 x n = x₀ ℚ.+ fromNat n ℚ.· fst s

 -- TODO : this should be used in few places bellow:
 x-suc : ∀ n → x n ℚ.+ fst s ≡ x (suc n)
 x-suc n = sym (ℚ.+Assoc _ _ _)
     ∙ cong (x₀ ℚ.+_) (
       cong ((fromNat n) ℚ.· (fst s) ℚ.+_) (sym (ℚ.·IdL _)) ∙∙
       sym (ℚ.·DistR+  (fromNat n) 1 (fst s)) ∙∙
           cong (ℚ._· (fst s)) (ℚ.+Comm _ _ ∙ (ℚ.ℕ+→ℚ+ 1 n) ) )

 α : ℝ₊
 α = (1 ₊+ᵣ (b ^ℚ (2 ℚ.· fst s))) ₊·ᵣ ℚ₊→ℝ₊ ( [ 1 / 2 ] , 1/2∈ℚ.0<1/2 )

 y : ℕ → ℝ₊
 y zero = b ^ℚ x₀
 y (suc n) = (b ^ℚ (x n)) ₊·ᵣ α

 double-sub-shuffleᵣ : ∀ x y x' →
   ((x -ᵣ y) +ᵣ (x -ᵣ y)) -ᵣ (x' -ᵣ y) ≡
   (x +ᵣ x) -ᵣ x' -ᵣ y
 double-sub-shuffleᵣ _ _ _ = ℝ!



 fromAM-GM : fst (b ^ℚ x 1) <ᵣ
      fst (b ^ℚ x₀) +ᵣ
      rat (fst (invℚ₊ (fromNat 2))) ·ᵣ (fst (b ^ℚ x 2) -ᵣ fst (b ^ℚ x₀))
 fromAM-GM = isTrans≡<ᵣ _ _ _ (cong (fst ∘ b ^ℚ_ ∘ (x₀ ℚ.+_ ))
      (ℚ.·IdL _))
    (isTrans<≡ᵣ _ _ _ (invEq (z<x/y₊≃y₊·z<x _ _ 2)
   (AM-GM₂ b 1<b (x₀ ℚ.+ fst s) s))
    (cong (_·ᵣ fst (invℝ₊ 2))
       (cong₂ _+ᵣ_
          (cong (fst ∘ b ^ℚ_) (sym ℚ!)
          ∙ sym (Rℝ.plusMinus _ _)
          ∙ cong (_-ᵣ fst (b ^ℚ x₀))
              (Cubical.HITs.CauchyReals.Multiplication.x+x≡2x _ ∙ ·ᵣComm _ _))
          (cong (fst ∘ b ^ℚ_) (sym (ℚ.+Assoc _ _ _)
          ∙ cong (x₀ ℚ.+_) (ℚ.x+x≡2x _)))
       ∙ sym (+ᵣAssoc _ _ _))
      ∙ ·DistR+ (fst (b ^ℚ x₀) ·ᵣ 2) _ _
      ∙ cong₂ _+ᵣ_ ([x·yᵣ]/₊y _ _)
          (·ᵣComm _ _
          ∙ cong₂ _·ᵣ_ (invℝ₊-rat 2) (+ᵣComm _ _))))

 opaque
  unfolding -ᵣ_ _+ᵣ_
  convStep : ∀ N → rat (fst (invℚ₊ (fromNat (suc N)))) ·ᵣ
       (fst (b ^ℚ x (suc N)) -ᵣ fst (b ^ℚ x₀))
       <ᵣ
       rat (fst (invℚ₊ (fromNat (suc (suc N))))) ·ᵣ
       (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀))

  convSteps : ∀ N n → n ℕ.< N →
                  fst (b ^ℚ (x (suc n))) <ᵣ
                     (fst (b ^ℚ x₀) +ᵣ (rat (fst (fromNat (suc n)
                      ·₊ invℚ₊ (fromNat (suc N)))) ·ᵣ
                       (fst (b ^ℚ (x (suc N))) -ᵣ fst (b ^ℚ x₀))  ))
  convSteps zero n n<0 = ⊥.rec (ℕ.¬-<-zero n<0)
  convSteps (suc N) n n<sN@(N-n@(suc k) , p) =
    let X = convSteps N n (k , cong predℕ p)
    in isTrans<ᵣ _ _ _ X (<ᵣ-o+ _ _ _
         (subst2 _<ᵣ_ (·ᵣAssoc _ _ _ ∙
             cong (_·ᵣ ((fst (b ^ℚ (x (suc N))) -ᵣ fst (b ^ℚ x₀))))
            (sym (rat·ᵣrat  (fromNat (suc n))
             (fst $ invℚ₊ (fromNat (suc N))))))

           (·ᵣAssoc _ _ _ ∙
             cong (_·ᵣ ((fst (b ^ℚ (x (suc (suc N)))) -ᵣ fst (b ^ℚ x₀))))
            (sym (rat·ᵣrat (fromNat (suc n))
             (fst $ invℚ₊ (fromNat (suc (suc N)))))))
           (fst (z<x≃y₊·z<y₊·x _ _ (fromNat (suc n)))
             (convStep N))))
  convSteps (suc zero) zero (zero , 1+n=1+N) = fromAM-GM
  convSteps (suc (suc N)) zero (zero , 1+n=1+N) =
    ⊥.rec (ℕ.znots (cong predℕ 1+n=1+N))
  convSteps (suc N) (suc n) (zero , 2+n=1+N) =
    subst2 _<ᵣ_
      (cong (fst ∘ (b ^ℚ_) ∘ x) (sym 2+n=1+N))
      (cong
        (λ sn → fst (b ^ℚ x₀) +ᵣ
          rat (fst (fromNat (suc (predℕ sn)) ·₊ invℚ₊ (fromNat (suc (suc N)))))
          ·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
        (sym 2+n=1+N))
      (isTrans<≡ᵣ _ _ _
        (a-b<c⇒a<c+b (fst (b ^ℚ x (suc N))) _ _
          (invEq (z<x/y₊≃y₊·z<x _ _ (ℚ₊→ℝ₊ (invℚ₊ (fromNat (suc N)))))
            (convStep N)))
        (cong (_+ᵣ fst (b ^ℚ x₀))
          (sym (·ᵣAssoc _ _ _)
          ∙ cong (rat (fst (invℚ₊ (fromNat (suc (suc N))))) ·ᵣ_)
              (·ᵣComm _ _)
          ∙ ·ᵣAssoc _ _ _
          ∙ cong (_·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
              ((cong (rat (fst (invℚ₊ (fromNat (suc (suc N))))) ·ᵣ_)
                (invℝ₊-rat (invℚ₊ (fromNat (suc N)))
                ∙ cong rat (ℚ.invℚ₊-invol _))
              ∙ sym (rat·ᵣrat _ (fromNat (suc N))))
              ∙ cong rat (ℚ.·Comm _ _)))
        ∙ +ᵣComm _ _))


  convStep zero = isTrans≡<ᵣ _ _ _
    (·IdLᵣ _) (a<c+b⇒a-c<b _ _  _ fromAM-GM)
  convStep (suc N) =
    isTrans<ᵣ _ _ _
      (isTrans<≡ᵣ _ _ _
        (invEq (z<x/y₊≃y₊·z<x _ _ (fromNat (suc (suc (suc N)))))
          (isTrans≡<ᵣ _ _ _
            (·ᵣAssoc _ _ _
            ∙ cong (_·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
                (sym (rat·ᵣrat _ _)
                ∙ cong rat ((invℚ₊-[/] _ _) ∙ [2+N]/[1+N]=2-N/[1+N] (suc N)))
            ∙ cong (_·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
                (sym (+ᵣ-rat (fromNat 2) (ℚ.- [ pos (suc N) / 2+ N ]))
                ∙ cong (2 +ᵣ_) (sym (-ᵣ-rat [ pos (suc N) / 2+ N ])))
            ∙ ·DistR+ 2 (-ᵣ (rat [ _ / _ ])) _)
            (isTrans<≡ᵣ _ _ _
              (<ᵣ-o+ _ _ _
                (isTrans≡<ᵣ _ _ _ (-ᵣ· _ _)
                  (-ᵣ<ᵣ _ _
                    (isTrans<≡ᵣ _ _ _
                      (a<c+b⇒a-c<b _ _ _ (convSteps (suc N) N ℕ.≤-refl))
                      (cong (_·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
                        (cong rat (invℚ₊-[/] (pos (suc N)) (suc N))))))))
       (cong (_-ᵣ (fst (b ^ℚ x (suc N)) -ᵣ fst (b ^ℚ x₀)))
         (sym (Cubical.HITs.CauchyReals.Multiplication.x+x≡2x _))
       ∙∙ double-sub-shuffleᵣ _ _ _ ∙∙
       cong ((_-ᵣ fst (b ^ℚ x₀)) ∘ (_-ᵣ fst (b ^ℚ x (suc N))))
         (Cubical.HITs.CauchyReals.Multiplication.x+x≡2x _)))))
        (cong
          ((fst (2 ₊·ᵣ (b ^ℚ x (suc (suc N))))
          -ᵣ fst (b ^ℚ x (suc N)) +ᵣ
          -ᵣ fst (b ^ℚ x₀)) ·ᵣ_)
          (invℝ₊-rat (fromNat (suc (suc (suc N)))))
        ∙ ·ᵣComm _ _))
       (<ᵣ-o·ᵣ _ _
         (ℚ₊→ℝ₊ (invℚ₊ (fromNat (suc (suc (suc N))))))
        (<ᵣ-+o _ _ _
          (a<c+b⇒a-c<b _ _
            (fst (b ^ℚ (x (suc N))))
            (isTrans<≡ᵣ _ _ _
              (AM-GM₂ b 1<b (x (suc (suc N))) s)
              (cong₂ _+ᵣ_
                (cong (fst ∘ (b ^ℚ_))
                  (cong (ℚ._- (fst s)) (sym (x-suc (suc N))) ∙ sym ℚ!))
                (cong (fst ∘ (b ^ℚ_)) (x-suc (suc (suc N)))))))))



AM-GM-strict : ∀ z x → (1 <ᵣ fst z) → (Δ : ℚ₊) → (α : ℚ) → 0 ℚ.< α → α ℚ.< 1 →
          fst (z ^ℚ (x ℚ.+ (α ℚ.· fst Δ))) <ᵣ
            fst (z ^ℚ x) +ᵣ
              (rat α) ·ᵣ
                (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x))
AM-GM-strict z x 1<z Δ = ElimProp.go w
  where
  w : ElimProp _
  w .ElimProp.isPropB _ = isPropΠ2 λ _ _ → isProp<ᵣ _ _
  w .ElimProp.f (pos zero , (1+ m)) 0<α α<1 =
    ⊥.rec (ℚ.isIrrefl< 0
      (subst (0 ℚ.<_) (ℚ.[0/n]≡[0/m] m 0) 0<α))
  w .ElimProp.f (pos (suc n) , (1+ m)) 0<α α<1 =
   subst2 _<ᵣ_
     (cong (fst ∘ z ^ℚ_ ∘ (x ℚ.+_))
         (ℚ.·Assoc _ [ pos 1 / 1+ m ] _ ∙
            cong (ℚ._· (fst Δ)) n/N-lem))
     ((cong (fst (z ^ℚ x) +ᵣ_)
       (cong₂ _·ᵣ_ (cong rat n/N-lem)
         (cong (_-ᵣ (fst (z ^ℚ x)))
           ((cong (fst ∘ z ^ℚ_ ∘ (x ℚ.+_))
              (ℚ.·Assoc _ [ pos 1 / 1+ m ] _ ∙
            cong (ℚ._· (fst Δ)) (ℚ.x·invℚ₊[x] (fromNat (suc m)))
              ∙ ℚ.·IdL _)))))))
     ww
   where
    Δ/N : ℚ₊
    Δ/N = ([ pos 1 / 1+ m ] , ℚ.0<pos 0 (1+ m)) ·₊ Δ

    n/N-lem : [ pos (suc n) / 1 ] ℚ.· [ pos 1 / 1+ m ] ≡ [ pos (suc n) / 1+ m ]
    n/N-lem = cong₂ [_/_] (ℤ.·IdR (pos (suc n))) (·₊₁-identityˡ (1+ m))

    ww = AM-GM-hlp.convSteps z 1<z x Δ/N m n
         (ℕ.predℕ-≤-predℕ (ℤ.pos-≤-pos→ℕ≤ _ _
           (ℤ.<→suc≤ (subst2 ℤ._<_ (ℤ.·IdR _) (ℤ.·IdL _)
             (α<1 .ℚ._<_.prf)))))
  w .ElimProp.f α@(ℤ.negsuc n , 1+ m) 0<α _ =
    ⊥.rec $ ℤ.¬pos≤negsuc (subst (0 ℤ.≤_) (ℤ.·IdR _)
             ((ℚ.<Weaken≤ 0 SQ.[ α ] 0<α) .ℚ._≤_.prf))

AM-GM : ∀ z x → (1 <ᵣ fst z) → (Δ : ℚ₊) → (α : ℚ) → 0 ℚ.≤ α → α ℚ.≤ 1 →
          fst (z ^ℚ (x ℚ.+ (α ℚ.· fst Δ))) ≤ᵣ
            fst (z ^ℚ x) +ᵣ
              (rat α) ·ᵣ
                (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x))

AM-GM z x 1<z Δ α 0≤α α≤1 =
 ⊎.rec
   (λ α≡1 → ≡ᵣWeaken≤ᵣ
       (fst (z ^ℚ (x ℚ.+ α ℚ.· fst Δ)))
       (fst (z ^ℚ x) +ᵣ rat α ·ᵣ (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x)))
       (cong {y = fst Δ} (fst ∘ (z ^ℚ_) ∘ (x ℚ.+_))
          (cong (ℚ._· _) α≡1 ∙ ℚ.·IdL _)
        ∙∙ sym ℝ!
        ∙∙ cong (fst (z ^ℚ x) +ᵣ_)
             (sym (cong ((_·ᵣ (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x))
               ) ∘ rat) α≡1 ∙ ·IdLᵣ _))))
   (⊎.rec
      (λ 0=α _ → ≡ᵣWeaken≤ᵣ _ _
         (cong (fst ∘ (z ^ℚ_))
            (Rℚ.+IdR' x _
               (cong (ℚ._· (fst Δ)) (sym 0=α)
                 ∙ Rℚ.0LeftAnnihilates _))
           ∙ sym (Rℝ.+IdR' _ _
           (cong (_·ᵣ (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x)))
             (cong rat (sym 0=α))
            ∙ Rℝ.0LeftAnnihilates _))))
      ((<ᵣWeaken≤ᵣ _ _ ∘_) ∘ (AM-GM-strict z x 1<z Δ α))
      (ℚ.≤→≡⊎< 0 α 0≤α))
   (ℚ.≤→≡⊎< α 1 α≤1)

^ⁿ-1 : ∀ x → x ^ⁿ 1 ≡ x
^ⁿ-1 x = ·IdR _

^ℚ-1 : ∀ x → x ^ℚ 1 ≡ x
^ℚ-1 x = ℝ₊≡ (^ⁿ-1 _)

diff-split : ∀ x y z → z -ᵣ x ≡ (y -ᵣ x) +ᵣ (z -ᵣ y)
diff-split x y z = sym $
  (y -ᵣ x) +ᵣ (z -ᵣ y)    ≡⟨ Rℝ.+Assoc _ _ _ ⟩
  ((y -ᵣ x) +ᵣ z) +ᵣ -ᵣ y ≡⟨ cong (_+ᵣ -ᵣ y) (+ᵣComm (y -ᵣ x) z) ⟩
  (z +ᵣ (y -ᵣ x)) +ᵣ -ᵣ y ≡⟨ sym (Rℝ.+Assoc _ _ _) ⟩
  z +ᵣ ((y -ᵣ x) +ᵣ -ᵣ y) ≡⟨ cong (z +ᵣ_) y-x-y≡-x ⟩
  z -ᵣ x                         ∎
  where
  y-x-y≡-x : (y -ᵣ x) +ᵣ -ᵣ y ≡ -ᵣ x
  y-x-y≡-x =
    (y -ᵣ x) +ᵣ -ᵣ y      ≡⟨ sym (Rℝ.+Assoc _ _ _) ⟩
    y +ᵣ (-ᵣ x +ᵣ -ᵣ y)   ≡⟨ cong (y +ᵣ_) (+ᵣComm (-ᵣ x) (-ᵣ y)) ⟩
    y +ᵣ (-ᵣ y +ᵣ -ᵣ x)   ≡⟨ Rℝ.+Assoc _ _ _ ⟩
    (y +ᵣ -ᵣ y) +ᵣ -ᵣ x   ≡⟨ cong (_+ᵣ -ᵣ x) (Rℝ.+InvR y) ⟩
    0 +ᵣ -ᵣ x             ≡⟨ Rℝ.+IdL _ ⟩
    -ᵣ x                  ∎

-- AM-GM



slope-incr-strict : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ)
  → (a<b : a ℚ.< b) → (b<c : b ℚ.< c) →  (a<c : a ℚ.< c) →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      <ᵣ
  ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))
slope-incr-strict z 1<z a b c a<b b<c a<c =
  isTrans≡<ᵣ _ _ _
     (cong (_·ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b))))
      (cong (_-ᵣ fst (z ^ℚ a))
          (cong (fst ∘ (z ^ℚ_))
            (sym ℚ! ∙ cong (a ℚ.+_)
              (sym (ℚ.y·[x/y]
                (ℚ.<→ℚ₊ a c a<c)
                (fst (ℚ.<→ℚ₊ a b a<b))) ∙
             ℚ.·Comm _ _ ∙
              cong (ℚ._· fst (ℚ.<→ℚ₊ a c a<c))
               (ℚ.·Comm _ _))))))
      (isTrans<≡ᵣ _ _ _
       amgm
       (·ᵣComm _ _
       ∙ cong₂ _·ᵣ_
           (cong (_-ᵣ fst (z ^ℚ a))
             (cong (fst ∘ (z ^ℚ_)) ℚ!))
           (sym (invℝ₊-rat (ℚ.<→ℚ₊ _ _ a<c)))))

 where
 α₊ = (ℚ.<→ℚ₊ _ _  a<b ) ·₊ invℚ₊ (ℚ.<→ℚ₊ _ _  a<c )
 α<1 : fst α₊ ℚ.< 1
 α<1 = ℚ.x<y·z→x/y<z _ _ _
   (subst (b ℚ.- a ℚ.<_)
    (sym (ℚ.·IdR _))
    (ℚ.<-+o _ _ (ℚ.- a) b<c))


 amgm = invEq (z/y<x₊≃z<y₊·x _ _ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<b )))
  (isTrans<≡ᵣ _ _ _ (a<c+b⇒a-c<b _ _ _
      (AM-GM-strict z a 1<z ((ℚ.<→ℚ₊ _ _  a<c ))
          (fst α₊) (snd α₊) α<1))
           (cong (_·ᵣ (fst (z ^ℚ (a ℚ.+ fst (ℚ.<→ℚ₊ _ _ a<c))) -ᵣ
       fst (z ^ℚ a))) (rat·ᵣrat _ _)
        ∙ sym (·ᵣAssoc _ _ _)))

opaque
 unfolding _+ᵣ_
 slope-incr'-strict : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ)
   → (a ℚ.< b) → (b<c : b ℚ.< c) →  (a<c : a ℚ.< c) →
   ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<c))
       <ᵣ
   ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ b))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  b<c ))
 slope-incr'-strict z 1<z a b c a<b b<c a<c =
  let w = fst (x'/x<[x'+y']/[x+y]≃[x'+y']/[x+y]<y'/y
                  (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b)) ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)))
                  (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ b<c)) ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ b))))
              (isTrans<≡ᵣ _ _ _
                (slope-incr-strict z 1<z _ _ _ a<b b<c a<c)
                (cong₂ _／ᵣ₊_
                  (diff-split (fst (z ^ℚ a)) (fst (z ^ℚ b)) (fst (z ^ℚ c)))
                  (ℝ₊≡ (cong rat ℚ! ∙ sym (+ᵣ-rat _ _)))))
  in isTrans≡<ᵣ _ _ _
      (cong₂ _／ᵣ₊_
        (diff-split (fst (z ^ℚ a)) (fst (z ^ℚ b)) (fst (z ^ℚ c)))
        ((ℝ₊≡ (cong rat ℚ! ∙ sym (+ᵣ-rat _ _))))) w

opaque
 unfolding _+ᵣ_ -ᵣ_
 slope-incr : (z : ℝ₊) (a b c : ℚ)
   → (a<b : a ℚ.< b) → (b≤c : b ℚ.≤ c) →  (a<c : a ℚ.< c) →
   ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
       ≤ᵣ
   ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))
 slope-incr (z , 0<z) a b c a<b b≤c a<c =
   <→≤ContPos'pred {0}
     {λ z 0<z →
        ((fst ((z , 0<z) ^ℚ b)
        -ᵣ fst ((z , 0<z) ^ℚ a))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))}
      {λ z 0<z →
         ((fst ((z , 0<z) ^ℚ c)
           -ᵣ fst ((z , 0<z) ^ℚ a))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))}
       ((IsContinuousWP∘' _ _ _
       (IsContinuous·ᵣR (fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b)))))
       (contDiagNE₂WP sumR _ _ _
         (⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ b))
            (IsContinuousWP∘' _ _ _ IsContinuous-ᵣ
              ((⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ a)))))))
       (((IsContinuousWP∘' _ _ _
       (IsContinuous·ᵣR (fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<c)))))
       (contDiagNE₂WP sumR _ _ _
         (⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ c))
            (IsContinuousWP∘' _ _ _ IsContinuous-ᵣ
              ((⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ a))))))))
       (ℚ.byTrichotomy 1 w)
         z 0<z

  where

   slope-incr** : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ)
     → (a<b : a ℚ.< b) → (b≤c : b ℚ.≤ c) →  (a<c : a ℚ.< c) →
     ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
         ≤ᵣ
     ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))
   slope-incr** z 1<z a b c a<b =
      flip
        λ a<c → ⊎.rec
           (≡ᵣWeaken≤ᵣ _ _ ∘
             cong
               (λ (b , a<b) →
                 ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)) ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b)))
               ∘ Σ≡Prop {B = λ b → a ℚ.< b} (ℚ.isProp< _))
           (λ b<c → <ᵣWeaken≤ᵣ _ _ $  slope-incr-strict z 1<z a b c a<b b<c a<c)
          ∘ ℚ.≤→≡⊎< b c

   w : ℚ.TrichotomyRec 1
          λ u → (0<u : 0 <ᵣ rat u) → ((fst ((rat u , 0<u) ^ℚ b) -ᵣ fst ((rat u , 0<u) ^ℚ a)) ／ᵣ₊
                      ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b))
                     ≤ᵣ
                     ((fst ((rat u , 0<u) ^ℚ c) -ᵣ fst ((rat u , 0<u) ^ℚ a)) ／ᵣ₊
                      ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a c a<c))
   w .ℚ.TrichotomyRec.lt-case u u<1 0<u =
     subst2 _≤ᵣ_
         (sym (-ᵣ· _ _ ) ∙ cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
            (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_ (sym (cong fst (^ℚ-minus u₊ b)))
                        ((sym (cong fst (^ℚ-minus u₊ a)))))
                        {u = ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) (ℚ.minus-< a b a<b)}
                        (ℚ₊≡ ℚ!))
         (sym (-ᵣ· _ _) ∙ (cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
            (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_
               ((sym (cong fst (^ℚ-minus u₊ c))))
               ((sym (cong fst (^ℚ-minus u₊ a)))))
               {u = ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)}
                 (ℚ₊≡ ℚ!)))
           (-ᵣ≤ᵣ _ _
             (⊎.rec ww'' ww' (ℚ.≤→≡⊎< b c b≤c)))
     where
     u₊ : ℝ₊
     u₊ = (rat u , 0<u)
     1/u₊ : ℝ₊
     1/u₊ = (invℝ₊ (rat u , 0<u))
     1<1/u : 1 <ᵣ (fst 1/u₊)
     1<1/u = isTrans<≡ᵣ _ _ _
        (invEq (z<x/y₊≃y₊·z<x 1 1 (rat u , 0<u)) (isTrans≡<ᵣ _ _ _
            (·IdR _) (<ℚ→<ᵣ _ _ u<1)))
         (·IdLᵣ _)

     ww' : (b ℚ.< c) →   ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- c)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)))
                                    ≤ᵣ
                                ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- b)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) (ℚ.minus-< a b a<b) ))
     ww' b<c = <ᵣWeaken≤ᵣ _ _ $ slope-incr'-strict (invℝ₊ (rat u , 0<u)) 1<1/u (ℚ.- c) (ℚ.- b) (ℚ.- a)
              (ℚ.minus-< _ _ b<c) (ℚ.minus-< _ _ a<b) (ℚ.minus-< _ _ a<c)


     ww'' : (b ≡ c) →   ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- c)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)))
                                   ≤ᵣ
                                ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- b)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) (ℚ.minus-< a b a<b) ))
     ww'' b=c = ≡ᵣWeaken≤ᵣ _ _ (
             cong
               (λ (b , -b<-a) →
                 ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- b))) ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) -b<-a)))
               (Σ≡Prop {B = λ b → (ℚ.- b) ℚ.< (ℚ.- a)} (λ _ → ℚ.isProp< _ _) (sym b=c)))


   w .ℚ.TrichotomyRec.eq-case _ = ≡ᵣWeaken≤ᵣ _ _
             (Rℝ.0LeftAnnihilates' _ _
                 (Rℝ.+InvR' _ _ (cong (fst ∘ (_^ℚ b)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 b)
                   ∙ sym (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 a))))
               ∙ sym (Rℝ.0LeftAnnihilates' _ _
                 (Rℝ.+InvR' _ _ ((cong (fst ∘ (_^ℚ c)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 c)
                   ∙ sym (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 a)))))))
   w .ℚ.TrichotomyRec.gt-case u 1<u 0<u =
     slope-incr** (rat u , 0<u) (<ℚ→<ᵣ _ _ 1<u) a b c a<b b≤c a<c




slope-incr' : (z : ℝ₊) → (a b c : ℚ)
  → (a≤b : a ℚ.≤ b) → (b<c : b ℚ.< c) →  (a<c : a ℚ.< c) →
  ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<c))
      ≤ᵣ
  ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ b))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  b<c ))
slope-incr' z a b c a≤b b<c a<c =
     subst2 _≤ᵣ_
       (sym (-ᵣ· _ _) ∙ cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
          (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_ (sym (cong fst (^ℚ-minus z c)))
                      ((sym (cong fst (^ℚ-minus z a)))))
                      {u = ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)}
                      (ℚ₊≡ ℚ!))
       (sym (-ᵣ· _ _) ∙ (cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
          (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_
             ((sym (cong fst (^ℚ-minus z c))))
             ((sym (cong fst (^ℚ-minus z b)))))
             {u = ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- b) (ℚ.minus-< b c b<c)}
               (ℚ₊≡ ℚ!)))
              ww

 where
 ww : -ᵣ ((fst (invℝ₊ z ^ℚ (ℚ.- a)) -ᵣ fst (invℝ₊ z ^ℚ (ℚ.- c))) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)))
      ≤ᵣ
      -ᵣ ((fst (invℝ₊ z ^ℚ (ℚ.- b)) -ᵣ fst (invℝ₊ z ^ℚ (ℚ.- c))) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- b) (ℚ.minus-< b c b<c)))


 ww = -ᵣ≤ᵣ _ _ (slope-incr (invℝ₊ z) (ℚ.- c) (ℚ.- b) (ℚ.- a)
         (ℚ.minus-< _ _ b<c) (ℚ.minus-≤ _ _ a≤b) (ℚ.minus-< _ _ a<c))


slope-monotone : (z : ℝ₊)  → (a b a' b' : ℚ)
  → (a<b : a ℚ.< b) → (a'<b' : a' ℚ.< b') → (a≤a' : a ℚ.≤ a') →  (b≤b' : b ℚ.≤ b') →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      ≤ᵣ
  ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
slope-monotone z a b a' b' a<b a'<b' a≤a' b≤b' =
  isTrans≤ᵣ _ _ _
    (slope-incr z a b b' a<b b≤b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))
      (slope-incr' z a a' b' a≤a' a'<b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))

opaque
 unfolding -ᵣ_ _+ᵣ_
 slope-monotone＃ : (z : ℝ₊) → (a b a' b' : ℚ)
   → (a＃b : rat a ＃ rat b) → (a'<b' : a' ℚ.< b') → (a≤a' : a ℚ.≤ a') →  (b≤b' : b ℚ.≤ b') →
   ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
     ／ᵣ[ rat b -ᵣ rat a  , invEq (＃Δ _ _) a＃b ])
       ≤ᵣ
   ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
 slope-monotone＃ z a b a' b' (inl a<b) a'<b' a≤a' b≤b' =
   isTrans≡≤ᵣ _ _ _
     (cong ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)) ·ᵣ_)
       (cong₂ invℝ (-ᵣ-rat₂ b a) (toPathP refl)
       ∙ sym (invℝ₊≡invℝ _ _)))
     (slope-monotone z  a b a' b' (<ᵣ→<ℚ _ _ a<b) a'<b' a≤a' b≤b')
 slope-monotone＃ z  a b a' b' (inr b<a) a'<b' a≤a' b≤b' =
   isTrans≡≤ᵣ _ _ _
      w
     (slope-monotone z b a a' b' (<ᵣ→<ℚ _ _ b<a) a'<b'
       (ℚ.isTrans≤ _ _ _
         (ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ b<a)) a≤a')
          (ℚ.isTrans≤ _ _ _ a≤a' (ℚ.<Weaken≤ _ _ a'<b')))

  where
  w : ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)) ／ᵣ[ rat b -ᵣ rat a ,
        invEq (＃Δ (rat b) (rat a)) (inr b<a) ])
       ≡
       ((fst (z ^ℚ a) -ᵣ fst (z ^ℚ b)) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ b a (<ᵣ→<ℚ b a b<a)))
  w = sym (-ᵣ·-ᵣ _ _) ∙
      cong₂ _·ᵣ_
        (-[x-y]≡y-x _ _)
        (-invℝ _ _ ∙ cong₂ invℝ (-[x-y]≡y-x (rat b) (rat a))
          (toPathP refl)
          ∙ cong₂ invℝ (-ᵣ-rat₂ a b) (toPathP refl)
          ∙ sym (invℝ₊≡invℝ _ _))

 slope-monotone＃' : (z : ℝ₊) → (a b a' b' : ℚ)
   → (a<b : a ℚ.< b) → (a'＃b' : rat a' ＃ rat b')  → (a≤a' : a ℚ.≤ a') →  (b≤b' : b ℚ.≤ b') →
   ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<b ))
       ≤ᵣ
   ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
      ／ᵣ[ rat b' -ᵣ rat a'  , invEq (＃Δ _ _) a'＃b' ])
 slope-monotone＃' z a b a' b' a<b (inl a'<b') a≤a' b≤b' =
   isTrans≤≡ᵣ _ _ _
     (slope-monotone z a b a' b' a<b (<ᵣ→<ℚ _ _ a'<b') a≤a' b≤b')
     ((cong ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a')) ·ᵣ_)
      (invℝ₊≡invℝ _ _
      ∙ sym (cong₂ invℝ (-ᵣ-rat₂ b' a') (toPathP refl)))))
 slope-monotone＃' z a b a' b' a<b (inr b'<a') a≤a' b≤b' =
  isTrans≤≡ᵣ _ _ _
    ((slope-monotone z a b b' a' a<b (<ᵣ→<ℚ _ _ b'<a')
       (ℚ.isTrans≤ _ _ _ (ℚ.<Weaken≤ _ _ a<b) b≤b')
       (ℚ.isTrans≤ _ _ _ b≤b' ((ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ b'<a'))))))
    (sym w)


  where
  w : ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a')) ／ᵣ[ rat b' -ᵣ rat a' ,
        invEq (＃Δ (rat b') (rat a')) (inr b'<a') ])
       ≡
       ((fst (z ^ℚ a') -ᵣ fst (z ^ℚ b')) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ b' a' (<ᵣ→<ℚ b' a' b'<a')))
  w = sym (-ᵣ·-ᵣ _ _) ∙
      cong₂ _·ᵣ_
        (-[x-y]≡y-x _ _)
        (-invℝ _ _ ∙ cong₂ invℝ (-[x-y]≡y-x (rat b') (rat a'))
          (toPathP refl)
          ∙ cong₂ invℝ (-ᵣ-rat₂ a' b') (toPathP refl)
          ∙ sym (invℝ₊≡invℝ _ _))




slope-monotone-strict : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b a' b' : ℚ)
  → (a<b : a ℚ.< b) → (a'<b' : a' ℚ.< b') → (a≤a' : a ℚ.≤ a') →  (b<b' : b ℚ.< b') →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      <ᵣ
  ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
slope-monotone-strict z 1<z a b a' b' a<b a'<b' a≤a' b<b' =
  isTrans<≤ᵣ _ _ _
    (slope-incr-strict z 1<z a b b' a<b b<b' (ℚ.isTrans< _ _ _ a<b b<b'))
      (slope-incr' z a a' b' a≤a' a'<b' (ℚ.isTrans< _ _ _ a<b b<b'))

slope-monotone-strict' : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b a' b' : ℚ)
  → (a<b : a ℚ.< b) → (a'<b' : a' ℚ.< b') → (a<a' : a ℚ.< a') →  (b≤b' : b ℚ.≤ b') →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      <ᵣ
  ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
slope-monotone-strict' z 1<z a b a' b' a<b a'<b' a<a' b≤b' =
  isTrans≤<ᵣ _ _ _
    (slope-incr z a b b' a<b b≤b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))
      (slope-incr'-strict z 1<z a a' b' a<a' a'<b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))

opaque
 unfolding invℝ
 bernoulli's-ineq-^ℚ-r<1 : ∀ x r → 1 <ᵣ fst x → 0 ℚ.< r → r ℚ.< 1 → fst (x ^ℚ r) <ᵣ 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)
 bernoulli's-ineq-^ℚ-r<1 x r 1<x 0<r r<1 =
   isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ 1 _
       ((fst (z/y<x₊≃z<y₊·x _ _ _)
             (slope-incr-strict x 1<x 0 r 1
                0<r r<1 ℚ.decℚ<?))))
              (+ᵣComm _ _ ∙ cong (1 +ᵣ_)
                (cong₂ _·ᵣ_ (cong rat (ℚ.+IdR _))
                  (Rℝ.·IdR' _ _
                   (cong (fst ∘ invℝ₊) (ℝ₊≡ (cong rat (ℚ.+IdR _)))
                   ∙ cong fst invℝ₊1)
                   ∙ cong₂ (_-ᵣ_) (cong fst (^ℚ-1 x)) (cong fst (1^ℚ≡1 0)))))

 bernoulli's-ineq-^ℚ : ∀ x r → 1 <ᵣ fst x
  → 1 ℚ.< r → 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)  <ᵣ fst (x ^ℚ r)
 bernoulli's-ineq-^ℚ x r 1<x 1<r =
   isTrans≡<ᵣ _ _ _
        (cong (1 +ᵣ_) (cong₂ _·ᵣ_
          (sym (cong rat (ℚ.+IdR _)))
          (cong₂ (_-ᵣ_) (sym (cong fst (^ℚ-1 x))) (cong fst (sym (1^ℚ≡1 0)))
           ∙ sym (Rℝ.·IdR' _ _
             (cong (fst ∘ invℝ₊) (ℝ₊≡ (cong rat (ℚ.+IdR _)))
             ∙ cong fst invℝ₊1))))
          ∙ +ᵣComm _ _)
        (a<b-c⇒a+c<b _ _ 1 (fst (z<x/y₊≃y₊·z<x _ _ _)
         (slope-incr-strict x 1<x 0 1 r ℚ.decℚ<?
          1<r (ℚ.isTrans< _ 1 _ ℚ.decℚ<? 1<r))))


power-slope-Δ : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b : ℚ) → a ℚ.< b →
   (Δ : ℚ₊) →
  fst (z ^ℚ b) -ᵣ fst (z ^ℚ a) <ᵣ
   fst (z ^ℚ (b ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ (a ℚ.+ fst Δ))
power-slope-Δ z 1<z a b a<b Δ =
  isTrans<≡ᵣ _ _ _
    (isTrans≡<ᵣ _ _ _
       (sym (·IdLᵣ _))
       (<ᵣ-·ᵣo _ _ (_ ,
         x<y→0<y-x _ _ (^ℚ-StrictMonotoneR 1<z _ _ a<b ))
        (1<^ℚ z Δ 1<z)  ))
    (·DistL- (fst (z ^ℚ (fst Δ))) _ _ ∙
      cong₂ _-ᵣ_
       (·ᵣComm _ _ ∙ cong fst (^ℚ-+ z _ _))
       (·ᵣComm _ _ ∙ cong fst (^ℚ-+ z _ _)))


fromNatℝ≡fromNatℚ : ∀ n → fromNat (suc n) ≡ ℚ₊→ℝ₊ (fromNat (suc n))
fromNatℝ≡fromNatℚ n = ℝ₊≡ refl

bound : ℝ₊ → ℚ₊ → ℝ
bound z B = ((fst (z ^ℚ (2 ℚ.· (fst B))) -ᵣ fst (z ^ℚ (fst B))) ·ᵣ
   rat (fst (invℚ₊ B)))

bound1≡0 : ∀ q → bound 1 q ≡ 0
bound1≡0 q = Rℝ.0LeftAnnihilates' _ _
  (Rℝ.+InvR' _ _ ((cong fst (1^ℚ≡1 _) ∙ cong fst (sym (1^ℚ≡1 _)))))

2x-x≡x : ∀ q → (2 ℚ.· q) ℚ.- q ≡ q
2x-x≡x q = cong ((2 ℚ.· q) ℚ.+_)
            (cong (ℚ.-_) (sym (ℚ.·IdL _)))
              ∙ sym (Rℚ.·DistL- 2 1 q)
              ∙ ℚ.·IdL _

module _ (Z N : ℕ) where

 N<2N : fromNat (suc N) ℚ.< 2 ℚ.· fromNat (suc N)
 N<2N = (<ℤ→<ℚ _ _
         (ℤ.ℕ<→pos-<-pos _ _
           (subst (suc N ℕ.<_)
             (cong (suc N ℕ.+_) (sym (ℕ.+-zero (suc N))))
             (ℕ.<SumRight {n = suc N} {k = N}))))

 N<2N' : fromNat (suc N) ℚ.< fromNat (2 ℕ.· suc N)
 N<2N' = subst (fromNat (suc N) ℚ.<_) (ℚ.ℕ·→ℚ· _ _) N<2N



 1<2+Z = (<ℚ→<ᵣ 1 (fromNat (2 ℕ.+ Z)) (<ℤ→<ℚ _ _ (ℤ.ℕ<→pos-<-pos _ _
        (ℕ.≤-k+ {k = 2} ℕ.zero-≤))))

 baseℚ₊ : ℚ₊
 baseℚ₊ = fromNat (2 ℕ.+ Z)

 baseℚ : ℚ
 baseℚ = fst baseℚ₊

 invBaseℚ₊ : ℚ₊
 invBaseℚ₊ = invℚ₊ baseℚ₊

 invBaseℚ : ℚ
 invBaseℚ = fst invBaseℚ₊

 baseℝ₊ : ℝ₊
 baseℝ₊ = fromNat (2 ℕ.+ Z)

 boundℚ : ℚ₊
 boundℚ = ℚ.<→ℚ₊ _ _
    (<ᵣ→<ℚ (baseℚ ℚ^ⁿ suc N)
           (baseℚ ℚ^ⁿ (2 ℕ.· suc N))
      (subst2 _<ᵣ_
        (^ⁿ-ℚ^ⁿ (suc N) baseℚ)
        (cong (fst ∘ (baseℝ₊ ^ℚ_))
          (ℚ.ℕ·→ℚ· _ _)
         ∙ ^ⁿ-ℚ^ⁿ (2 ℕ.· suc N) baseℚ)
       (^ℚ-StrictMonotoneR {baseℝ₊}
       1<2+Z
       (fromNat (suc N)) (2 ℚ.· fromNat (suc N)) N<2N)))
        ·₊
       (invℚ₊ (fromNat (suc N)))

 boundℚInv : ℚ₊
 boundℚInv = ℚ.<→ℚ₊ _ _
    (<ᵣ→<ℚ (invBaseℚ ℚ^ⁿ (2 ℕ.· suc N))
           (invBaseℚ ℚ^ⁿ (suc N))
      (subst2 _<ᵣ_
        (^ⁿ-ℚ^ⁿ (2 ℕ.· suc N) invBaseℚ)
        (^ⁿ-ℚ^ⁿ (suc N) invBaseℚ)
        (^ℚ-StrictMonotoneR' {ℚ₊→ℝ₊ invBaseℚ₊}
           (<ℚ→<ᵣ _ _ (fst (ℚ.invℚ₊-<-invℚ₊ 1 baseℚ₊)
            (<ℤ→<ℚ _ _ ((ℤ.ℕ<→pos-<-pos _ _
               (ℕ.≤-k+ {k = 2} ℕ.zero-≤))))))
           (fromNat (suc N)) (fromNat (2 ℕ.· suc N))
              (subst (λ n → fromNat (n) ℚ.< fromNat (2 ℕ.· suc N))
                (ℕ.·-identityˡ _)
                (<ℤ→<ℚ _ _
                  (ℤ.ℕ<→pos-<-pos _ _
                    (ℕ.<-·sk {1} {2} {N} ℕ.≤-refl)))))))
        ·₊
       (invℚ₊ (fromNat (suc N)))


 hlp : fst
      (invℝ₊
       (ℚ₊→ℝ₊
        (ℚ.<→ℚ₊ [ pos (suc N) / 1+ 0 ]
         [ pos (suc (N ℕ.+ suc (N ℕ.+ zero))) / 1+ 0 ] N<2N')))
      ≡ rat (fst (invℚ₊ ([ pos (suc N) , (1+ 0) ] , ℚ.0<pos N (1+ 0))))
 hlp = (invℝ₊-rat _ ∙
            cong (rat ∘ fst ∘ invℚ₊)
              (ℚ₊≡ (cong (ℚ._- (fromNat (suc N))) (sym (ℚ.ℕ·→ℚ· _ _))
               ∙ 2x-x≡x (fromNat (suc N)))))

 hlp2 : invℝ₊ baseℝ₊ ≡ ℚ₊→ℝ₊ invBaseℚ₊
 hlp2 = ℝ₊≡ (cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _)
  ∙ invℝ₊-rat (fromNat (2 ℕ.+ Z)))

 opaque
  boundℚInv<boundℚ : fst (boundℚInv) ℚ.< fst (boundℚ)
  boundℚInv<boundℚ =
    <ᵣ→<ℚ _ _
      (subst2 _<ᵣ_
        (cong₂ _·ᵣ_
           (cong₂ _-ᵣ_
             (cong fst (^ℚ-minus' _ _ ∙ cong (_^ℚ fromNat (suc N))
                  hlp2)
              ∙ ^ⁿ-ℚ^ⁿ (suc N) invBaseℚ)
             (cong fst (^ℚ-minus' _ _ ∙ cong (_^ℚ fromNat (2 ℕ.· suc N))
                  hlp2) ∙ ^ⁿ-ℚ^ⁿ (2 ℕ.· suc N) invBaseℚ))
           (cong (fst ∘ invℝ₊ ∘ ℚ₊→ℝ₊)
             (ℚ₊≡ ℚ!)
             ∙ hlp)
          ∙ ℚℝ!)
        (cong₂ _·ᵣ_
           (cong₂ _-ᵣ_
             (^ⁿ-ℚ^ⁿ (2 ℕ.· suc N) baseℚ)
             (^ⁿ-ℚ^ⁿ (suc N) baseℚ))
           hlp
          ∙ ℚℝ!)
        (slope-monotone-strict baseℝ₊
           1<2+Z
          (ℚ.- (fromNat (2 ℕ.· suc N))) (ℚ.- (fromNat (suc N)))
          (fromNat (suc N)) (fromNat (2 ℕ.· suc N))
          (ℚ.minus-< _ _ N<2N')
          N<2N'
          (ℚ.isTrans≤ _ 0 _  (ℚ.neg≤pos _ _) (ℚ.0≤pos _ _))
          (ℚ.isTrans≤< _ 0 _  (ℚ.neg≤pos _ _) (ℚ.0<pos _ _))))

1<boundℚ : ∀ Z n → 1 ℚ.< fst (boundℚ Z n)
1<boundℚ Z n = w

 where
 sn₊ : ℚ₊
 sn₊ = fromNat (suc n)

 w : 1 ℚ.< (((fromNat (2 ℕ.+ Z)) ℚ^ⁿ (2 ℕ.· suc n)) ℚ.- ((fromNat (2 ℕ.+ Z)) ℚ^ⁿ suc n))
              ℚ.· fst (invℚ₊ sn₊)
 w = subst (1 ℚ.<_)
    (ℚ.·Assoc _ _ _
       ∙ cong (ℚ._· fst (invℚ₊ sn₊))
         (ℚ.·DistR+ (fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n) (-1) (fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n)
           ∙ cong₂ (ℚ._+_)
           (ℚExponentiation.·-of-^-is-^-of-+ (fromNat (2 ℕ.+ Z)) (suc n) (suc n) ∙ cong {x = (suc n) ℕ.+ (suc n)} ((fromNat (2 ℕ.+ Z)) ℚ^ⁿ_)
             (cong (λ n' → suc (n ℕ.+ suc n')) (sym (ℕ.+-zero n))))
             (sym (ℚ.-·- (ℚ.- 1) _) ∙ ℚ.·IdL _)
             ) )
    (ℚ.≤<Monotone·-onPos 1 ((fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n) ℚ.- 1)
       1 _
       (ℚ.≤-+o 2 ((fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n)) -1
         (ℚ.isTrans≤ _ (fromNat (2 ℕ.+ Z)) _ (≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos 2 (2 ℕ.+ Z)
          (ℕ.suc-≤-suc (ℕ.suc-≤-suc (ℕ.zero-≤ {Z})))))
          (subst (fromNat (2 ℕ.+ Z) ℚ.≤_) (sym (ℚ.fromNat-^ (2 ℕ.+ Z) (suc n)))
            (≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
              (subst (ℕ._≤ ((2 ℕ.+ Z) ^ suc n))
                (cong (suc ∘ suc) (·-identityʳ Z))
                 (ℕ.^-monotone (2 ℕ.+ Z) 0 n (ℕ.zero-≤ {n}))))))))
       (subst (ℚ._<
          (fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n) ℚ.· fst (invℚ₊ sn₊))
            (ℚ.x·invℚ₊[x] sn₊)
              (ℚ.<-·o _ _ (fst (invℚ₊ sn₊))
                (snd (invℚ₊ sn₊))
                 (subst (fst sn₊ ℚ.<_)
                   (sym (ℚ.fromNat-^ (2 ℕ.+ Z) (suc n)))
                   (<ℤ→<ℚ _ _ (ℤ.ℕ<→pos-<-pos _ _ (ℕ.sn<ssm^sn n Z))))))
       (ℚ.decℚ<? {0} {1}) (ℚ.decℚ≤? {0} {1}))

-- Previous location: pred0< and pred1< were defined here.


opaque
 unfolding -ᵣ_ _+ᵣ_
 contBound : ∀ B → IsContinuousWithPred pred0< (curry (flip bound B))
 contBound B =
   IsContinuousWP∘ ⊤Pred _ _ _ _
     (AsContinuousWithPred _ _ (IsContinuous·ᵣR (rat (fst (invℚ₊ B)))))
     (contDiagNE₂WP sumR _
        _ _
          (IsContinuous^ℚ _)
           (IsContinuousWP∘ pred0< _ _ _
             (curry (snd ∘ (_^ℚ fst B))) (AsContinuousWithPred _ _  IsContinuous-ᵣ)
               (IsContinuous^ℚ _)))




-- module ExpSlopeBound (z : ℝ₊) (1<z : 1 <ᵣ fst z)  where
--  module _ (B : ℚ₊) where



--   ineqStrict : ∀ x y → y ℚ.≤ fst B → x ℚ.< y →
--            (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) <ᵣ
--               bound z B ·ᵣ rat (y ℚ.- x)
--   ineqStrict x y y≤B x<y =
--        isTrans<≡ᵣ _ _ _
--          (fst (z/y<x₊≃z<y₊·x _ _ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ x<y)))
--            (isTrans≤<ᵣ _ _ _
--              (slope-incr' z x x' y
--                (ℚ.≤max _ _) x'<y x<y)
--              (isTrans<≤ᵣ _ _ _
--                (<ᵣ-·ᵣo _ _ (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ x' y x'<y)))
--                 (power-slope-Δ z 1<z x' y x'<y
--                (ℚ.<→ℚ₊ _ _ (ℚ.isTrans<≤  _ _ _ x'<y y≤B))))
--                (isTrans≡≤ᵣ _ _ _
--                  (cong₂ _／ᵣ₊_ (cong (λ v →
--                         fst (z ^ℚ (y ℚ.+ (fst B ℚ.- x'))) -ᵣ fst (z ^ℚ v))
--                        lem--05)
--                    (ℝ₊≡ (cong rat lem--078)))
--                  (isTrans≤≡ᵣ _ _ _
--                     (slope-incr z
--                       (fst B) (y ℚ.+ (fst B ℚ.- x')) (2 ℚ.· (fst B))
--                        (subst2 (ℚ._<_) (ℚ.+IdL (fst B))
--                          (sym (ℚ.+Assoc _ _ _)
--                          ∙ cong (y ℚ.+_) (ℚ.+Comm _ _))
--                          (ℚ.<-+o 0 _ (fst B) (ℚ.-< _ _ x'<y)))
--                        (subst2 ℚ._≤_
--                          ( sym (ℚ.+Assoc _ _ _)
--                          ∙ cong (y ℚ.+_) (ℚ.+Comm _ _)) (ℚ.x+x≡2x (fst B))
--                          (ℚ.≤-+o _ _ _ y-x'≤B))
--                        (subst (ℚ._< (2 ℚ.· fst B)) (ℚ.·IdL (fst B))
--                          (ℚ.<-·o _ _ (fst B) (ℚ.0<ℚ₊ B)
--                            (ℚ.decℚ<? {1} {2})))) ww)))))
--          (·ᵣComm _ _)

--     where
--     x' = ℚ.max x (y ℚ.- fst B)

--     x'<y : x' ℚ.< y
--     x'<y = ℚ.max< _ _ _ x<y (ℚ.<-ℚ₊' y y B (ℚ.isRefl≤ y ) )

--     y-x'≤B : y ℚ.- x' ℚ.≤ fst B
--     y-x'≤B = subst (y ℚ.- x' ℚ.≤_) lem--079
--      (ℚ.≤-o+ _ _ y
--      (ℚ.minus-≤ (y ℚ.- fst B) x' (ℚ.≤max' x (y ℚ.- fst B))))

--     ww' = (ℚ.<→ℚ₊ (fst B) (2 ℚ.· fst B)
--              (subst (ℚ._< 2 ℚ.· fst B) (ℚ.·IdL (fst B))
--               (ℚ.<-·o 1 2 (fst B) (ℚ.0<ℚ₊ B) ℚ.decℚ<?)))

--     ww : ((fst (z ^ℚ (2 ℚ.· fst B)) -ᵣ fst (z ^ℚ fst B)) ／ᵣ₊
--             (ℚ₊→ℝ₊ ww'))
--            ≡ ((fst (z ^ℚ (2 ℚ.· (fst B))) -ᵣ fst (z ^ℚ (fst B))) ·ᵣ
--      rat (fst (invℚ₊ B)))
--     ww =
--      cong ((fst (z ^ℚ (2 ℚ.· fst B)) -ᵣ fst (z ^ℚ fst B)) ·ᵣ_)
--        (invℝ'-rat _ (snd ww') (snd (ℚ₊→ℝ₊ ww')) ∙
--          cong (rat ∘ fst ∘ invℚ₊) (ℚ₊≡
--           (cong (ℚ._- (fst B)) (sym (ℚ.x+x≡2x (fst B)))
--            ∙ sym (lem--034 {fst B}))) )


--   ineqStrictInv : ∀ x y → (ℚ.- (fst B)) ℚ.≤ x → x ℚ.< y →
--                 (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat (y ℚ.- x) <ᵣ  (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
--   ineqStrictInv x y -B≤x x<y =
--      isTrans≡<ᵣ _ _ _ (·ᵣComm _ _)
--        (fst (z<x/y₊≃y₊·z<x _ _ _) w)
--     where

--     -2B<-B = (ℚ.minus-< _ _ (subst (ℚ._< 2 ℚ.· (fst B))
--                 (ℚ.·IdL (fst B)) (ℚ.<-·o 1 2 (fst B) (ℚ.0<ℚ₊ B)
--                   ℚ.decℚ<?)))

--     w : (-ᵣ (bound (invℝ₊ z) B))  <ᵣ  ((fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  x<y ))
--     w = isTrans≡<ᵣ _ _ _ (sym (-ᵣ· _ _) ∙
--        cong₂ _·ᵣ_ (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_
--                     (cong fst (cong (invℝ₊ z ^ℚ_) (sym (ℚ.-Invol _)) ∙ sym (^ℚ-minus _ _)))
--                     (cong fst (cong (invℝ₊ z ^ℚ_) (sym (ℚ.-Invol _)) ∙ sym (^ℚ-minus _ _))))
--                   (sym (invℝ₊-rat B)
--                    ∙ cong (fst ∘ invℝ₊ ∘ ℚ₊→ℝ₊)
--                      (ℚ₊≡ ((sym (ℚ.·IdL _) ∙ ℚ.·DistR+ 2 -1 (fst B))
--                       ∙ cong (ℚ._+ (ℚ.- fst B)) (sym (ℚ.-Invol _))
--                       ∙ ℚ.+Comm _ _))) )
--       (slope-monotone-strict z 1<z
--         (ℚ.- (2 ℚ.· fst B)) (ℚ.- (fst B))
--           x y -2B<-B x<y
--             (ℚ.isTrans≤ _ _ _ (ℚ.<Weaken≤ _ _ -2B<-B) -B≤x)
--             (ℚ.isTrans≤< _ _ _ -B≤x x<y))

--   ineq : ∀ x y → y ℚ.≤ fst B → x ℚ.≤ y →
--            (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
--               bound z B ·ᵣ rat (y ℚ.- x)
--   ineq x y y≤B = ⊎.rec
--     (λ x≡y → ≡ᵣWeaken≤ᵣ _ _
--       (𝐑'.+InvR' _ _ (cong (fst ∘ z ^ℚ_) (sym x≡y))
--         ∙∙ sym (𝐑'.0RightAnnihilates (bound z B)) ∙∙
--         cong (bound z B ·ᵣ_) (cong rat (sym (𝐐'.+InvR' _ _ (sym x≡y))))))
--     (<ᵣWeaken≤ᵣ _ _ ∘ ineqStrict x y y≤B )
--     ∘ ℚ.≤→≡⊎< x y



--   ineqInv : ∀ x y → (ℚ.- (fst B)) ℚ.≤ x → x ℚ.≤ y →
--                 (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat (y ℚ.- x) ≤ᵣ  (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
--   ineqInv x y -B≤x =
--     ⊎.rec
--       (λ x≡y → ≡ᵣWeaken≤ᵣ _ _
--          (cong (-ᵣ bound (invℝ₊ z) B ·ᵣ_) (cong rat (𝐐'.+InvR' y x (sym x≡y))) ∙∙
--            𝐑'.0RightAnnihilates (-ᵣ bound (invℝ₊ z) B) ∙∙
--             (sym (𝐑'.+InvR' (fst (z ^ℚ y)) (fst (z ^ℚ x))
--              (cong (fst ∘ (z ^ℚ_)) (sym x≡y))) )))
--       (<ᵣWeaken≤ᵣ _ _ ∘ ineqStrictInv x y -B≤x)
--      ∘ ℚ.≤→≡⊎< x y

--   opaque
--    unfolding -ᵣ_ absᵣ
--    ineq-abs : ∀ x y → x ℚ.≤ fst B → y ℚ.≤ fst B →
--             absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
--                bound z B ·ᵣ rat (abs' (y ℚ.- x))
--    ineq-abs x y x≤B y≤B = w (ℚ.≡⊎# x y)

--     where
--     w : (x ≡ y) ⊎ (x ℚ.# y) → absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
--                bound z B ·ᵣ rat (abs' (y ℚ.- x))
--     w (inl x≡y) =
--       ≡ᵣWeaken≤ᵣ _ _
--        (cong absᵣ (𝐑'.+InvR' _ _ (cong (fst ∘ z ^ℚ_) (sym x≡y)))
--          ∙∙ sym (𝐑'.0RightAnnihilates (bound z B)) ∙∙
--          cong (bound z B ·ᵣ_)
--           (cong (rat ∘ abs') (sym (𝐐'.+InvR' _ _ (sym x≡y))))
--           )
--     w (inr (inl x<y)) = <ᵣWeaken≤ᵣ _ _ (isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
--           (absᵣNonNeg _ (x≤y→0≤y-x _ _ (^ℚ-MonotoneR x y
--              (ℚ.<Weaken≤ _ _ x<y)
--             (<ᵣWeaken≤ᵣ _ _ 1<z))))
--            (ineqStrict x y y≤B x<y))
--          (cong (bound z B ·ᵣ_)
--           (cong rat (sym (ℚO.0<→abs≡id _ (ℚ.-< _ _ x<y)) ∙ abs'≡abs _))))
--     w (inr (inr y<x)) =
--       <ᵣWeaken≤ᵣ _ _ (isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
--           (minusComm-absᵣ _ _ ∙
--            absᵣPos _ (x<y→0<y-x _ _ (^ℚ-StrictMonotoneR 1<z y x y<x)))
--            (ineqStrict y x x≤B y<x))
--          (cong (bound z B ·ᵣ_)
--           (cong rat ((sym (ℚ.-[x-y]≡y-x _ _) ∙ sym (ℚO.<0→abs≡- _
--             (subst ((y ℚ.- x) ℚ.<_)
--               (ℚ.+InvR _) (ℚ.<-+o _ _ (ℚ.- x) y<x)))) ∙ abs'≡abs _))))

--   ineqInv-abs : ∀ x y → (ℚ.- (fst B)) ℚ.≤ x → (ℚ.- (fst B)) ℚ.≤ y →
--                 (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat (abs (y ℚ.- x)) ≤ᵣ
--                     absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
--   ineqInv-abs = ℚ.elimBy≤ (λ x y X u v →
--     subst2 (λ a b → (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat a ≤ᵣ b)
--                     (ℚO.abs-Comm _ _) (minusComm-absᵣ _ _) (X v u))
--      λ x y x≤y x≤ _ →
--         subst2 (λ a b → (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat a ≤ᵣ b)
--           (sym (ℚO.0≤→abs≡id _ (ℚ.-≤ _ _ x≤y)))
--            (sym (absᵣNonNeg _ (x≤y→0≤y-x _ _ (^ℚ-MonotoneR _ _ x≤y (<ᵣWeaken≤ᵣ _ _ 1<z) ))))
--            (ineqInv x y x≤ x≤y)
