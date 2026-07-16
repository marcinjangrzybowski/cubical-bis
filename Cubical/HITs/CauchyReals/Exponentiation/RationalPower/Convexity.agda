module Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Convexity where

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


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting
open import Cubical.HITs.CauchyReals.Foundation.Order.Base public using (pred0< ; pred1<)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base hiding (pred0< ; pred1<)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core

private
  opaque
    invℝ₊-rat-opaque : ∀ q →
      fst (invℝ₊ (ℚ₊→ℝ₊ q)) ≡ rat (fst (invℚ₊ q))
    invℝ₊-rat-opaque q = invℝ₊-rat q

    invℝ₊-rat-involutive-opaque : ∀ (q : ℚ₊) →
      fst (invℝ₊ (ℚ₊→ℝ₊ (invℚ₊ q))) ≡ rat (fst q)
    invℝ₊-rat-involutive-opaque q =
      invℝ₊-rat-opaque (invℚ₊ q)
      ∙ cong rat (ℚ.invℚ₊-invol q)

fromNatℝ+ : ∀ {x y z} →
    x ℕ.+ y ≡ z →
    HasFromNat.fromNat fromNatℝ x +ᵣ HasFromNat.fromNat fromNatℝ y
      ≡ HasFromNat.fromNat fromNatℝ z
fromNatℝ+ {x} {y} p =
  fromNat+ᵣ x y
  ∙ cong (λ n → HasFromNat.fromNat fromNatℝ n {{tt}}) p

square-minus-one-expanded : ∀ t →
  (t -ᵣ 1) ·ᵣ (t -ᵣ 1)
    ≡ (t ·ᵣ t +ᵣ 1 ·ᵣ 1) +ᵣ -ᵣ (t ·ᵣ 1 +ᵣ t ·ᵣ 1)
square-minus-one-expanded t = ℝ!

AM-GM₂ : ∀ z → 1 <ᵣ fst z → ∀ x (Δ : ℚ₊) →
          fst (2 ₊·ᵣ (z ^ℚ x)) <ᵣ
            fst ((z ^ℚ (x ℚ.- fst Δ)) ₊+ᵣ (z ^ℚ (x ℚ.+ fst Δ)))
AM-GM₂ z 1<z x Δ = isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
       (cong (2 ·ᵣ_) (cong (fst ∘ z ^ℚ_) centerSplit
          ∙ sym (cong fst (^ℚ-+ z lowerExponent d)))
          ∙ ·ᵣComm 2 (fst lowerPower ·ᵣ fst a)
          ∙ sym (·ᵣAssoc (fst lowerPower) (fst a) 2))
       (fst (z<x≃y₊·z<y₊·x _ _ lowerPower) (isTrans≡<ᵣ _ _ _
         (cong (fst a ·ᵣ_)
           (sym (fromNatℝ+ {x = 1} {y = 1} {z = 2} refl))
           ∙ ·DistL+ (fst a) 1 1)
       (invEq (x<y≃0<y-x _ _)
      $ isTrans<≡ᵣ _ _ _ (ℝ₊· (fst a -ᵣ 1 , w') (fst a -ᵣ 1 , w'))
       (square-minus-one-expanded (fst a))))))
        (·DistL+ (fst lowerPower) (fst a ·ᵣ fst a) (1 ·ᵣ 1)
          ∙ +ᵣComm _ _ ∙
          cong₂ _+ᵣ_
          (cong (fst lowerPower ·ᵣ_)
              (sym (rat·ᵣrat 1 1)) ∙ ·IdR (fst lowerPower))
              (cong (fst lowerPower ·ᵣ_)
                (cong fst (^ℚ-+ z d d)) ∙
                  (cong fst (^ℚ-+ z lowerExponent (d ℚ.+ d))) ∙
                    cong (fst ∘ z ^ℚ_)
                      shiftedSplit))


 where
 d : ℚ
 d = fst Δ

 lowerExponent : ℚ
 lowerExponent = x ℚ.- d

 centerSplit : x ≡ lowerExponent ℚ.+ d
 centerSplit = ℚ!

 shiftedSplit : lowerExponent ℚ.+ (d ℚ.+ d) ≡ x ℚ.+ d
 shiftedSplit = ℚ!

 lowerPower : ℝ₊
 lowerPower = z ^ℚ lowerExponent

 a : ℝ₊
 a = z ^ℚ d

 w' : 0 <ᵣ fst a -ᵣ 1
 w' = fst (x<y≃0<y-x _ _) (1<^ℚ z Δ 1<z)

invℚ₊-fromNat : ∀ m → fst (invℚ₊ (fromNat (suc m))) ≡ [ pos 1 / 1+ m ]
invℚ₊-fromNat = ℚ.invℚ₊-fromNat

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
 x-suc n = sym (ℚ.+Assoc x₀ (fromNat n ℚ.· fst s) (fst s))
     ∙ cong (x₀ ℚ.+_) (
       cong ((fromNat n ℚ.· fst s) ℚ.+_)
         (sym (ℚ.·IdL (fst s))) ∙∙
       sym (ℚ.·DistR+ (fromNat n) 1 (fst s)) ∙∙
       cong (ℚ._· fst s)
         (ℚ.+Comm (fromNat n) 1 ∙ ℚ.ℕ+→ℚ+ 1 n))

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
      (ℚ.·IdL (fst s)))
    (isTrans<≡ᵣ _ _ _ (invEq (z<x/y₊≃y₊·z<x _ _ 2)
   (AM-GM₂ b 1<b (x₀ ℚ.+ fst s) s))
    (cong (_·ᵣ fst (invℝ₊ 2))
       (cong₂ _+ᵣ_
          (cong (fst ∘ b ^ℚ_) cancelStep
          ∙ sym (Rℝ.plusMinus _ _)
          ∙ cong (_-ᵣ fst (b ^ℚ x₀))
              (Cubical.HITs.CauchyReals.Algebra.Multiplication.x+x≡2x _ ∙ ·ᵣComm _ _))
          (cong (fst ∘ b ^ℚ_) doubleStep)
       ∙ sym (+ᵣAssoc _ _ _))
      ∙ ·DistR+ (fst (b ^ℚ x₀) ·ᵣ 2) _ _
      ∙ cong₂ _+ᵣ_ ([x·yᵣ]/₊y _ _)
          (·ᵣComm _ _
          ∙ cong₂ _·ᵣ_ (invℝ₊-rat 2) (+ᵣComm _ _))))

  where
  cancelStep : (x₀ ℚ.+ fst s) ℚ.- fst s ≡ x₀
  cancelStep = ℚ!

  doubleStep : (x₀ ℚ.+ fst s) ℚ.+ fst s ≡ x 2
  doubleStep =
    sym (ℚ.+Assoc x₀ (fst s) (fst s))
    ∙ cong (x₀ ℚ.+_) (ℚ.x+x≡2x (fst s))

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
{-
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
-}
  convSteps (suc N) (suc n) (zero , 2+n=1+N) =
    subst2 _<ᵣ_ leftPath rightPath boundary
    where
    power : ℕ → ℝ
    power k = fst (b ^ℚ x k)

    base : ℝ
    base = fst (b ^ℚ x₀)

    rightAt : ℕ → ℝ
    rightAt k =
      base +ᵣ
      rat (fst (fromNat (suc (predℕ k)) ·₊
        invℚ₊ (fromNat (suc (suc N))))) ·ᵣ
      (power (suc (suc N)) -ᵣ base)

    leftPath : power (suc N) ≡ power (suc (suc n))
    leftPath = cong power (sym 2+n=1+N)

    rightPath : rightAt (suc N) ≡ rightAt (suc (suc n))
    rightPath = cong rightAt (sym 2+n=1+N)

    firstDifference : ℝ
    firstDifference = power (suc N) -ᵣ base

    secondDifference : ℝ
    secondDifference = power (suc (suc N)) -ᵣ base

    firstRational : ℚ₊
    firstRational = fromNat (suc N)

    secondRational : ℚ₊
    secondRational = fromNat (suc (suc N))

    firstReciprocal : ℝ₊
    firstReciprocal = ℚ₊→ℝ₊ (invℚ₊ firstRational)

    secondSlope : ℝ
    secondSlope =
      rat (fst (invℚ₊ secondRational)) ·ᵣ
      secondDifference

    dividedBound : ℝ
    dividedBound = secondSlope ·ᵣ fst (invℝ₊ firstReciprocal)

    strictStep : power (suc N) <ᵣ dividedBound +ᵣ base
    strictStep =
      a-b<c⇒a<c+b (power (suc N)) base dividedBound
        (invEq
          (z<x/y₊≃y₊·z<x secondSlope firstDifference firstReciprocal)
          (convStep N))

    firstInverse : ℝ
    firstInverse = fst (invℝ₊ firstReciprocal)

    secondReciprocal : ℝ
    secondReciprocal = rat (fst (invℚ₊ secondRational))

    rationalCoefficient : ℚ
    rationalCoefficient = fst (firstRational ·₊ invℚ₊ secondRational)

    reassociateProduct :
      dividedBound ≡
      (secondReciprocal ·ᵣ firstInverse) ·ᵣ secondDifference
    reassociateProduct =
      sym (·ᵣAssoc secondReciprocal secondDifference firstInverse)
      ∙ cong (secondReciprocal ·ᵣ_)
          (·ᵣComm secondDifference firstInverse)
      ∙ ·ᵣAssoc secondReciprocal firstInverse secondDifference

    invertFirstReciprocal :
      fst (invℝ₊ (ℚ₊→ℝ₊ (invℚ₊ firstRational))) ≡
      rat (fst firstRational)
    invertFirstReciprocal =
      invℝ₊-rat-involutive-opaque firstRational

    normalizeCoefficient :
      secondReciprocal ·ᵣ firstInverse ≡ rat rationalCoefficient
    normalizeCoefficient =
      cong (secondReciprocal ·ᵣ_) invertFirstReciprocal
      ∙ sym
          (rat·ᵣrat
            (fst (invℚ₊ secondRational))
            (fst firstRational))
      ∙ cong rat
          (ℚ.·Comm
            (fst (invℚ₊ secondRational))
            (fst firstRational))

    normalizeBound :
      dividedBound ≡ rat rationalCoefficient ·ᵣ secondDifference
    normalizeBound =
      reassociateProduct
      ∙ cong (_·ᵣ secondDifference) normalizeCoefficient

    coefficientPath : dividedBound +ᵣ base ≡ rightAt (suc N)
    coefficientPath =
      cong (_+ᵣ base) normalizeBound
      ∙ +ᵣComm (rat rationalCoefficient ·ᵣ secondDifference) base

    boundary : power (suc N) <ᵣ rightAt (suc N)
    boundary = isTrans<≡ᵣ _ _ _ strictStep coefficientPath


  convStep zero = isTrans≡<ᵣ _ _ _
    (·IdLᵣ _) (a<c+b⇒a-c<b _ _  _ fromAM-GM)
{-
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
         (sym (Cubical.HITs.CauchyReals.Algebra.Multiplication.x+x≡2x _))
       ∙∙ double-sub-shuffleᵣ _ _ _ ∙∙
       cong ((_-ᵣ fst (b ^ℚ x₀)) ∘ (_-ᵣ fst (b ^ℚ x (suc N))))
         (Cubical.HITs.CauchyReals.Algebra.Multiplication.x+x≡2x _)))))
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
-}
  convStep (suc N) = isTrans<ᵣ _ _ _ firstHalf secondHalf
    where
    power : ℕ → ℝ
    power k = fst (b ^ℚ x k)

    base : ℝ
    base = fst (b ^ℚ x₀)

    secondIndex : ℚ₊
    secondIndex = fromNat (suc (suc N))

    thirdIndex : ℚ₊
    thirdIndex = fromNat (suc (suc (suc N)))

    secondReciprocal : ℝ
    secondReciprocal = rat (fst (invℚ₊ secondIndex))

    thirdReciprocal : ℝ
    thirdReciprocal = rat (fst (invℚ₊ thirdIndex))

    secondDifference : ℝ
    secondDifference = power (suc (suc N)) -ᵣ base

    thirdDifference : ℝ
    thirdDifference = power (suc (suc (suc N))) -ᵣ base

    convexDifference : ℝ
    convexDifference =
      (2 ·ᵣ power (suc (suc N)) -ᵣ power (suc N)) -ᵣ base

    middle : ℝ
    middle = thirdReciprocal ·ᵣ convexDifference

    previousCoefficientℚ : ℚ
    previousCoefficientℚ = [ pos (suc N) / 2+ N ]

    previousCoefficient : ℝ
    previousCoefficient = rat previousCoefficientℚ

    previousDifference : ℝ
    previousDifference = power (suc N) -ᵣ base

    previousBound :
      previousDifference <ᵣ previousCoefficient ·ᵣ secondDifference
    previousBound =
      isTrans<≡ᵣ _ _ _
        (a<c+b⇒a-c<b
          (power (suc N))
          (rat (fst
            (fromNat (suc N) ·₊ invℚ₊ secondIndex)) ·ᵣ
            secondDifference)
          base
          (convSteps (suc N) N ℕ.≤-refl))
        (cong (_·ᵣ secondDifference)
          (cong rat (invℚ₊-[/] (pos (suc N)) (suc N))))

    negativePreviousBound :
      (-ᵣ previousCoefficient) ·ᵣ secondDifference <ᵣ
      -ᵣ previousDifference
    negativePreviousBound =
      isTrans≡<ᵣ _ _ _
        (-ᵣ· previousCoefficient secondDifference)
        (-ᵣ<ᵣ previousDifference
          (previousCoefficient ·ᵣ secondDifference)
          previousBound)

    expandedAverageBound :
      (2 ·ᵣ secondDifference) +ᵣ
        ((-ᵣ previousCoefficient) ·ᵣ secondDifference) <ᵣ
      (2 ·ᵣ secondDifference) -ᵣ previousDifference
    expandedAverageBound =
      <ᵣ-o+
        ((-ᵣ previousCoefficient) ·ᵣ secondDifference)
        (-ᵣ previousDifference)
        (2 ·ᵣ secondDifference)
        negativePreviousBound

    discreteDifferencePath :
      (2 ·ᵣ secondDifference) -ᵣ previousDifference ≡
      convexDifference
    discreteDifferencePath =
      cong (_-ᵣ previousDifference)
        (sym
          (Cubical.HITs.CauchyReals.Algebra.Multiplication.x+x≡2x
            secondDifference))
      ∙∙ double-sub-shuffleᵣ
          (power (suc (suc N))) base (power (suc N))
      ∙∙ cong
          ((_-ᵣ base) ∘ (_-ᵣ power (suc N)))
          (Cubical.HITs.CauchyReals.Algebra.Multiplication.x+x≡2x
            (power (suc (suc N))))

    thirdNatural : ℝ
    thirdNatural = rat (fst thirdIndex)

    scaleCoefficientℚ :
      fst thirdIndex ℚ.· fst (invℚ₊ secondIndex) ≡
      fromNat 2 ℚ.- previousCoefficientℚ
    scaleCoefficientℚ =
      invℚ₊-[/] (pos (suc (suc (suc N)))) (suc N)
      ∙ [2+N]/[1+N]=2-N/[1+N] (suc N)

    scaleCoefficient :
      thirdNatural ·ᵣ secondReciprocal ≡
      2 +ᵣ (-ᵣ previousCoefficient)
    scaleCoefficient =
      sym
        (rat·ᵣrat (fst thirdIndex) (fst (invℚ₊ secondIndex)))
      ∙ cong rat scaleCoefficientℚ
      ∙ sym (+ᵣ-rat (fromNat 2) (ℚ.- previousCoefficientℚ))
      ∙ cong (2 +ᵣ_) (sym (-ᵣ-rat previousCoefficientℚ))

    scaledLeft : ℝ
    scaledLeft =
      thirdNatural ·ᵣ (secondReciprocal ·ᵣ secondDifference)

    expandScaledLeft :
      scaledLeft ≡
      (2 ·ᵣ secondDifference) +ᵣ
        ((-ᵣ previousCoefficient) ·ᵣ secondDifference)
    expandScaledLeft =
      ·ᵣAssoc thirdNatural secondReciprocal secondDifference
      ∙ cong (_·ᵣ secondDifference) scaleCoefficient
      ∙ ·DistR+ 2 (-ᵣ previousCoefficient) secondDifference

    scaledAverageBound : scaledLeft <ᵣ convexDifference
    scaledAverageBound =
      isTrans≡<ᵣ _ _ _ expandScaledLeft
        (isTrans<≡ᵣ _ _ _
          expandedAverageBound discreteDifferencePath)

    divideScaledAverage :
      secondReciprocal ·ᵣ secondDifference <ᵣ
      convexDifference ·ᵣ
        fst (invℝ₊ (ℚ₊→ℝ₊ thirdIndex))
    divideScaledAverage =
      invEq
        (z<x/y₊≃y₊·z<x
          convexDifference
          (secondReciprocal ·ᵣ secondDifference)
          (ℚ₊→ℝ₊ thirdIndex))
        scaledAverageBound

    normalizeDivision :
      convexDifference ·ᵣ
        fst (invℝ₊ (ℚ₊→ℝ₊ thirdIndex)) ≡ middle
    normalizeDivision =
      cong (convexDifference ·ᵣ_) (invℝ₊-rat-opaque thirdIndex)
      ∙ ·ᵣComm convexDifference thirdReciprocal

    firstHalf :
      secondReciprocal ·ᵣ secondDifference <ᵣ middle
    firstHalf =
      isTrans<≡ᵣ _ _ _ divideScaledAverage normalizeDivision

    lowerStep :
      x (suc (suc N)) ℚ.- fst s ≡ x (suc N)
    lowerStep = ℚ!

    upperStep :
      x (suc (suc N)) ℚ.+ fst s ≡ x (suc (suc (suc N)))
    upperStep = x-suc (suc (suc N))

    amGMAtSecond :
      2 ·ᵣ power (suc (suc N)) <ᵣ
      power (suc N) +ᵣ power (suc (suc (suc N)))
    amGMAtSecond =
      isTrans<≡ᵣ _ _ _
        (AM-GM₂ b 1<b (x (suc (suc N))) s)
        (cong₂ _+ᵣ_
          (cong (fst ∘ (b ^ℚ_)) lowerStep)
          (cong (fst ∘ (b ^ℚ_)) upperStep))

    convexDifferenceBound : convexDifference <ᵣ thirdDifference
    convexDifferenceBound =
      <ᵣ-+o
        (2 ·ᵣ power (suc (suc N)) -ᵣ power (suc N))
        (power (suc (suc (suc N))))
        (-ᵣ base)
        (a<c+b⇒a-c<b
          (2 ·ᵣ power (suc (suc N)))
          (power (suc (suc (suc N))))
          (power (suc N))
          amGMAtSecond)

    secondHalf : middle <ᵣ thirdReciprocal ·ᵣ thirdDifference
    secondHalf =
      <ᵣ-o·ᵣ convexDifference thirdDifference
        (ℚ₊→ℝ₊ (invℚ₊ thirdIndex))
        convexDifferenceBound



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
    subst2 _<ᵣ_ leftPath rightPath sourceBound
   where
    αValue : ℚ
    αValue = [ pos (suc n) / 1+ m ]

    Δ/N : ℚ₊
    Δ/N = ([ pos 1 / 1+ m ] , ℚ.0<pos 0 (1+ m)) ·₊ Δ

    n/N-lem : [ pos (suc n) / 1 ] ℚ.· [ pos 1 / 1+ m ] ≡ [ pos (suc n) / 1+ m ]
    n/N-lem = cong₂ [_/_] (ℤ.·IdR (pos (suc n))) (·₊₁-identityˡ (1+ m))

    sampleScale :
      fromNat (suc n) ℚ.· fst Δ/N ≡ αValue ℚ.· fst Δ
    sampleScale =
      ℚ.·Assoc (fromNat (suc n)) [ pos 1 / 1+ m ] (fst Δ)
      ∙ cong (ℚ._· fst Δ) n/N-lem

    fullScale :
      fromNat (suc m) ℚ.· fst Δ/N ≡ fst Δ
    fullScale =
      ℚ.·Assoc (fromNat (suc m)) [ pos 1 / 1+ m ] (fst Δ)
      ∙ cong (ℚ._· fst Δ)
          (ℚ.x·invℚ₊[x] (fromNat (suc m)))
      ∙ ℚ.·IdL (fst Δ)

    coefficientScale :
      fst (fromNat (suc n) ·₊ invℚ₊ (fromNat (suc m))) ≡
      αValue
    coefficientScale = n/N-lem

    leftPath :
      fst (z ^ℚ
        (x ℚ.+ fromNat (suc n) ℚ.· fst Δ/N)) ≡
      fst (z ^ℚ (x ℚ.+ αValue ℚ.· fst Δ))
    leftPath =
      cong (fst ∘ z ^ℚ_ ∘ (x ℚ.+_)) sampleScale

    rightPath :
      fst (z ^ℚ x) +ᵣ
        rat (fst
          (fromNat (suc n) ·₊ invℚ₊ (fromNat (suc m)))) ·ᵣ
        (fst (z ^ℚ
          (x ℚ.+ fromNat (suc m) ℚ.· fst Δ/N)) -ᵣ
          fst (z ^ℚ x)) ≡
      fst (z ^ℚ x) +ᵣ
        rat αValue ·ᵣ
        (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x))
    rightPath =
      cong (fst (z ^ℚ x) +ᵣ_)
        (cong₂ _·ᵣ_
          (cong rat coefficientScale)
          (cong (_-ᵣ fst (z ^ℚ x))
            (cong (fst ∘ z ^ℚ_ ∘ (x ℚ.+_)) fullScale)))

    integerBound : pos (suc n) ℤ.< pos (suc m)
    integerBound =
      subst2 ℤ._<_
        (ℤ.·IdR (pos (suc n)))
        (ℤ.·IdL (pos (suc m)))
        (α<1 .ℚ._<_.prf)

    naturalBound : suc (suc n) ℕ.≤ suc m
    naturalBound =
      ℤ.pos-≤-pos→ℕ≤ (suc (suc n)) (suc m)
        (ℤ.<→suc≤ integerBound)

    indexBound : n ℕ.< m
    indexBound = ℕ.predℕ-≤-predℕ naturalBound

    sourceBound :
      fst (z ^ℚ
        (x ℚ.+ fromNat (suc n) ℚ.· fst Δ/N)) <ᵣ
      fst (z ^ℚ x) +ᵣ
        rat (fst
          (fromNat (suc n) ·₊ invℚ₊ (fromNat (suc m)))) ·ᵣ
        (fst (z ^ℚ
          (x ℚ.+ fromNat (suc m) ℚ.· fst Δ/N)) -ᵣ
          fst (z ^ℚ x))
    sourceBound =
      AM-GM-hlp.convSteps z 1<z x Δ/N m n indexBound
  w .ElimProp.f α@(ℤ.negsuc n , 1+ m) 0<α _ =
    ⊥.rec $ ℤ.¬pos≤negsuc (subst (0 ℤ.≤_)
             (ℤ.·IdR (ℤ.negsuc n))
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
                 ∙ Rℚ.0LeftAnnihilates (fst Δ)))
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
  invEq
    (z/y<x₊≃z<y₊·x slopeAC differenceAB intervalABℝ)
    scaledDifferenceBound

 where
 intervalAB : ℚ₊
 intervalAB = ℚ.<→ℚ₊ a b a<b

 intervalAC : ℚ₊
 intervalAC = ℚ.<→ℚ₊ a c a<c

 intervalABℝ : ℝ₊
 intervalABℝ = ℚ₊→ℝ₊ intervalAB

 intervalACℝ : ℝ₊
 intervalACℝ = ℚ₊→ℝ₊ intervalAC

 α₊ : ℚ₊
 α₊ = intervalAB ·₊ invℚ₊ intervalAC

 differenceAB : ℝ
 differenceAB = fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)

 differenceAC : ℝ
 differenceAC = fst (z ^ℚ c) -ᵣ fst (z ^ℚ a)

 slopeAC : ℝ
 slopeAC = differenceAC ／ᵣ₊ intervalACℝ

 intervalLt : fst intervalAB ℚ.< fst intervalAC
 intervalLt = ℚ.<-+o b c (ℚ.- a) b<c

 α<1 : fst α₊ ℚ.< 1
 α<1 =
   ℚ.x<y·z→x/y<z (fst intervalAB) intervalAC 1
     (subst (fst intervalAB ℚ.<_)
       (sym (ℚ.·IdR (fst intervalAC))) intervalLt)

 ratioCancel :
   fst α₊ ℚ.· fst intervalAC ≡ fst intervalAB
 ratioCancel =
   ℚ.·Comm (fst α₊) (fst intervalAC)
   ∙ cong (fst intervalAC ℚ.·_)
       (ℚ.·Comm (fst intervalAB) (fst (invℚ₊ intervalAC)))
   ∙ ℚ.y·[x/y] intervalAC (fst intervalAB)

 interpolationExponent :
   a ℚ.+ fst α₊ ℚ.· fst intervalAC ≡ b
 interpolationExponent =
   cong (a ℚ.+_) ratioCancel ∙ ℚ!

 endExponent : a ℚ.+ fst intervalAC ≡ c
 endExponent = ℚ!

 leftPath :
   fst (z ^ℚ (a ℚ.+ fst α₊ ℚ.· fst intervalAC)) ≡
   fst (z ^ℚ b)
 leftPath = cong (fst ∘ z ^ℚ_) interpolationExponent

 rightPath :
   fst (z ^ℚ a) +ᵣ rat (fst α₊) ·ᵣ
     (fst (z ^ℚ (a ℚ.+ fst intervalAC)) -ᵣ fst (z ^ℚ a)) ≡
   fst (z ^ℚ a) +ᵣ rat (fst α₊) ·ᵣ differenceAC
 rightPath =
   cong (fst (z ^ℚ a) +ᵣ_)
     (cong (rat (fst α₊) ·ᵣ_)
       (cong (_-ᵣ fst (z ^ℚ a))
         (cong (fst ∘ z ^ℚ_) endExponent)))

 amGMAtPoints :
   fst (z ^ℚ b) <ᵣ
   fst (z ^ℚ a) +ᵣ rat (fst α₊) ·ᵣ differenceAC
 amGMAtPoints =
   subst2 _<ᵣ_ leftPath rightPath
     (AM-GM-strict z a 1<z intervalAC
       (fst α₊) (snd α₊) α<1)

 differenceBound :
   differenceAB <ᵣ rat (fst α₊) ·ᵣ differenceAC
 differenceBound =
   a<c+b⇒a-c<b
     (fst (z ^ℚ b))
     (rat (fst α₊) ·ᵣ differenceAC)
     (fst (z ^ℚ a))
     amGMAtPoints

 ratioAsReal :
   rat (fst α₊) ≡
   rat (fst intervalAB) ·ᵣ rat (fst (invℚ₊ intervalAC))
 ratioAsReal =
   rat·ᵣrat (fst intervalAB) (fst (invℚ₊ intervalAC))

 scaledSlopePath :
   rat (fst α₊) ·ᵣ differenceAC ≡
   fst intervalABℝ ·ᵣ slopeAC
 scaledSlopePath =
   cong (_·ᵣ differenceAC) ratioAsReal
   ∙ sym
       (·ᵣAssoc
         (rat (fst intervalAB))
         (rat (fst (invℚ₊ intervalAC)))
         differenceAC)
   ∙ cong (rat (fst intervalAB) ·ᵣ_)
       (·ᵣComm (rat (fst (invℚ₊ intervalAC))) differenceAC
       ∙ cong (differenceAC ·ᵣ_)
           (sym (invℝ₊-rat-opaque intervalAC)))

 scaledDifferenceBound :
   differenceAB <ᵣ fst intervalABℝ ·ᵣ slopeAC
 scaledDifferenceBound =
   isTrans<≡ᵣ _ _ _ differenceBound scaledSlopePath

opaque
  slope-incr-strict-opaque :
      (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ) →
      (a<b : a ℚ.< b) → (b<c : b ℚ.< c) → (a<c : a ℚ.< c) →
      ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b)) <ᵣ
      ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a c a<c))
  slope-incr-strict-opaque = slope-incr-strict

  slope-zero-one-strict-below :
    (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (r : ℚ) →
    (0<r : 0 ℚ.< r) → (r<1 : r ℚ.< 1) → (0<1 : 0 ℚ.< 1) →
    ((fst (z ^ℚ r) -ᵣ fst (z ^ℚ 0))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) <ᵣ
    ((fst (z ^ℚ 1) -ᵣ fst (z ^ℚ 0))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 0<1))
  slope-zero-one-strict-below z 1<z r 0<r r<1 0<1 =
    slope-incr-strict-opaque z 1<z 0 r 1 0<r r<1 0<1

  slope-zero-one-strict-above :
    (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (r : ℚ) →
    (0<1 : 0 ℚ.< 1) → (1<r : 1 ℚ.< r) → (0<r : 0 ℚ.< r) →
    ((fst (z ^ℚ 1) -ᵣ fst (z ^ℚ 0))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 0<1)) <ᵣ
    ((fst (z ^ℚ r) -ᵣ fst (z ^ℚ 0))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r))
  slope-zero-one-strict-above z 1<z r 0<1 1<r 0<r =
    slope-incr-strict-opaque z 1<z 0 1 r 0<1 1<r 0<r

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
                (slope-incr-strict-opaque z 1<z a b c a<b b<c a<c)
                (cong₂ _／ᵣ₊_
                  (diff-split (fst (z ^ℚ a)) (fst (z ^ℚ b)) (fst (z ^ℚ c)))
                  (ℝ₊≡ (cong rat ℚ! ∙ sym (+ᵣ-rat _ _)))))
  in isTrans≡<ᵣ _ _ _
      (cong₂ _／ᵣ₊_
        (diff-split (fst (z ^ℚ a)) (fst (z ^ℚ b)) (fst (z ^ℚ c)))
        ((ℝ₊≡ (cong rat ℚ! ∙ sym (+ᵣ-rat _ _))))) w

private
  opaque
    forwardSlope :
      (z : ℝ₊) (a q : ℚ) → a ℚ.< q → ℝ
    forwardSlope z a q a<q =
      (fst (z ^ℚ q) -ᵣ fst (z ^ℚ a))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q)

    negatedIntervalSlope :
      (z : ℝ₊) (a q : ℚ) → a ℚ.< q → ℝ
    negatedIntervalSlope z a q a<q =
      (fst (z ^ℚ (ℚ.- a)) -ᵣ fst (z ^ℚ (ℚ.- q)))
        ／ᵣ₊ ℚ₊→ℝ₊
          (ℚ.<→ℚ₊ (ℚ.- q) (ℚ.- a) (ℚ.minus-< a q a<q))

  opaque
    unfolding negatedIntervalSlope
    slope-incr-negated-strict :
      (z : ℝ₊) (1<z : 1 <ᵣ fst z) →
      (a b c : ℚ) →
      (a<b : a ℚ.< b) → (b<c : b ℚ.< c) → (a<c : a ℚ.< c) →
      negatedIntervalSlope z a c a<c <ᵣ
      negatedIntervalSlope z a b a<b
    slope-incr-negated-strict z 1<z a b c a<b b<c a<c =
      slope-incr'-strict z 1<z
        (ℚ.- c) (ℚ.- b) (ℚ.- a)
        (ℚ.minus-< b c b<c)
        (ℚ.minus-< a b a<b)
        (ℚ.minus-< a c a<c)

  opaque
    unfolding forwardSlope negatedIntervalSlope
    negatedIntervalSlope-inverseBase :
      (z : ℝ₊) (a q : ℚ) (a<q : a ℚ.< q) →
      -ᵣ negatedIntervalSlope (invℝ₊ z) a q a<q ≡
      forwardSlope z a q a<q
    negatedIntervalSlope-inverseBase z a q a<q =
      sym
        (-ᵣ·
          (fst (invℝ₊ z ^ℚ (ℚ.- a)) -ᵣ
            fst (invℝ₊ z ^ℚ (ℚ.- q)))
          (fst
            (invℝ₊
              (ℚ₊→ℝ₊
                (ℚ.<→ℚ₊ (ℚ.- q) (ℚ.- a)
                  (ℚ.minus-< a q a<q))))))
      ∙ cong₂ (λ difference interval →
          difference ／ᵣ₊ ℚ₊→ℝ₊ interval)
          (-[x-y]≡y-x
            (fst (invℝ₊ z ^ℚ (ℚ.- a)))
            (fst (invℝ₊ z ^ℚ (ℚ.- q)))
          ∙ cong₂ _-ᵣ_
              (sym (cong fst (^ℚ-minus z q)))
              (sym (cong fst (^ℚ-minus z a))))
          (ℚ₊≡ ℚ!)

  opaque
    unfolding forwardSlope
    forwardSlope-formula :
      (z : ℝ₊) (a q : ℚ) (a<q : a ℚ.< q) →
      forwardSlope z a q a<q ≡
      (fst (z ^ℚ q) -ᵣ fst (z ^ℚ a))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q)
    forwardSlope-formula z a q a<q = refl
{-
      isTrans≡<ᵣ _ _ _ combinedSlopePath mediantBound
      where
      leftOrder : (ℚ.- c) ℚ.< (ℚ.- b)
      leftOrder = ℚ.minus-< b c b<c

      rightOrder : (ℚ.- b) ℚ.< (ℚ.- a)
      rightOrder = ℚ.minus-< a b a<b

      wholeOrder : (ℚ.- c) ℚ.< (ℚ.- a)
      wholeOrder = ℚ.minus-< a c a<c

      leftInterval : ℚ₊
      leftInterval = ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- b) leftOrder

      rightInterval : ℚ₊
      rightInterval = ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) rightOrder

      wholeInterval : ℚ₊
      wholeInterval = ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) wholeOrder

      leftIntervalℝ : ℝ₊
      leftIntervalℝ = ℚ₊→ℝ₊ leftInterval

      rightIntervalℝ : ℝ₊
      rightIntervalℝ = ℚ₊→ℝ₊ rightInterval

      wholeIntervalℝ : ℝ₊
      wholeIntervalℝ = ℚ₊→ℝ₊ wholeInterval

      leftDifference : ℝ
      leftDifference =
        fst (z ^ℚ (ℚ.- b)) -ᵣ fst (z ^ℚ (ℚ.- c))

      rightDifference : ℝ
      rightDifference =
        fst (z ^ℚ (ℚ.- a)) -ᵣ fst (z ^ℚ (ℚ.- b))

      wholeDifference : ℝ
      wholeDifference =
        fst (z ^ℚ (ℚ.- a)) -ᵣ fst (z ^ℚ (ℚ.- c))

      intervalSplitℚ :
        fst wholeInterval ≡ fst leftInterval ℚ.+ fst rightInterval
      intervalSplitℚ = ℚ!

      intervalSplit :
        wholeIntervalℝ ≡ leftIntervalℝ ₊+ᵣ rightIntervalℝ
      intervalSplit =
        ℝ₊≡
          (cong rat intervalSplitℚ
          ∙ sym (+ᵣ-rat (fst leftInterval) (fst rightInterval)))

      differenceSplit :
        wholeDifference ≡ leftDifference +ᵣ rightDifference
      differenceSplit =
        diff-split
          (fst (z ^ℚ (ℚ.- c)))
          (fst (z ^ℚ (ℚ.- b)))
          (fst (z ^ℚ (ℚ.- a)))

      combinedSlopePath :
        wholeDifference ／ᵣ₊ wholeIntervalℝ ≡
        (leftDifference +ᵣ rightDifference)
          ／ᵣ₊ (leftIntervalℝ ₊+ᵣ rightIntervalℝ)
      combinedSlopePath =
        cong₂ _／ᵣ₊_ differenceSplit intervalSplit

      leftBound :
        leftDifference ／ᵣ₊ leftIntervalℝ <ᵣ
        wholeDifference ／ᵣ₊ wholeIntervalℝ
      leftBound = ?

      leftToCombined :
        leftDifference ／ᵣ₊ leftIntervalℝ <ᵣ
        (leftDifference +ᵣ rightDifference)
          ／ᵣ₊ (leftIntervalℝ ₊+ᵣ rightIntervalℝ)
      leftToCombined =
        isTrans<≡ᵣ _ _ _ leftBound combinedSlopePath

      mediantBound :
        (leftDifference +ᵣ rightDifference)
          ／ᵣ₊ (leftIntervalℝ ₊+ᵣ rightIntervalℝ) <ᵣ
        rightDifference ／ᵣ₊ rightIntervalℝ
      mediantBound =
        fst
          (x'/x<[x'+y']/[x+y]≃[x'+y']/[x+y]<y'/y
            leftIntervalℝ leftDifference
            rightIntervalℝ rightDifference)
          leftToCombined
-}

opaque
  powerSecantSlope :
      (a q : ℚ) → a ℚ.< q → ∀ x → 0 <ᵣ x → ℝ
  powerSecantSlope a q a<q x 0<x =
      (fst ((x , 0<x) ^ℚ q) -ᵣ fst ((x , 0<x) ^ℚ a))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q)

opaque
  unfolding powerSecantSlope
  powerSecantSlope-formula :
      (a q : ℚ) (a<q : a ℚ.< q) (x : ℝ) (0<x : 0 <ᵣ x) →
      powerSecantSlope a q a<q x 0<x ≡
      (fst ((x , 0<x) ^ℚ q) -ᵣ fst ((x , 0<x) ^ℚ a))
        ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q)
  powerSecantSlope-formula a q a<q x 0<x = refl

opaque
  unfolding powerSecantSlope _+ᵣ_ -ᵣ_
  powerSecantSlope-continuous :
      (a q : ℚ) (a<q : a ℚ.< q) →
      IsContinuousWithPred posℙ (powerSecantSlope a q a<q)
  powerSecantSlope-continuous a q a<q =
      IsContinuousWP∘' posℙ
        (_·ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q))))
        (λ x 0<x →
          fst ((x , 0<x) ^ℚ q) -ᵣ fst ((x , 0<x) ^ℚ a))
        (IsContinuous·ᵣR
          (fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q)))))
        (contDiagNE₂WP sumR posℙ
          (curry (fst ∘ (_^ℚ q)))
          (λ x 0<x → -ᵣ fst ((x , 0<x) ^ℚ a))
          (IsContinuous^ℚ q)
          (IsContinuousWP∘' posℙ (-ᵣ_)
            (curry (fst ∘ (_^ℚ a)))
            IsContinuous-ᵣ (IsContinuous^ℚ a)))

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
   subst2 _≤ᵣ_
     (powerSecantSlope-formula a b a<b z 0<z)
     (powerSecantSlope-formula a c a<c z 0<z)
     (continuousOpenLowerComparison
       {x₀ = 0}
       {f₀ = powerSecantSlope a b a<b}
       {f₁ = powerSecantSlope a c a<c}
       (powerSecantSlope-continuous a b a<b)
       (powerSecantSlope-continuous a c a<c)
       rationalComparison
       z 0<z)

  where

   slope-incr** : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ)
     → (a<b : a ℚ.< b) → (b≤c : b ℚ.≤ c) →  (a<c : a ℚ.< c) →
     ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
         ≤ᵣ
     ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))
   slope-incr** z 1<z a b c a<b b≤c a<c =
      ⊎.rec equalCase strictCase (ℚ.≤→≡⊎< b c b≤c)
      where
      slopeTo : Σ[ q ∈ ℚ ] (a ℚ.< q) → ℝ
      slopeTo (q , a<q) =
        (fst (z ^ℚ q) -ᵣ fst (z ^ℚ a))
          ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q)

      equalCase : b ≡ c → slopeTo (b , a<b) ≤ᵣ slopeTo (c , a<c)
      equalCase b=c =
        subst
          (λ q → (a<q : a ℚ.< q) →
            slopeTo (b , a<b) ≤ᵣ slopeTo (q , a<q))
          b=c sameEndpoint a<c
        where
        sameEndpoint :
          (a<b' : a ℚ.< b) →
          slopeTo (b , a<b) ≤ᵣ slopeTo (b , a<b')
        sameEndpoint a<b' =
          ≡ᵣWeaken≤ᵣ _ _
            (cong (λ proof → slopeTo (b , proof))
              (ℚ.isProp< a b a<b a<b'))

      strictCase : b ℚ.< c → slopeTo (b , a<b) ≤ᵣ slopeTo (c , a<c)
      strictCase b<c =
        <ᵣWeaken≤ᵣ _ _
          (slope-incr-strict-opaque z 1<z a b c a<b b<c a<c)

   comparisonFamily : ℚ → Type
   comparisonFamily u =
     (0<u : 0 <ᵣ rat u) →
     ((fst ((rat u , 0<u) ^ℚ b) -ᵣ fst ((rat u , 0<u) ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b)) ≤ᵣ
     ((fst ((rat u , 0<u) ^ℚ c) -ᵣ fst ((rat u , 0<u) ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a c a<c))

   w : ℚ.TrichotomyRec 1 comparisonFamily
   w .ℚ.TrichotomyRec.lt-case u u<1 0<u =
     subst2 _≤ᵣ_ leftPath rightPath negatedInverseOrder
     where
     u₊ : ℝ₊
     u₊ = (rat u , 0<u)

     1/u₊ : ℝ₊
     1/u₊ = invℝ₊ u₊

     1<1/u : 1 <ᵣ fst 1/u₊
     1<1/u =
       isTrans<≡ᵣ _ _ _
         (invEq (z<x/y₊≃y₊·z<x 1 1 u₊)
           (isTrans≡<ᵣ _ _ _ (·IdR (rat u)) (<ℚ→<ᵣ u 1 u<1)))
         (·IdLᵣ (fst (invℝ₊ u₊)))

     inverseSlope : ∀ q → (a<q : a ℚ.< q) → ℝ
     inverseSlope q a<q = negatedIntervalSlope 1/u₊ a q a<q

     originalSlope : ∀ q → (a<q : a ℚ.< q) → ℝ
     originalSlope q a<q = forwardSlope u₊ a q a<q

     negativeSlopePath : ∀ q (a<q : a ℚ.< q) →
       -ᵣ inverseSlope q a<q ≡ originalSlope q a<q
     negativeSlopePath q a<q =
       negatedIntervalSlope-inverseBase u₊ a q a<q

     equalInverseOrder : b ≡ c →
       inverseSlope c a<c ≤ᵣ inverseSlope b a<b
     equalInverseOrder b=c =
       subst
         (λ q → (a<q : a ℚ.< q) →
           inverseSlope c a<c ≤ᵣ inverseSlope q a<q)
         (sym b=c) sameEndpoint a<b
       where
       sameEndpoint : (a<c' : a ℚ.< c) →
         inverseSlope c a<c ≤ᵣ inverseSlope c a<c'
       sameEndpoint a<c' =
         ≡ᵣWeaken≤ᵣ _ _
           (cong (inverseSlope c) (ℚ.isProp< a c a<c a<c'))

     strictInverseOrder : b ℚ.< c →
       inverseSlope c a<c ≤ᵣ inverseSlope b a<b
     strictInverseOrder b<c =
       <ᵣWeaken≤ᵣ _ _
         (slope-incr-negated-strict 1/u₊ 1<1/u
           a b c a<b b<c a<c)

     inverseOrder : inverseSlope c a<c ≤ᵣ inverseSlope b a<b
     inverseOrder =
       ⊎.rec equalInverseOrder strictInverseOrder
         (ℚ.≤→≡⊎< b c b≤c)

     negatedInverseOrder :
       -ᵣ inverseSlope b a<b ≤ᵣ -ᵣ inverseSlope c a<c
     negatedInverseOrder =
       -ᵣ≤ᵣ (inverseSlope c a<c) (inverseSlope b a<b) inverseOrder

     leftPath :
       -ᵣ inverseSlope b a<b ≡
       (fst (u₊ ^ℚ b) -ᵣ fst (u₊ ^ℚ a))
         ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b)
     leftPath =
       negativeSlopePath b a<b ∙ forwardSlope-formula u₊ a b a<b

     rightPath :
       -ᵣ inverseSlope c a<c ≡
       (fst (u₊ ^ℚ c) -ᵣ fst (u₊ ^ℚ a))
         ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a c a<c)
     rightPath =
       negativeSlopePath c a<c ∙ forwardSlope-formula u₊ a c a<c
{-
     subst2 _≤ᵣ_ leftPath rightPath negatedInverseOrder
     where
     u₊ : ℝ₊
     u₊ = (rat u , 0<u)

     1/u₊ : ℝ₊
     1/u₊ = invℝ₊ u₊

     1<1/u : 1 <ᵣ (fst 1/u₊)
     1<1/u =
       isTrans<≡ᵣ _ _ _
         (invEq (z<x/y₊≃y₊·z<x 1 1 u₊)
           (isTrans≡<ᵣ _ _ _ (·IdR (rat u)) (<ℚ→<ᵣ u 1 u<1)))
         (·IdLᵣ (fst (invℝ₊ u₊)))

     intervalAB : ℚ₊
     intervalAB = ℚ.<→ℚ₊ a b a<b

     intervalAC : ℚ₊
     intervalAC = ℚ.<→ℚ₊ a c a<c

     negativeInterval : ∀ q → a ℚ.< q → ℚ₊
     negativeInterval q a<q =
       ℚ.<→ℚ₊ (ℚ.- q) (ℚ.- a) (ℚ.minus-< a q a<q)

     inverseSlope : ∀ q → (a<q : a ℚ.< q) → ℝ
     inverseSlope q a<q =
       (fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- q)))
         ／ᵣ₊ ℚ₊→ℝ₊ (negativeInterval q a<q)

     originalSlope : ∀ q → (a<q : a ℚ.< q) → ℝ
     originalSlope q a<q =
       (fst (u₊ ^ℚ q) -ᵣ fst (u₊ ^ℚ a))
         ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a q a<q)

     negativeNumeratorPath : ∀ q →
       -ᵣ (fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ
         fst (1/u₊ ^ℚ (ℚ.- q))) ≡
       fst (u₊ ^ℚ q) -ᵣ fst (u₊ ^ℚ a)
     negativeNumeratorPath q = ?

     negativeIntervalPath : ∀ q (a<q : a ℚ.< q) →
       negativeInterval q a<q ≡ ℚ.<→ℚ₊ a q a<q
     negativeIntervalPath q a<q = ℚ₊≡ ℚ!

     negativeSlopePath : ∀ q (a<q : a ℚ.< q) →
       -ᵣ inverseSlope q a<q ≡ originalSlope q a<q
     negativeSlopePath q a<q =
       sym
         (-ᵣ·
           (fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ
             fst (1/u₊ ^ℚ (ℚ.- q)))
           (fst (invℝ₊ (ℚ₊→ℝ₊ (negativeInterval q a<q)))))
       ∙ cong₂ (λ difference interval →
           difference ／ᵣ₊ ℚ₊→ℝ₊ interval)
           (negativeNumeratorPath q)
           (negativeIntervalPath q a<q)

     equalInverseOrder : b ≡ c →
       inverseSlope c a<c ≤ᵣ inverseSlope b a<b
     equalInverseOrder b=c = ?

     strictInverseOrder : b ℚ.< c →
       inverseSlope c a<c ≤ᵣ inverseSlope b a<b
     strictInverseOrder b<c = rawStrict
       where
       rawStrict :
         ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- c)))
           ／ᵣ₊ ℚ₊→ℝ₊
             (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a)
               (ℚ.minus-< a c a<c))) ≤ᵣ
         ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- b)))
           ／ᵣ₊ ℚ₊→ℝ₊
             (ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a)
               (ℚ.minus-< a b a<b)))
       rawStrict =
         ?

     inverseOrder : inverseSlope c a<c ≤ᵣ inverseSlope b a<b
     inverseOrder =
       ⊎.rec equalInverseOrder strictInverseOrder
         (ℚ.≤→≡⊎< b c b≤c)

     negatedInverseOrder :
       -ᵣ inverseSlope b a<b ≤ᵣ -ᵣ inverseSlope c a<c
     negatedInverseOrder =
       -ᵣ≤ᵣ (inverseSlope c a<c) (inverseSlope b a<b) inverseOrder

     leftPath : -ᵣ inverseSlope b a<b ≡ originalSlope b a<b
     leftPath = negativeSlopePath b a<b

     rightPath : -ᵣ inverseSlope c a<c ≡ originalSlope c a<c
     rightPath = negativeSlopePath c a<c
-}


{-
   w .ℚ.TrichotomyRec.eq-case _ = ≡ᵣWeaken≤ᵣ _ _
             (Rℝ.0LeftAnnihilates' _ _
                 (Rℝ.+InvR' _ _ (cong (fst ∘ (_^ℚ b)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 b)
                   ∙ sym (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 a))))
               ∙ sym (Rℝ.0LeftAnnihilates' _ _
                 (Rℝ.+InvR' _ _ ((cong (fst ∘ (_^ℚ c)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 c)
                   ∙ sym (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 a)))))))
   w .ℚ.TrichotomyRec.gt-case u 1<u 0<u =
     slope-incr** (rat u , 0<u) (<ℚ→<ᵣ _ _ 1<u) a b c a<b b≤c a<c
-}
   w .ℚ.TrichotomyRec.eq-case _ = ≡ᵣWeaken≤ᵣ _ _
     (Rℝ.0LeftAnnihilates' _ _
       (Rℝ.+InvR' _ _
         (cong (fst ∘ (_^ℚ b)) (ℝ₊≡ refl)
         ∙ cong fst (1^ℚ≡1 b)
         ∙ sym
             (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl)
             ∙ cong fst (1^ℚ≡1 a))))
     ∙ sym
         (Rℝ.0LeftAnnihilates' _ _
           (Rℝ.+InvR' _ _
             (cong (fst ∘ (_^ℚ c)) (ℝ₊≡ refl)
             ∙ cong fst (1^ℚ≡1 c)
             ∙ sym
                 (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl)
                 ∙ cong fst (1^ℚ≡1 a))))))
   w .ℚ.TrichotomyRec.gt-case u 1<u 0<u =
     slope-incr** (rat u , 0<u) (<ℚ→<ᵣ 1 u 1<u)
       a b c a<b b≤c a<c

   rationalComparison : ∀ u (0<u : 0 <ᵣ rat u) →
     powerSecantSlope a b a<b (rat u) 0<u ≤ᵣ
     powerSecantSlope a c a<c (rat u) 0<u
   rationalComparison u 0<u =
     subst2 _≤ᵣ_
       (sym (powerSecantSlope-formula a b a<b (rat u) 0<u))
       (sym (powerSecantSlope-formula a c a<c (rat u) 0<u))
       (ℚ.byTrichotomy 1 {A = comparisonFamily} w u 0<u)

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

{-
opaque
 unfolding invℝ
 bernoulli's-ineq-^ℚ-r<1 : ∀ x r → 1 <ᵣ fst x → 0 ℚ.< r → r ℚ.< 1 → fst (x ^ℚ r) <ᵣ 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)
 bernoulli's-ineq-^ℚ-r<1 x r 1<x 0<r r<1 =
   isTrans<≡ᵣ _ _ _ addBound
     (+ᵣComm (rat r ·ᵣ (fst x -ᵣ 1)) 1)
   where
   strictSlope :
     ((fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) <ᵣ
     ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 ℚ.decℚ<?))
   strictSlope =
     slope-incr-strict-opaque x 1<x 0 r 1 0<r r<1 ℚ.decℚ<?

   unscaledBound :
     fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0) <ᵣ
     fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
       ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
         ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 ℚ.decℚ<?))
   unscaledBound =
     fst
       (z/y<x₊≃z<y₊·x
         ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
           ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 ℚ.decℚ<?))
         (fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0))
         (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)))
       strictSlope

   zeroPowerPath : fst (x ^ℚ 0) ≡ 1
   zeroPowerPath = cong fst (^ℚ-zero x)

   onePowerPath : fst (x ^ℚ 1) ≡ fst x
   onePowerPath = cong fst (^ℚ-1 x)

   differenceRPath :
     fst (x ^ℚ r) -ᵣ fst (x ^ℚ 0) ≡
     fst (x ^ℚ r) -ᵣ 1
   differenceRPath =
     cong (λ y → fst (x ^ℚ r) -ᵣ y) zeroPowerPath

   intervalRPath :
     fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ≡ rat r
   intervalRPath = cong rat ℚ!

   intervalOnePath :
     ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 ℚ.decℚ<?) ≡ 1
   intervalOnePath = ℝ₊≡ (cong rat ℚ!)

   intervalOneInversePath :
     fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 ℚ.decℚ<?))) ≡ 1
   intervalOneInversePath =
     cong (fst ∘ invℝ₊) intervalOnePath ∙ cong fst invℝ₊1

   oneDifferencePath :
     fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0) ≡ fst x -ᵣ 1
   oneDifferencePath = cong₂ _-ᵣ_ onePowerPath zeroPowerPath

   slopeOnePath :
     ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 ℚ.decℚ<?)) ≡
     fst x -ᵣ 1
   slopeOnePath =
     cong₂ _·ᵣ_ oneDifferencePath intervalOneInversePath
     ∙ ·IdR (fst x -ᵣ 1)

   scaledSlopePath :
     fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 r 0<r)) ·ᵣ
       ((fst (x ^ℚ 1) -ᵣ fst (x ^ℚ 0))
         ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ 0 1 ℚ.decℚ<?)) ≡
     rat r ·ᵣ (fst x -ᵣ 1)
   scaledSlopePath = cong₂ _·ᵣ_ intervalRPath slopeOnePath

   normalizedBound :
     fst (x ^ℚ r) -ᵣ 1 <ᵣ rat r ·ᵣ (fst x -ᵣ 1)
   normalizedBound =
     subst2 _<ᵣ_ differenceRPath scaledSlopePath unscaledBound

   addBound :
     fst (x ^ℚ r) <ᵣ rat r ·ᵣ (fst x -ᵣ 1) +ᵣ 1
   addBound =
     a-b<c⇒a<c+b (fst (x ^ℚ r)) 1
       (rat r ·ᵣ (fst x -ᵣ 1)) normalizedBound

 bernoulli's-ineq-^ℚ : ∀ x r → 1 <ᵣ fst x
  → 1 ℚ.< r → 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)  <ᵣ fst (x ^ℚ r)
 bernoulli's-ineq-^ℚ x r 1<x 1<r = ?
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
-}
