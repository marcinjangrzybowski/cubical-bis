module Cubical.HITs.CauchyReals.Transcendental.Roots.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order.Inductive as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Analysis.Lipschitz using
  ( IsLipschitzWithOn
  ; isLipschitzWithOnOrdered→isLipschitzWithOn
  )


open import Cubical.HITs.CauchyReals.Foundation.Base

open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp using
  (elimIntervalByClampᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base using (IsContinuous^ⁿ)
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.Data.Rationals.Bisection as ℚB

open ℚ using (invℚ)

invℚ₊ : ℚ₊ → ℚ₊
invℚ₊ = ℚ._⁻¹₊

infixl 8 _ℚ^ⁿ_ _ℚ₊^ⁿ_

_ℚ^ⁿ_ : ℚ → ℕ → ℚ
_ℚ^ⁿ_ = ℚ._^ⁿ_

_ℚ₊^ⁿ_ : ℚ₊ → ℕ → ℚ₊
_ℚ₊^ⁿ_ = ℚ._ℚ₊^ⁿ_

open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

sqrRestr< : ∀ n → (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) ℚ.< (fromNat (2 ℕ.+ n))
sqrRestr< n =
  (ℚ.isTrans< (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) 1 (fromNat (2 ℕ.+ n))
               (fst (ℚ.invℚ₊-<-invℚ₊ 1 ([ (1+ (suc n)) / 1 ]₊))
                 (ℚ.inj (ℤ.Σℕ→< (_ , refl))))
               (ℚ.inj (ℤ.Σℕ→< (_ , refl))))

module NthRoot (m : ℕ) where


 module _ (n : ℕ) where


  open bⁿ-aⁿ m hiding (n)


  A B : ℝ
  A = rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
  B = (fromNat (2 ℕ.+ n))
  0<A = (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))))
  0<B = (snd (ℚ₊→ℝ₊ (fromNat (2 ℕ.+ n))))
  A<B : A <ᵣ B
  A<B = <ℚ→<ᵣ _ _ (sqrRestr< n)



  L = (((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m))
      ·₊ (fromNat (2 ℕ.+ m)))

  K = (fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)

  aℚ bℚ : ℚ
  aℚ = fst (invℚ₊ (fromNat (2 ℕ.+ n)))
  bℚ = fromNat (2 ℕ.+ n)

  powℚ : ℚ → ℚ
  powℚ x = x ℚ^ⁿ (2 ℕ.+ m)

  module RootQB = ℚB.ℚIncrFunBisectFamily aℚ bℚ (sqrRestr< n) powℚ

  Sourceℚℙ : ℙ ℚ
  Sourceℚℙ = ℚ.ℚintervalℙ aℚ bℚ

  Sourceℙ : ℙ ℝ
  Sourceℙ = intervalℙ (rat aℚ) (rat bℚ)

  incrF : isIncrasingℙ
   Sourceℚℙ (λ x _ → powℚ x)
  incrF  x x∈ y y∈ =
    ℚ^ⁿ-StrictMonotone (2 ℕ.+ m)
     (ℕ.≤-suc (ℕ.suc-≤-suc (ℕ.zero-≤ {m})))
     (ℚ.isTrans≤ 0 (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          x (ℚ.0≤ℚ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))) (fst x∈))
     (ℚ.isTrans≤ 0 (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          y (ℚ.0≤ℚ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))) (fst y∈))

  1/K<L : fst (invℚ₊ K) ℚ.< fst L
  1/K<L = ℚ.isTrans≤< _ 1 _
    (subst (ℚ._≤ 1) (sym (ℚ.invℚ₊-ℚ^ⁿ ([ (1+ (suc n)) / 1 ]₊) (suc m)))
      (ℚ.x^ⁿ≤1 _ (suc m) (ℚ.0≤pos _ _)
       (ℚ.invℚ₊≤invℚ₊ (fromNat (2 ℕ.+ n)) 1
        (≤ℤ→≤ℚ _ _ (ℤ.pos≤pos tt)))))
         (ℚ.isTrans≤< _ _ _
           (ℚ.1≤x^ⁿ (fromNat (2 ℕ.+ n))
            (fromNat (1 ℕ.+ m)) ((≤ℤ→≤ℚ _ _ (ℤ.pos≤pos tt))))
            (subst (ℚ._< fst L)

               (ℚ.·IdR _)
                 (ℚ.<-o· 1 (fromNat (2 ℕ.+ m))
                   _ (snd ((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)))
            ((<ℤ→<ℚ 1 (ℤ.pos (suc (suc m)))
             (ℤ.pos<pos tt)))))
            )


  powerUpperOrdered≤ᵣ :
    ∀ q → rat q ∈ Sourceℙ →
    ∀ r → rat r ∈ Sourceℙ →
    r ℚ.< q →
    absᵣ (rat (powℚ q) -ᵣ rat (powℚ r))
      ≤ᵣ rat (fst L ℚ.· (q ℚ.- r))
  powerUpperOrdered≤ᵣ q q∈ r r∈ r<q =
       let 0<r : 0 <ᵣ (rat r)
           0<r = isTrans<≤ᵣ 0 A (rat r) 0<A (fst r∈)
           0<q : 0 <ᵣ (rat q)
           0<q = isTrans<ᵣ 0 (rat r) (rat q) 0<r (<ℚ→<ᵣ _ _ r<q)

           ineqL : (rat q ^ⁿ suc (suc m)) -ᵣ (rat r ^ⁿ suc (suc m))
                      ≤ᵣ rat ((fst L) ℚ.· (q ℚ.- r))

           ineqL =
             isTrans≡≤ᵣ _ _ _ (sym $
                  [b-a]·S≡bⁿ-aⁿ (rat r) (rat q)
                     0<r 0<q)
               (isTrans≤≡ᵣ _ _ _ (≤ᵣ-o·ᵣ _ _ _
                      (isTrans≤≡ᵣ _ _ _  (≤ℚ→≤ᵣ _ _  $ ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q))
                       (sym (-ᵣ-rat₂ _ _))) --
                    (isTrans≤≡ᵣ _ _ _
               (S≤Bⁿ·n (rat r) (rat q) 0<r 0<q A B 0<A
                     (isTrans≤<ᵣ _ _ _
                       (fst r∈ ) (<ℚ→<ᵣ _ _ r<q)) 0<B A<B
                  (snd q∈)
                  (<ℚ→<ᵣ _ _ r<q))
                      (sym ((rat·ᵣrat ((fromNat (2 ℕ.+ n)) ℚ^ⁿ suc m) (fromNat (2 ℕ.+ m))
                        ∙ cong (_·ᵣ (rat ((fromNat (2 ℕ.+ m)))))
                          (sym (^ⁿ-ℚ^ⁿ (suc m) (fromNat (2 ℕ.+ n)))))))
                          ))
                           (cong₂ _·ᵣ_ (-ᵣ-rat₂ _ _) refl ∙ (sym (rat·ᵣrat _ _) ∙
                            (cong rat (ℚ.·Comm (q ℚ.- r)
                            (((fromNat (2 ℕ.+ n)) ℚ^ⁿ suc m) ℚ.· fromNat (2 ℕ.+ m)))))) --
                           )


       in isTrans≡≤ᵣ _ _ _ (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣPos _
            (<ℚ→<ᵣ _ _  (ℚ.<→<minus _ _ (incrF r
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ r∈)
                     q
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ q∈)
                     r<q)))
                 ∙ sym (-ᵣ-rat₂ (q ℚ^ⁿ (2 ℕ.+ m)) (r ℚ^ⁿ (2 ℕ.+ m)))  ∙ cong₂ _-ᵣ_
                   (sym (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) q))
                   (sym (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) r ))) ineqL

  powerUpperLipℚℙ : IsLipschitzWithOn L Sourceℚℙ powℚ
  powerUpperLipℚℙ =
    isLipschitzWithOnOrdered→isLipschitzWithOn L Sourceℚℙ powℚ
      λ q q∈ r r∈ r<q →
        ≤ᵣ→≤ℚ _ _
          (isTrans≡≤ᵣ _ _ _
            (sym (cong absᵣ (-ᵣ-rat₂ (powℚ q) (powℚ r))
              ∙ absᵣ-rat (powℚ q ℚ.- powℚ r)))
            (powerUpperOrdered≤ᵣ q (∈ℚintervalℙ→∈intervalℙ _ _ _ q∈)
              r (∈ℚintervalℙ→∈intervalℙ _ _ _ r∈) r<q))

  powerℚExtended :
    Σ[ f' ∈ (ℚ → ℝ) ]
      (Lipschitz-ℚ→ℝ L f'
      × (∀ x x∈ → f' x ≡ rat (powℚ x)))
  powerℚExtended =
    extend-Lipshitzℚ→ℝ L aℚ bℚ (ℚ.<Weaken≤ _ _ (sqrRestr< n))
      (λ x _ → rat (powℚ x))
      (Lipschitz-ℚ→ℚℙ→Lipschitz-ℚ→ℝℙ L aℚ bℚ powℚ powerUpperLipℚℙ)

  powerℝ-L : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ L)
  powerℝ-L =
    fromLipschitz L (fst powerℚExtended , fst (snd powerℚExtended))

  powerℝ : ℝ → ℝ
  powerℝ = fst powerℝ-L

  powerℝ-lip : Lipschitz-ℝ→ℝ L powerℝ
  powerℝ-lip = snd powerℝ-L

  powerℝ-rat : ∀ x → rat x ∈ Sourceℙ → powerℝ (rat x) ≡ rat (powℚ x)
  powerℝ-rat x x∈ = fromLipschitz-rat ∙ snd (snd powerℚExtended) x x∈

  powerLowerSlope< :
    ∀ q → q ∈ Sourceℚℙ →
    ∀ r → r ∈ Sourceℚℙ →
    r ℚ.< q →
    fst (invℚ₊ K) ℚ.· (q ℚ.- r) ℚ.≤ powℚ q ℚ.- powℚ r
  powerLowerSlope< q q∈ r r∈ r<q =
    let r∈' = ∈ℚintervalℙ→∈intervalℙ _ _ _ r∈
        q∈' = ∈ℚintervalℙ→∈intervalℙ _ _ _ q∈
        0<r : 0 <ᵣ rat r
        0<r = isTrans<≤ᵣ 0 A (rat r) 0<A (fst r∈')
        0<q : 0 <ᵣ rat q
        0<q = isTrans<ᵣ 0 (rat r) (rat q) 0<r (<ℚ→<ᵣ _ _ r<q)
    in ≤ᵣ→≤ℚ _ _
      (isTrans≡≤ᵣ _ _ _
        (cong rat (ℚ.·Comm (fst (invℚ₊ K)) (q ℚ.- r))
          ∙ cong rat
              (cong ((q ℚ.- r) ℚ.·_)
                (ℚ.invℚ₊-ℚ^ⁿ (fromNat (2 ℕ.+ n)) (suc m)))
          ∙ rat·ᵣrat _ _)
        (isTrans≤≡ᵣ _ _ _
          (≤ᵣ-o·ᵣ _ _ _
            (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q)))
            (isTrans≡≤ᵣ _ _ _
              (sym (^ⁿ-ℚ^ⁿ (suc m) (fst (invℚ₊ (fromNat (2 ℕ.+ n))))))
              (Aⁿ≤S (rat r) (rat q) 0<r 0<q
                A B 0<A
                (isTrans≤<ᵣ _ _ _ (fst r∈') (<ℚ→<ᵣ _ _ r<q))
                0<B A<B
                (snd q∈')
                (<ℚ→<ᵣ _ _ r<q))))
          (cong₂ _·ᵣ_ (sym (-ᵣ-rat₂ q r)) refl
            ∙ [b-a]·S≡bⁿ-aⁿ (rat r) (rat q) 0<r 0<q
            ∙ cong₂ _-ᵣ_ (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) q) (^ⁿ-ℚ^ⁿ (2 ℕ.+ m) r)
            ∙ -ᵣ-rat₂ (powℚ q) (powℚ r))))

  powerLowerSlope :
    RootQB.SlopeBoundedBelow (invℚ₊ K)
  powerLowerSlope x x' a≤x x≤x' x'≤b with ℚ.≤→≡⊎< x x' x≤x'
  ... | inl x≡x' =
    subst
      (λ z → fst (invℚ₊ K) ℚ.· (z ℚ.- x) ℚ.≤ powℚ z ℚ.- powℚ x)
      x≡x'
      (ℚ.≡Weaken≤ _ _
        (cong (fst (invℚ₊ K) ℚ.·_) (ℚ.+InvR x)
          ∙ ℚ.·AnnihilR (fst (invℚ₊ K))
          ∙ sym (ℚ.+InvR (powℚ x))))
  ... | inr x<x' =
    powerLowerSlope< x'
      (ℚ.isTrans≤ _ _ _ a≤x x≤x' , x'≤b)
      x
      (a≤x , ℚ.isTrans≤ _ _ _ x≤x' x'≤b)
      x<x'

  module RootInverse = InverseBisection aℚ bℚ (sqrRestr< n) powℚ
  module RootLower = RootInverse.LowerSlope (invℚ₊ K) powerLowerSlope
  module RootReal =
    RootLower.RealFunction L powerℝ powerℝ-lip powerUpperLipℚℙ powerℝ-rat

  rootMap : ℝ → ℝ
  rootMap = powerℝ

  rootInv : ℝ → ℝ
  rootInv = RootLower.inverseℝ

  rootMap∈ : ∀ x → x ∈ Sourceℙ → rootMap x ∈ RootLower.TargetIntervalℙ
  rootMap∈ = RootReal.F∈

  rootInv∈ : ∀ x → x ∈ RootLower.TargetIntervalℙ → rootInv x ∈ Sourceℙ
  rootInv∈ = RootLower.inverseℝ∈

  rootMap-rootInv : ∀ x → x ∈ RootLower.TargetIntervalℙ → rootMap (rootInv x) ≡ x
  rootMap-rootInv = RootReal.F-inverseℝ

  rootInv-rootMap : ∀ x → x ∈ Sourceℙ → rootInv (rootMap x) ≡ x
  rootInv-rootMap = RootReal.inverseℝ-F

  rootInv-cont : IsContinuous rootInv
  rootInv-cont = RootLower.inverseℝ-cont

  rootMap-cont : IsContinuous rootMap
  rootMap-cont = Lipschitz→IsContinuous L rootMap powerℝ-lip




 loB hiB : ∀ n → ℚ
 loB n = (((fst (invℚ₊ (fromNat (2 ℕ.+ n))))) ℚ^ⁿ (2 ℕ.+ m))
 hiB n = ((fromNat (2 ℕ.+ n)) ℚ^ⁿ (2 ℕ.+ m))

 loB-mon : ∀ n → loB (suc n) ℚ.< loB n
 loB-mon n = (
     (ℚ^ⁿ-StrictMonotone (2 ℕ.+ m) (ℕ.suc-≤-suc ℕ.zero-≤)
      (ℚ.0≤ℚ₊ [ 1 / (1+ (suc (suc n))) ]₊) (ℚ.0≤ℚ₊ [ 1 / (1+ (suc n)) ]₊)
      (fst (ℚ.invℚ₊-<-invℚ₊
    (fromNat (2 ℕ.+ n)) (fromNat (3 ℕ.+ n)))
      (<ℤ→<ℚ _ _ (ℤ.pos<pos (ℕ.<ᵗsucm {n}))))))

 hiB-mon : ∀ n → hiB n ℚ.< hiB (suc n)
 hiB-mon n = ℚ^ⁿ-StrictMonotone (2 ℕ.+ m)
        (ℕ.suc-≤-suc ℕ.zero-≤) (ℚ.0≤ℚ₊ [ 1+ (suc n) / 1 ]₊) (ℚ.0≤ℚ₊ ([ (1+ (1 ℕ.+ suc n)) / 1 ]₊))
      (<ℤ→<ℚ _ _ (ℤ.pos<pos (ℕ.<ᵗsucm {n})))

 rootSeq⊆ : Seq⊆
 rootSeq⊆ .Seq⊆.𝕡 n = intervalℙ
   (rat (loB n))
   (rat (hiB n))
 rootSeq⊆ .Seq⊆.𝕡⊆ n x (≤x , x≤) =
   isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (loB-mon n))) ≤x ,
   isTrans≤ᵣ _ _ _ x≤ (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (hiB-mon n)))




 f⊆ : (x : ℝ) (n n' : ℕ) →
      (x∈ : x ∈ intervalℙ (rat (loB n)) (rat (hiB n))) →
      (x∈' : x ∈ intervalℙ (rat (loB n')) (rat (hiB n'))) →
      n ℕ.< n' →
      rootInv n x ≡ rootInv n' x
 f⊆ x n n' x∈ x∈' n<n' =
   sym (rootInv-rootMap n' (rootInv n x) x⁻¹∈ )
    ∙ cong (rootInv n') (rootMap'≡rootMap (rootInv n x) (rootInv∈ n x x∈)
       ∙ rootMap-rootInv n x x∈ )

  where

  opaque
   rootMap'≡rootMap : ∀ y → y ∈ Sourceℙ n → rootMap n' y ≡ rootMap n y
   rootMap'≡rootMap = elimIntervalByClampᵣ _ _
     (≡Continuous _ _
        ((IsContinuous∘ _ _
              (rootMap-cont n')
              (IsContinuousClamp (rat (aℚ n)) _)))
        (IsContinuous∘ _ _
              (rootMap-cont n)
               (IsContinuousClamp (rat (aℚ n)) _))
       λ r → cong (rootMap n') (clampᵣ-rat _ _ _)
         ∙∙ powerℝ-rat n' _ (∈ℚintervalℙ→∈intervalℙ _ _ _ (inClmp' r))
         ∙∙ sym (powerℝ-rat n _
              (∈ℚintervalℙ→∈intervalℙ _ _ _
                (ℚ.clam∈ℚintervalℙ _ _ (ℚ.<Weaken≤ _ _ (sqrRestr< n)) r)))
          ∙ cong (rootMap n) (sym (clampᵣ-rat _ _ _)))
     where
     h : bℚ n ℚ.≤ bℚ n'
     h = ≤ℤ→≤ℚ (pos (suc (suc n))) (pos (suc (suc n')))
           (( ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-k+ {k = 2} (ℕ.<-weaken n<n'))))


     inClmp' : ∀ r → ℚ.clamp (aℚ n) (bℚ n) r
       ∈
       Sourceℚℙ n'
     inClmp' r =
        ℚ.isTrans≤
          (aℚ n')
          (aℚ n)
          (ℚ.clamp (aℚ n) (bℚ n) r)
          (ℚ.invℚ₊≤invℚ₊
            (fromNat (2 ℕ.+ n'))
            (fromNat (2 ℕ.+ n)) h)
           (ℚ.≤clamp (aℚ n) (bℚ n) r (ℚ.<Weaken≤ _ _ (sqrRestr< n)))
        , ℚ.isTrans≤ _
             (bℚ n) _
            (ℚ.clamp≤ (aℚ n) _ r)
            h


  2+n≤ℚ2+n' = ≤ℤ→≤ℚ _ _ ( ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-k+ {k = 2} (ℕ.<-weaken n<n')))

  x⁻¹∈ : rootInv n x ∈ Sourceℙ n'
  x⁻¹∈ =
      isTrans≤ᵣ _ _ _
        (≤ℚ→≤ᵣ _ _
          (ℚ.invℚ₊≤invℚ₊
            (fromNat (2 ℕ.+ n')) (fromNat (2 ℕ.+ n)) 2+n≤ℚ2+n'))
        (fst x∈*)
    , isTrans≤ᵣ _ _ _ (snd x∈*) (≤ℚ→≤ᵣ _ _ 2+n≤ℚ2+n')

   where
   x∈* : rootInv n x ∈ Sourceℙ n
   x∈* = rootInv∈ n x x∈


 opaque

  rootSeq⊆→ : Seq⊆→ ℝ rootSeq⊆
  rootSeq⊆→ .Seq⊆→.fun x n _ = rootInv n x
  rootSeq⊆→ .Seq⊆→.fun⊆ x n m = f⊆ x n m

  getBounds : ∀ x → 0 <ᵣ x → Σ ℚ (λ q → (0 <ᵣ rat q) × (rat q <ᵣ x)) →
       Σ[ M ∈ ℕ₊₁ ] (absᵣ x <ᵣ fromNat (ℕ₊₁→ℕ M)) →
       Σ[ N ∈ ℕ   ] (x ∈ intervalℙ (rat (loB N)) (rat (hiB N)))
  getBounds x 0<x (q , 0<q , q<x) ((1+ M) , x<1+M ) =
     𝑵 , loB≤x , x≤hiB
     -- 𝑵 ,
    -- (loB≤x , x≤hiB)
   where

   q₊ : ℚ₊
   q₊ = (q , <ᵣ→<ℚ _ _ 0<q)

   lo𝑵₊ : ℕ₊₁
   lo𝑵₊ = fst (ℚ.ceilℚ₊ (invℚ₊ q₊))

   lo𝑵 : ℕ
   lo𝑵 = ℕ₊₁→ℕ lo𝑵₊
   hi𝑵 : ℕ
   hi𝑵 = M

   invq<lo𝑵 : fst (invℚ₊ q₊) ℚ.< fromNat lo𝑵
   invq<lo𝑵 = snd (ℚ.ceilℚ₊ (invℚ₊ q₊))

   𝑵 : ℕ
   𝑵 = ℕ.max lo𝑵 hi𝑵

   loB≤q : loB 𝑵 ℚ.≤ q
   loB≤q = subst2 (ℚ._≤_)
      (ℚ.invℚ₊-ℚ^ⁿ (fromNat (2 ℕ.+ 𝑵)) (suc (suc m)) ) (ℚ.invℚ₊-invol q₊)
      (ℚ.invℚ₊≤invℚ₊ (fromNat (2 ℕ.+ 𝑵) ℚ₊^ⁿ suc (suc m)) (invℚ₊ q₊)
       (ℚ.isTrans≤ (fst (invℚ₊ q₊)) _ _
         (ℚ.<Weaken≤ _ _ invq<lo𝑵)
          (ℚ.isTrans≤ _ _ _
            (ℚ.isTrans≤ _ _ _ (≤ℤ→≤ℚ _ _

              (ℤ.ℕ≤→pos-≤-pos
                  _ _ (subst (ℕ._≤ (lo𝑵 ℕ.^ suc (suc m)))
                    (ℕ.·-identityʳ lo𝑵)
                     ((ℕ.^-monotone lo𝑵 0 (suc m) ℕ.zero-≤))))
                     )
              (ℚ.≡Weaken≤ (fromNat (lo𝑵 ℕ.^ suc (suc m)))
                ((fromNat lo𝑵 ℚ^ⁿ (2 ℕ.+ m)))
                 (sym ((ℚ.fromNat-^ lo𝑵 (suc (suc m)))))))
            (ℚ^ⁿ-Monotone {fromNat lo𝑵} (suc (suc m))
              (≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
              (≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
              (((≤ℤ→≤ℚ _ _

               (ℤ.ℕ≤→pos-≤-pos _ _
               (ℕ.≤-trans (ℕ.≤-suc (ℕ.≤-suc ℕ.≤-refl))
                (ℕ.≤-k+ {_} {_} {2} (ℕ.left-≤-max {lo𝑵} {hi𝑵}))
                ))
            )))))
           ))

   loB≤x : rat (loB 𝑵) ≤ᵣ x
   loB≤x = isTrans≤ᵣ _ _ _
     (≤ℚ→≤ᵣ _ _ loB≤q)
       (<ᵣWeaken≤ᵣ _ _ q<x)

   1+M≤hiB : fromNat (suc M) ℚ.≤ (hiB M)
   1+M≤hiB =
    subst (fromNat (suc M) ℚ.≤_) (sym (ℚ.fromNat-^ (2 ℕ.+ M) (suc (suc m))))
     ((≤ℤ→≤ℚ (pos (suc M)) (pos ((2 ℕ.+ M) ℕ.^ suc (suc m))) (ℤ.ℕ≤→pos-≤-pos _ _
       (ℕ.≤-trans (ℕ.≤-suc ℕ.≤-refl) (subst (ℕ._≤ (suc (suc M) ℕ.^ suc (suc m)))
           (sym (cong (suc ∘ suc) (sym (·-identityʳ M))))
            (ℕ.^-monotone (suc (suc M)) 0 (suc m) ℕ.zero-≤ )))
       )))


   x≤hiB : x ≤ᵣ rat (hiB 𝑵)
   x≤hiB =
    isTrans≡≤ᵣ _ _ _  (sym (absᵣPos _ 0<x))
       (isTrans≤ᵣ _ _ _
        (<ᵣWeaken≤ᵣ _ _ x<1+M)
          ((≤ℚ→≤ᵣ _ _ (ℚ.isTrans≤ (fromNat (suc M)) _ _ 1+M≤hiB
            ((ℚ^ⁿ-Monotone (suc (suc m))
               (≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤)) (≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤))
             (≤ℤ→≤ℚ _ _
              (ℤ.ℕ≤→pos-≤-pos _ _
              (ℕ.≤-k+ {_} {_} {2} ((ℕ.right-≤-max {(hi𝑵)} {(lo𝑵)})))))))))))

  ℝ₊⊆rootSeq : rootSeq⊆ Seq⊆.s⊇ (pred> 0)
  ℝ₊⊆rootSeq x 0<x =
    PT.map2
      (getBounds x 0<x)
       (denseℚinℝ _ _ 0<x)
       (getClamps x)


  0<root : (x : ℝ) (n : ℕ)
      (x∈ : x ∈ intervalℙ (rat (loB n)) (rat (hiB n))) →
      rat [ pos 0 / 1+ 0 ] <ᵣ rootInv n x
  0<root x n x∈ =
    isTrans<≤ᵣ _ _ _
      (<ℚ→<ᵣ _ _ (snd (invℚ₊ ([  (1+ (suc n)) / 1 ]₊))))
      (fst (rootInv∈ n x x∈))

  rootSeq⊆→-fun : ∀ {n x y} → rootSeq⊆→ .Seq⊆→.fun x n y ≡ rootInv n x
  rootSeq⊆→-fun = refl

 open Seq⊆→.FromIntersection rootSeq⊆→ isSetℝ (pred> 0) ℝ₊⊆rootSeq public

 opaque

  𝒇=f : ∀ n x → x ∈ intervalℙ
                      (rat (fst (invℚ₊ ([  (1+ (suc n)) / 1 ]₊))))
                      (rat (fromNat (2 ℕ.+ n)))  →
           (x ^ⁿ (suc (suc m))) ≡ rootMap n x
  𝒇=f n = elimIntervalByClampᵣ (rat (aℚ n)) (rat (bℚ n))
   (≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuous^ⁿ (suc (suc m)) ) (IsContinuousClamp (rat _) (rat _)))
        (IsContinuous∘ _ _ (rootMap-cont n) (IsContinuousClamp (rat _) (rat _)))
       λ r →  cong (_^ⁿ suc (suc m)) ((clampᵣ-rat _ _ _))
          ∙ ^ⁿ-ℚ^ⁿ (suc (suc m)) _
          ∙ sym (powerℝ-rat n _
              (∈ℚintervalℙ→∈intervalℙ _ _ _
                (ℚ.clam∈ℚintervalℙ _ _ (ℚ.<Weaken≤ _ _ (sqrRestr< n)) r)))
          ∙ cong (rootMap n) (sym (clampᵣ-rat _ _ _)))



 bounds⊂ : (n : ℕ) (x : ℝ) →
      x ∈ (λ z → Seq⊆.𝕡 rootSeq⊆ n z) →
      ∃-syntax ℚ₊
      (λ δ →
         (y : ℝ) → x ∼[ δ ] y → y ∈ (λ z → Seq⊆.𝕡 rootSeq⊆ (suc n) z))
 bounds⊂ n x (lo<x , x<hi)  = ∣ δ
         , (λ y → (λ abs< →
             let u =
                       isTrans≤ᵣ (x -ᵣ y) _
                         (rat (loB n ℚ.- loB (suc n)))
                         (≤absᵣ (x -ᵣ y))
                         (<ᵣWeaken≤ᵣ (absᵣ (x -ᵣ y)) _
                           (isTrans<≤ᵣ _ (rat (fst δ)) _ abs<
                             (≤ℚ→≤ᵣ _ _ (ℚ.min≤ _ _))))
                 v =
                       isTrans≤ᵣ (y -ᵣ x) _
                         (rat (hiB (suc n) ℚ.- hiB n))
                         (≤absᵣ (y -ᵣ x))
                         (isTrans≡≤ᵣ _ _ _ (minusComm-absᵣ _ _)
                           (<ᵣWeaken≤ᵣ (absᵣ (x -ᵣ y)) _
                             (isTrans<≤ᵣ _ _ _ abs<
                               (≤ℚ→≤ᵣ _ _
                                 (ℚ.min≤' (loB n ℚ.- loB (suc n))
                                   (hiB (suc n) ℚ.- hiB n))))))
             in  subst2 _≤ᵣ_ ℝ! ℝ!
                    (≤ᵣMonotone+ᵣ _ _ _ _
                       lo<x (-ᵣ≤ᵣ _ _ (isTrans≤≡ᵣ _ _ _ u (sym (-ᵣ-rat₂  (loB n) (loB (suc n))) ))))
                    , subst2 _≤ᵣ_ ℝ! ℝ!
                          (isTrans≤≡ᵣ _ _ _ (≤ᵣMonotone+ᵣ _ _ _ _
                             v x<hi) (cong (_+ᵣ rat (hiB n)) (sym (-ᵣ-rat₂ (hiB (suc n)) (hiB n))))))
                              ∘ fst (∼≃abs<ε _ _ _)) ∣₁
  where
  δ = min₊ (ℚ.<→ℚ₊ _ _ (loB-mon n))
                        (ℚ.<→ℚ₊ _ _ (hiB-mon n))
 opaque
  nth-root : ℝ₊ → ℝ₊
  nth-root (x , 0<x) =
      ∩$ x 0<x
    , ∩$-elimProp x 0<x {B = λ y → 0 <ᵣ y} (λ _ → isProp<ᵣ _ _)
       λ n x∈ → isTrans<≡ᵣ _ _ _ (0<root x n x∈) (sym rootSeq⊆→-fun)


  nth-root-impl-fst : ∀ x 0<x → fst (nth-root (x , 0<x)) ≡ ∩$ x 0<x
  nth-root-impl-fst _ _ = refl

  ^ⁿ∘ⁿ√ : ∀ x 0<x → (fst (nth-root (x , 0<x)) ^ⁿ (2 ℕ.+ m)) ≡ x
  ^ⁿ∘ⁿ√ x 0<x = ∩$-elimProp x 0<x
    {B = λ a → (a ^ⁿ (2 ℕ.+ m)) ≡ x}
    (λ _ → isSetℝ _ _)
      λ n x∈ →
           cong (_^ⁿ (2 ℕ.+ m)) rootSeq⊆→-fun ∙ 𝒇=f _ _ (rootInv∈ n x x∈)
        ∙ rootMap-rootInv n x x∈

  ⁿ√∘^ⁿ : ∀ x 0<x → fst (nth-root ((x , 0<x) ₊^ⁿ (2 ℕ.+ m))) ≡ x
  ⁿ√∘^ⁿ x 0<x = (∩$-elimProp _ (snd ((x , 0<x) ₊^ⁿ (2 ℕ.+ m)))
    {B = λ a → a ≡ x}
    (λ a → isSetℝ a x)
     λ n x∈' →
      let 0<n : 1 ℕ.≤ suc (suc m)
          0<n = ℕ.suc-≤-suc ℕ.zero-≤
          zzs : rat (fst (invℚ₊ ([ (1+ (suc n)) / 1 ]₊))) ≤ᵣ x
          zzs = (^ⁿMonotone⁻¹ (suc (suc m)) 0<n
                 (0<A n) 0<x (isTrans≡≤ᵣ _ _ _ (^ⁿ-ℚ^ⁿ (suc (suc m))
                  (fst (invℚ₊ ([ (1+ (suc n)) / 1 ]₊)))) (fst x∈')))

          zzss : x ≤ᵣ rat [ pos (suc (suc n)) / 1+ 0 ]
          zzss = (^ⁿMonotone⁻¹ (suc (suc m)) 0<n 0<x (0<B n)
                     (isTrans≤≡ᵣ _ _ _ (snd x∈') (sym (^ⁿ-ℚ^ⁿ (suc (suc m)) (fromNat (2 ℕ.+ n))))))
          x∈ : (rat (fst (invℚ₊ ([  (1+ (suc n)) / 1 ]₊))) ≤ᵣ x) ×
               (x ≤ᵣ rat (fromNat (2 ℕ.+ n)))
          x∈ =  zzs , zzss




      in rootSeq⊆→-fun ∙ cong (rootInv n)
                 (𝒇=f n x x∈)
                ∙ rootInv-rootMap n x x∈)

  opaque
   unfolding rootSeq⊆→
   nth-root-cont : IsContinuousWithPred
           (pred> 0) (curry (fst ∘ nth-root))
   nth-root-cont = ∩$-cont' (pred> 0) rootSeq⊆
      bounds⊂ rootSeq⊆→ ℝ₊⊆rootSeq
       λ n → AsContinuousWithPred (Seq⊆.𝕡 rootSeq⊆ n) _
                (rootInv-cont n)

  ℚApproxℙ-nth-root : ℚApproxℙ'
                          (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                          (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                          (curry (nth-root))
  ℚApproxℙ-nth-root q q∈ =
   let q₊ = (q , <ᵣ→<ℚ _ _ q∈)
       (m , q<m) = ℚ.ceilℚ₊ q₊
       (n' , q∈') = getBounds (rat q) q∈
          (fst (q₊ /2₊) ,
            snd (ℚ₊→ℝ₊ (q₊ /2₊))
              , <ℚ→<ᵣ _ _ (/2₊<id q₊))
               (1+ (ℕ₊₁→ℕ m) , isTrans<ᵣ _ _ _
                   (isTrans≡<ᵣ _ _ _
                     (absᵣPos _ (snd (ℚ₊→ℝ₊ q₊)))
                     (<ℚ→<ᵣ _ _ q<m))
                   (<ℚ→<ᵣ _ _ (<ℤ→<ℚ _ _
                     (ℤ.pos<pos (ℕ.<ᵗsucm {ℕ₊₁→ℕ m})))))
       (a , b , c , d) =
          RootLower.inverseℝ-ℚApproxℙ n' q q∈'
   in a , (λ ε →
      isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (2 ℕ.+ _)))))
         (fst (b ε))) , c ,
      d
      ∙ sym rootSeq⊆→-fun ∙ sym (∩$-∈ₙ (rat q) q∈ n' q∈')


 nth-pow-root-iso₊₂ : Iso ℝ₊ ℝ₊
 nth-pow-root-iso₊₂ .Iso.fun x = x ₊^ⁿ (2 ℕ.+ m)
 nth-pow-root-iso₊₂ .Iso.inv = nth-root
 nth-pow-root-iso₊₂ .Iso.sec =
   ℝ₊≡ ∘ uncurry ^ⁿ∘ⁿ√
 nth-pow-root-iso₊₂ .Iso.ret =
   ℝ₊≡ ∘ uncurry ⁿ√∘^ⁿ


root : ℕ₊₁ → ℝ₊ →  ℝ₊
root one x = x
root (2+ n) x = NthRoot.nth-root n x

ℚApproxℙ-root : ∀ n → ℚApproxℙ'
                        (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                        (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                        (curry ((root n)))
ℚApproxℙ-root one q q∈ = (λ _ → q) , (λ _ → q∈) , (λ _ _ → refl∼ _ _) , limConstRat _ _

ℚApproxℙ-root (2+ n) = NthRoot.ℚApproxℙ-nth-root n

IsContinuousRoot : ∀ n → IsContinuousWithPred
         (λ x → _ , isProp<ᵣ _ _)
         λ x 0<x → fst (root n (x , 0<x))
IsContinuousRoot one =
  AsContinuousWithPred (pred> 0) _ IsContinuousId
IsContinuousRoot (2+ n) = NthRoot.nth-root-cont n


nth-pow-root-iso : ℕ₊₁ → Iso ℝ₊ ℝ₊
nth-pow-root-iso k .Iso.fun x = x ₊^ⁿ ℕ₊₁→ℕ k
nth-pow-root-iso k .Iso.inv = root k
nth-pow-root-iso one .Iso.sec _ = ℝ₊≡ (·IdR _)
nth-pow-root-iso (2+ n) .Iso.sec = Iso.sec
  (NthRoot.nth-pow-root-iso₊₂ n)
nth-pow-root-iso one .Iso.ret _ = ℝ₊≡ (·IdR _)
nth-pow-root-iso (2+ n) .Iso.ret = Iso.ret
  (NthRoot.nth-pow-root-iso₊₂ n)

opaque
  ^ⁿ∘root : ∀ n x → fst (root n x) ^ⁿ ℕ₊₁→ℕ n ≡ fst x
  ^ⁿ∘root n x = cong fst (Iso.sec (nth-pow-root-iso n) x)


isEquiv-₊^ⁿ : ∀ n → isEquiv (_₊^ⁿ ℕ₊₁→ℕ n)
isEquiv-₊^ⁿ n = isoToIsEquiv (nth-pow-root-iso n)
