module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.StrictMonotonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
import Cubical.Data.Int.Fast.Properties as ℤP
import Cubical.Data.Int.Base as ℤStd
import Cubical.Data.Int.Properties as ℤStdP
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (invℚ)

import Cubical.Algebra.OrderedCommRing.Properties as OCRP
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using (ℚOrderedCommRing)

module ℚO = OCRP.OrderedCommRingTheory ℚOrderedCommRing


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.Tactics.CauchyReals.ExpressionLifting

open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary using
  (seqΔ-δ; lnSeq; lnSeq'; lnSeqCont; fromSucℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Limit

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR

open import Cubical.Algebra.Group.DirProd
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Construction

open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition

rootₙ→1 : ∀ x (α : ℝ) → 1 <ᵣ α →
         ∃[ N ∈ ℕ ]
           (∀ n → N ℕ.< n → fst (root (1+ n) x) <ᵣ α)
rootₙ→1 x α 1<α =
  PT.rec squash₁ w
    (IsContinuousLim _ 0 (cont-^ x) (α -ᵣ 1 , x<y→0<y-x _ _ 1<α))
 where
 w : Σ ℝ₊
      (λ δ →
         (r : ℝ) (x＃r : 0 ＃ r) →
         absᵣ (0 -ᵣ r) <ᵣ fst δ →
         absᵣ (fst (x ^ᵣ 0) -ᵣ fst (x ^ᵣ r))
         <ᵣ α -ᵣ 1) →
      ∃ ℕ (λ N → (n : ℕ) → N ℕ.< n → fst (root (1+ n) x) <ᵣ α)
 w ((δᵣ , 0<δᵣ) , X) =
    PT.map
      (λ (δ , 0<δ , δ<δᵣ) →
        let 1/δ = (invℚ₊ (δ , <ᵣ→<ℚ _ _ 0<δ))
            ((1+ k) , Y) = ℚ.boundℕ (fst 1/δ)
        in suc k , λ n <n →
            <-+o-cancel _ _ (-ᵣ 1)
              (isTrans≤<ᵣ _ _ _
                (≤absᵣ _) (isTrans≡<ᵣ _ _ _
               (cong absᵣ (cong₂ _-ᵣ_
                (sym (^ᵣ[1/n] x (1+ n)))
                (sym (^ᵣ0 x)))
                ∙ minusComm-absᵣ _ _) (X (rat [ 1 / 1+ n ])
            (inl (<ℚ→<ᵣ _ _ (0<pos _ _)))
             (isTrans≡<ᵣ _ _ _ (
              cong absᵣ (+IdL _) ∙ sym (-absᵣ _)
                ∙ absᵣPos _ (<ℚ→<ᵣ _ _ (0<pos _ _))) (isTrans<ᵣ _ _ _
              (<ℚ→<ᵣ [ 1 / 1+ n ] δ
                (subst2 ℚ._<_
                  refl
                  (ℚ.invℚ₊-invol _)
                  (fst (ℚ.invℚ₊-<-invℚ₊ 1/δ (fromNat (suc n)) )
                   (ℚ.isTrans< _ _ _
                     (ℚ.isTrans≤< _ _ _ (≤abs (fst 1/δ)) Y)
                     (<ℤ→<ℚ _ _ (ℤ.ℕ<→pos-<-pos _ _ (ℕ.≤-suc <n))))))) δ<δᵣ)))))
        )
      (denseℚinℝ 0 δᵣ 0<δᵣ)

opaque
 unfolding maxᵣ
 ℚ-clamp-<-cases : ∀ L L' x y → L ℚ.< L' → x ℚ.< y →
                     (ℚ.clamp L L' x ≡ ℚ.clamp L L' y) ⊎
                        (ℚ.clamp L L' x ℚ.< ℚ.clamp L L' y)
 ℚ-clamp-<-cases L L' x y L<L' x<y =
   let clamp≤ = ℚ.≤MonotoneClamp L L' x y
         (ℚ.<Weaken≤ x y x<y)
   in ⊎.rec
        (λ reverse-clamp≤ → inl
          (ℚ.isAntisym≤
            (ℚ.clamp L L' x) (ℚ.clamp L L' y)
            clamp≤ reverse-clamp≤))
        inr
        (ℚ.Dichotomyℚ (ℚ.clamp L L' y) (ℚ.clamp L L' x))

 ℚ-clamp-<-casesᵣ : ∀ L L' x y → L ℚ.< L' →  x ℚ.< y →
                     (clampᵣ (rat L) (rat L') (rat x)
                       ≡ clampᵣ (rat L) (rat L') (rat y)) ⊎
                        (clampᵣ (rat L) (rat L') (rat x)
                         <ᵣ clampᵣ (rat L) (rat L') (rat y))
 ℚ-clamp-<-casesᵣ L L' x y L<L' x<y =
  (⊎.map
     (λ p → clampᵣ-rat L L' x ∙ cong rat p ∙ sym (clampᵣ-rat L L' y))
     (λ p → subst2 _<ᵣ_
       (sym (clampᵣ-rat L L' x))
       (sym (clampᵣ-rat L L' y))
       (<ℚ→<ᵣ _ _ p))
     (ℚ-clamp-<-cases L L' x y L<L' x<y))

eventually-lnSeq[x]<lnSeq'[x+Δ] : ∀ (x Δ : ℝ₊) → 1 <ᵣ fst x →
  ∃[ k ∈ ℕ ] lnSeq x k <ᵣ lnSeq' (x ₊+ᵣ Δ) k
eventually-lnSeq[x]<lnSeq'[x+Δ] x Δ 1<x =
   PT.map w
     (rootₙ→1 x α 1<α)

 where


 0<1-1/[x+Δ] = (isTrans<≡ᵣ _ _ _
          (invEq (invℝ₊-<-invℝ₊ _ 1)
            (isTrans≡<ᵣ _ _ _
              (sym (+IdR _))
              (<ᵣMonotone+ᵣ _ _ _ _ 1<x (snd Δ)))) (cong fst invℝ₊1) )


 0<1-1/x = (isTrans<≡ᵣ _ _ _
          (invEq (invℝ₊-<-invℝ₊ _ 1)
            (isTrans≡<ᵣ _ _ _
              (sym (+IdR _) ∙ (+ᵣ-rat _ _))
              1<x)) (cong fst invℝ₊1) )


 α : ℝ
 α = (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ)))
      ／ᵣ₊ (_ , x<y→0<y-x _ _ 0<1-1/x)

 1<α : 1 <ᵣ α
 1<α = invEq (1<x/y≃y<x _ _)
   (<ᵣ-o+ _ _ 1
     (-ᵣ<ᵣ _ _ (invEq (invℝ₊-<-invℝ₊ _ _)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _))
         (<ᵣ-o+ _ _ (fst x) (snd Δ))))))



 w : Σ ℕ
      (λ N → (n : ℕ) → N ℕ.< n → fst (root (1+ n) x) <ᵣ α) →
      Σ ℕ (λ k → lnSeq x k <ᵣ lnSeq' (x ₊+ᵣ Δ) k)
 w (K , X) =
   K , <ᵣ-·ᵣo _ _ (_ , <ℚ→<ᵣ _ _ (0<pos _ _))
     (isTrans<≤ᵣ _ _ _
       (isTrans≡<ᵣ _ _ _
         (cong₂ _-ᵣ_
           (^ⁿ-1 (fst (root (1+ suc K) x))
             ∙ sym (·IdLᵣ (fst (root (1+ suc K) x))))
           (cong fst
             (sym (ₙ√1 (1+ suc K))
             ∙∙ cong (root (1+ suc K))
               (ℝ₊≡
                 (sym (x·invℝ₊[x] x)
                 ∙ ·ᵣComm (fst x) (fst (invℝ₊ x))))
             ∙∙ sym (·DistRoot (invℝ₊ x) x (1+ suc K))))
           ∙ sym (Rℝ.·DistL-
             1 (fst (root (1+ suc K) (invℝ₊ x)))
             (fst (root (1+ suc K) x))))
         (<ᵣ-o·ᵣ _ _
           (_ , x<y→0<y-x (fst (root (1+ (suc K)) (invℝ₊ x))) 1
              (isTrans<≡ᵣ _ _ _
               (ₙ√-StrictMonotone {invℝ₊ x} {1}  (1+ suc K)
                 (invEq (1/x<1≃1<x x) 1<x))
               (cong fst (ₙ√1 (1+ suc K)))))
           (X (suc K) (ℕ.≤-refl {suc K}))))
       from-concave)

  where

  from-concave :
    (1 -ᵣ fst (root (2+ K) (invℝ₊ x))) ·ᵣ α ≤ᵣ
     1 -ᵣ fst ((x ₊+ᵣ Δ) ^ℚ (ℚ.- [ 1 / 2+ K ]))
  from-concave = isTrans≡≤ᵣ (_ ·ᵣ α) _ _
        (cong₂ (_·ᵣ_)
           (cong₂ _-ᵣ_
             (cong fst (sym (ₙ√1 (1+ suc K)))) refl)
           (·ᵣComm
             (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ)))
             (fst (invℝ₊
               (1 -ᵣ fst (invℝ₊ x) ,
                x<y→0<y-x _ _ 0<1-1/x))))
         ∙ ·ᵣAssoc
             (fst (root (1+ suc K) 1)
               -ᵣ fst (root (1+ suc K) (invℝ₊ x)))
             (fst (invℝ₊
               (1 -ᵣ fst (invℝ₊ x) ,
                x<y→0<y-x _ _ 0<1-1/x)))
             (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ)))
         ∙ ·ᵣComm
             ((fst (root (1+ suc K) 1)
                 -ᵣ fst (root (1+ suc K) (invℝ₊ x)))
               ·ᵣ fst (invℝ₊
                 (1 -ᵣ fst (invℝ₊ x) ,
                  x<y→0<y-x _ _ 0<1-1/x)))
             (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ))))
        (isTrans≤≡ᵣ _ _ _ (fst (z≤x/y₊≃y₊·z≤x _ _ _) (slope-monotone-ₙ√ (suc K)
         (invℝ₊ (x ₊+ᵣ Δ)) 1
         (invℝ₊ x) 1
         0<1-1/[x+Δ]
         0<1-1/x
         (invEq (invℝ₊-≤-invℝ₊ _ _)
           (isTrans≡≤ᵣ _ _ _ (sym (+IdR _))
            (≤ᵣ-o+ _ _ (fst x) (<ᵣWeaken≤ᵣ _ _ (snd Δ)))))
            (≤ᵣ-refl 1)))
            (cong₂ _-ᵣ_
              (cong fst (ₙ√1 (1+ suc K)))
              (sym (^ⁿ-1
                (fst (root (1+ suc K) (invℝ₊ (x ₊+ᵣ Δ)))))
              ∙ cong fst
                (sym (^ℚ-minus'
                  (x ₊+ᵣ Δ) [ 1 / 2+ K ])))))




monotoneStrictPreLn : ∀ Z → (z z' : ℝ₊) → 1 <ᵣ fst z →
         (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
         (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
         (z'≤Z : fst z' ≤ᵣ fromNat (suc (suc Z)))
         (1/Z≤z' :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z')
         → fst z <ᵣ fst z'
         → expPreDer.expPreDer'.preLn Z z z≤Z 1/Z≤z  <ᵣ
           expPreDer.expPreDer'.preLn Z z' z'≤Z 1/Z≤z'
monotoneStrictPreLn Z z z' 1<z z≤Z 1/Z≤z z'≤Z 1/Z≤z' z<z' =
  PT.rec (isProp<ᵣ _ _)
    (λ (K , X) →
       isTrans<≤ᵣ _ _ _
         (isTrans≤<ᵣ _ _ _
           (BDL.preLn≤lnSeq z Z z≤Z 1/Z≤z K) X)

         ((isTrans≡≤ᵣ _ _ _
          (cong (λ zz → lnSeq' zz K) (ℝ₊≡ ℝ!) )
          (BDL.lnSeq'≤preLn z' Z z'≤Z 1/Z≤z' K)))
          )
    (eventually-lnSeq[x]<lnSeq'[x+Δ]
      z (fst z' +ᵣ -ᵣ fst z , x<y→0<y-x _ _ z<z' )
      1<z)


ln-mon-str-1< :
   ∀ (y y' : ℝ₊)
   → 1 <ᵣ fst y
   → fst y <ᵣ fst y'
   → ln y <ᵣ ln y'
ln-mon-str-1< y y' 1<y y<y' =
  Seq-^-FI.∩$-elimProp2  (fst y) (snd y) (fst y') (snd y')
  {B = λ (_ , ln-y) (_ , ln-y') → ln-y <ᵣ ln-y'}
  (λ _ _ → isProp<ᵣ _ _)
  λ Z x∈ y∈ →
    let 0<y-stage =
          isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc Z)) ]) (fst y)
            (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst x∈)
        0<y'-stage =
          isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc Z)) ]) (fst y')
            (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst y∈)
        seq-y-path = Seq-^-fun-snd≡BDL-with
          (fst y) Z x∈ 0<y-stage
        seq-y'-path = Seq-^-fun-snd≡BDL-with
          (fst y') Z y∈ 0<y'-stage
        strict = monotoneStrictPreLn Z
          (fst y , 0<y-stage) (fst y' , 0<y'-stage)
          1<y (snd x∈) (fst x∈) (snd y∈) (fst y∈) y<y'
    in subst2 _<ᵣ_ (sym seq-y-path) (sym seq-y'-path) strict
