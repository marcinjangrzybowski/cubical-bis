-- {-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative using
  ( IsUContinuous
  ; IsUContinuous∘ℙ
  ; IsUContinuousℙ∘ℙ
  ; Lipschitiz→IsUContinuous
  ; restrIsUContinuousℙ
  ; ℚε/2+ε/2≡ε
  ; ·ᵣ-∼
  ; Bounded
  )
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.RationalsImports

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
 invℚ₊ : ℚ₊ → ℚ₊
 invℚ₊ = ℚ._⁻¹₊

-- Integration, exponential/trigonometric applications, and nth-root material
-- that used to live here are preserved temporarily in
-- Cubical.HITs.CauchyReals.PreviouslyInUniform.  This module now contains the
-- dependency-light uniform-continuity and uniform-convergence infrastructure.

opaque
 unfolding maxᵣ
 x∈interval-bound : ∀ a b → ∀ x (x∈ : x ∈ intervalℙ a b) →
                    absᵣ x ≤ᵣ maxᵣ (absᵣ a) (absᵣ b)
 x∈interval-bound a b x (a≤x , x≤b) =
    isTrans≡≤ᵣ _ _ _ (abs-max x)
      (max≤-lem _ _ _
        ((isTrans≤ᵣ _ _ _
          x≤b
          (isTrans≤ᵣ _ _ _
            (≤absᵣ _) (isTrans≤≡ᵣ _ _ _ (≤maxᵣ _ _) (maxᵣComm _ _)))))
        (isTrans≤ᵣ _ _ _
          (-ᵣ≤ᵣ  _ _ a≤x)
          (isTrans≤ᵣ _ _ _
            (≤absᵣ _) (isTrans≡≤ᵣ _ _ _ (sym (-absᵣ _)) (≤maxᵣ _ _)))))


<ε-lemma : ∀ x (y : ℝ)  (ε y' : ℚ₊)
                   → absᵣ y <ᵣ rat (fst y')
                   → absᵣ x <ᵣ rat (fst ε ℚ.· fst (invℚ₊ y'))
                   → absᵣ (x ·ᵣ y)  <ᵣ rat (fst ε)
<ε-lemma x y ε y' ∣y∣<y' ∣x∣<ε/y' =
  let z = <ᵣ₊Monotone·ᵣ _ _ _ _ (0≤absᵣ _) (0≤absᵣ _)
              ∣x∣<ε/y' ∣y∣<y'
   in subst2 _<ᵣ_
         (sym (·absᵣ _ _))
         (sym (rat·ᵣrat _ _)
        ∙ cong rat ℚ!)
         z

IsUContinuousℙ·ᵣ₂ : ∀ P f g →
   Bounded P f →
   Bounded P g →
   IsUContinuousℙ P f →
   IsUContinuousℙ P g →
   IsUContinuousℙ P λ x x∈ → f x x∈ ·ᵣ g x x∈
IsUContinuousℙ·ᵣ₂ P f g (bf , <bf) (bg , <bg) fuc guc ε =
  let δ  , X  = fuc (ε /2₊ ·₊ (invℚ₊ bg))
      δ' , X' = guc (ε /2₊  ·₊ (invℚ₊ bf))

  in min₊ δ δ' ,
    λ u v u∈ v∈ u∼v → subst∼ {ε = fst ( (ε /2₊) +₊  (ε /2₊))} {snd ( (ε /2₊) +₊  (ε /2₊))}
           {ε' = fst ε} ℚ!! $
      let Y = isTrans≡<ᵣ _ _ _ (cong absᵣ (sym (Rℝ.·DistL- _ _ _))
             ∙ ·absᵣ _ _)
            (isTrans≤<ᵣ _ _ _
              (((≤ᵣ-o·ᵣ _ _ _ (0≤absᵣ _) (<bg u u∈))))
              (isTrans≡<ᵣ _ _ _ (·ᵣComm _ _)
               $ fst (z<x/y₊≃y₊·z<x _ _ _) (isTrans<≡ᵣ _ _ _
              (fst (∼≃abs<ε _ _ _) $ X u v u∈ v∈
                  (∼-monotone≤ (ℚ.min≤ (fst δ) (fst δ')) u∼v))
              (rat·ᵣrat (fst (ε /2₊)) _ ∙ cong₂ _·ᵣ_ refl
                (sym (invℝ₊-rat bg))))))

          Y' = isTrans≡<ᵣ _ _ _ (cong absᵣ (sym (Rℝ.·DistR- _ _ _))
             ∙ (·absᵣ _ _))
            (isTrans≤<ᵣ _ _ _
              (≤ᵣ-·ᵣo _ _ _ (0≤absᵣ _) (<bf v v∈))
              (fst (z<x/y₊≃y₊·z<x _ _ _) (isTrans<≡ᵣ _ _ _
              (fst (∼≃abs<ε _ _ _) $ X' u v u∈ v∈
              (∼-monotone≤ (ℚ.min≤' (fst δ) (fst δ')) u∼v))
              (rat·ᵣrat (fst ε ℚ.· [ pos 1 / 1+ 1 ]) _ ∙ cong₂ _·ᵣ_ refl
                (sym (invℝ₊-rat bf))))))
      in invEq (∼≃abs<ε _ _ _)
         (isTrans≤<ᵣ _ _ _
           (isTrans≡≤ᵣ _ _ _
             (cong absᵣ ℝ!)
             (absᵣ-triangle _ _))
           (isTrans<≡ᵣ _ _ _
             (<ᵣMonotone+ᵣ _ _ _ _
             Y
             Y')
             (+ᵣ-rat _ _)))


IsUContinuousℙC·ᵣ : ∀ P (C : ℚ) f → IsUContinuousℙ P f →
   IsUContinuousℙ P λ x x∈ → f x x∈ ·ᵣ rat C
IsUContinuousℙC·ᵣ P C f X =
  map-snd (λ X u v u∈ v∈ → ·ᵣ-∼ _ _ _ _ _
   (isTrans≡≤ᵣ _ _ _
     (absᵣ-rat C ∙ cong rat (sym (ℚ.+IdR _)))
     (≤ℚ→≤ᵣ _ _ (ℚ.≤-o+ _ _ (abs C) (ℚ.decℚ≤? {0} {1}))))
    ∘ X u v u∈ v∈ )
    ∘ X ∘ (_·₊ invℚ₊ (abs C ℚ.+ 1 ,
      (ℚ.≤<Monotone+ 0 _ 0 _
        (0≤abs C) (ℚ.decℚ<? {0} {1}))))


IsUContinuousℙ-ᵣ∘ : ∀ P f → IsUContinuousℙ P f →
   IsUContinuousℙ P λ x x∈ → -ᵣ (f x x∈)
IsUContinuousℙ-ᵣ∘ P f X =
 subst (IsUContinuousℙ P)
   (funExt₂ λ _ _ → ·ᵣComm _ _ ∙ sym (-ᵣ≡[-1·ᵣ] _)) (IsUContinuousℙC·ᵣ P -1 f X)





IsUContinuousId : IsUContinuous (idfun _)
IsUContinuousId = _, λ _ _ → idfun _

IsUContinuousConst : ∀ C → IsUContinuous (λ _ → C)
IsUContinuousConst C ε = 1 , λ _ _ _ → refl∼ _ _

IsUContinuousℙ-const : ∀ P C → IsUContinuousℙ P λ _ _ → C
IsUContinuousℙ-const P C ε = 1 , λ _ _ _ _ _ → refl∼ _ _

IsUContinuousℙ-transl : ∀ P Δ f
 → IsUContinuousℙ (P ∘ (_-ᵣ Δ)) f
 → IsUContinuousℙ P λ x x∈ → f (x +ᵣ Δ) (subst-∈ P (sym (Rℝ.plusMinus _ _)) x∈)
IsUContinuousℙ-transl P Δ f =
 map-snd (λ X u v u∈ v∈ u∼v →
   X _ _ _ _ (+ᵣ-∼ _ _ _ _ u∼v)) ∘_

IsUContinuousℙ+ᵣ₂ : ∀ P f g → IsUContinuousℙ P f → IsUContinuousℙ P g →
   IsUContinuousℙ P λ x x∈ → f x x∈ +ᵣ g x x∈
IsUContinuousℙ+ᵣ₂ P f g fuc guc ε =
  let (δ , X) = fuc (ε /2₊)
      (δ' , X') = guc (ε /2₊)
  in min₊ δ δ' ,
      λ u v u∈ v∈ u∼v →
       subst∼ ℚ!!
         (triangle∼
            (+ᵣ-∼ _ _ _ (ε /2₊)
             (X u v u∈ v∈ (∼-monotone≤ (ℚ.min≤ _ _) u∼v)))
            (+ᵣ-∼' _ _ _ (ε /2₊)
             (X' u v u∈ v∈ (∼-monotone≤ (ℚ.min≤' (fst δ) (fst δ')) u∼v))))

bounded-id : ∀ a b →
             Bounded (intervalℙ (rat a) (rat b)) (λ x _ → x)
bounded-id a b =
 (ℚ.max (abs a) (abs b) ℚ.+ 1 ,
            (<ᵣ→<ℚ _ _
             ((isTrans≡<ᵣ _ _ _
         (sym (+IdR 0))
         (isTrans<≡ᵣ _ _ _
           (≤<ᵣMonotone+ᵣ _ _ _ _
          (isTrans≤ᵣ _ _ _ (0≤absᵣ (rat a)) (≤maxᵣ _ _ ))
          (decℚ<ᵣ? {0} {1}))
          (cong₂ _+ᵣ_ (cong₂ maxᵣ (absᵣ-rat a)
            ((absᵣ-rat b))) refl  ∙ cong (_+ᵣ 1) (maxᵣ-rat _ _)  ∙  +ᵣ-rat _ _)))))) ,
   λ x x∈ → isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _
     (x∈interval-bound (rat a) (rat b) x x∈)
     (isTrans≡≤ᵣ _ _ _
         (sym (+IdR _))
         (≤ᵣ-o+ _ _ _ (decℚ≤ᵣ? {0} {1}))))
          (cong₂ _+ᵣ_ (cong₂ maxᵣ (absᵣ-rat _) (absᵣ-rat _)) refl
           ∙ cong (_+ᵣ 1) (maxᵣ-rat _ _) ∙ (+ᵣ-rat _ _) )

bounded-+ : ∀ P f g
           → Bounded P f
           → Bounded P g
           → Bounded P (λ x x∈ → f x x∈ +ᵣ g x x∈)
bounded-+ P f g (bf , <bf) (bg , <bg) =
  (bf +₊ bg) , λ x x∈ →
     isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _
      (absᵣ-triangle _ _)
      (≤ᵣMonotone+ᵣ _ _ _ _ (<bf x x∈) (<bg x x∈)))
      (+ᵣ-rat _ _)

bounded-ᵣ : ∀ P f g
           → Bounded P f
           → Bounded P g
           → Bounded P (λ x x∈ → f x x∈ -ᵣ g x x∈)
bounded-ᵣ P f g (bf , <bf) (bg , <bg) =
  (bf +₊ bg) , λ x x∈ →
     isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _
      (isTrans≤≡ᵣ _ _ _ (absᵣ-triangle _ _)
        (cong₂ _+ᵣ_ refl (sym (-absᵣ _))))
      (≤ᵣMonotone+ᵣ _ _ _ _ (<bf x x∈) (<bg x x∈)))
      (+ᵣ-rat _ _)

-ᵣbounded : ∀ P f
           → Bounded P f
           → Bounded P λ x x∈ → -ᵣ (f x x∈)
-ᵣbounded P f (bf , <bf) =
  bf , λ x x∈ → isTrans≡≤ᵣ _ _ _ (sym (-absᵣ _)) (<bf x x∈)

bounded-· : ∀ P f g
           → Bounded P f
           → Bounded P g
           → Bounded P (λ x x∈ → f x x∈ ·ᵣ g x x∈)
bounded-· P f g (bf , <bf) (bg , <bg) =
  (bf ·₊ bg) , (λ x x∈ →
    isTrans≡≤ᵣ _ _ _
      (·absᵣ _ _)
      (isTrans≤≡ᵣ _ _ _
       (≤ᵣ₊Monotone·ᵣ _ _ _ _
         (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ bf)) (0≤absᵣ _)
         (<bf x x∈) (<bg x x∈))
       (sym (rat·ᵣrat _ _))))

bounded-^ⁿ : ∀ a b → rat a ≤ᵣ rat b → ∀ n →
             Bounded (intervalℙ (rat a) (rat b)) (λ x _ → (x ^ⁿ n))
bounded-^ⁿ a b a≤b zero = 1 ,
 λ _ _ → ≡ᵣWeaken≤ᵣ _ _ (absᵣPos _ (decℚ<ᵣ? {0} {1}))
bounded-^ⁿ a b a≤b (suc n) =
  bounded-· (intervalℙ (rat a) (rat b)) _ _
     (bounded-id a b) (bounded-^ⁿ a b a≤b n)

IsUContinuousℙ^ⁿ : ∀ a b → rat a ≤ᵣ rat b → ∀ n →
  IsUContinuousℙ (intervalℙ (rat a) (rat b))
  (λ x _ → x ^ⁿ n)
IsUContinuousℙ^ⁿ a b _ zero = restrIsUContinuousℙ (intervalℙ (rat a) (rat b)) _ (IsUContinuousConst _)
IsUContinuousℙ^ⁿ a b a≤b (suc n) =
  IsUContinuousℙ·ᵣ₂ (intervalℙ (rat a) (rat b)) _ _
    (bounded-id a b)
    (bounded-^ⁿ a b a≤b n)
    (restrIsUContinuousℙ (intervalℙ (rat a) (rat b)) _ IsUContinuousId)
    (IsUContinuousℙ^ⁿ a b a≤b n)


isCauchySequence-∘+ : ∀ s k
 → IsCauchySequence' s
 → IsCauchySequence' (s ∘ (k ℕ.+_))
isCauchySequence-∘+ s k =
  map-snd (λ X m n <n <m →
    X (k ℕ.+ m) (k ℕ.+ n)
      (ℕ.≤-trans <n ℕ.≤SumRight)
      (ℕ.≤-trans <m ℕ.≤SumRight)) ∘_

fromCauchySequence'₁-≡-lem : ∀ s ics ics' →
 fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s ics'
fromCauchySequence'₁-≡-lem s =
  PT.elim2 (λ _ _ → isSetℝ _ _)
   (fromCauchySequence'-≡-lem s)

fromCauchySequence'₁-≡ : ∀ s s' ics ics' →
  (∀ n → s n ≡ s' n) →
 fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s' ics'
fromCauchySequence'₁-≡ s s' ics ics' p = PT.elim2
  (λ ics ics' → isSetℝ
      (fromCauchySequence'₁ s ics)
      (fromCauchySequence'₁ s' ics'))
  (λ ics ics' → fromCauchySequence'-≡ s s' ics ics' p)
  ics ics'

module _ (P : ℙ ℝ) where
 FSeq : Type
 FSeq = ℕ → ∀ x → x ∈ P  → ℝ


 IsUConvFSeries' : FSeq → Type
 IsUConvFSeries' s =
     ∀ (ε : ℚ₊) →
      Σ[ N ∈ ℕ ] ∀ x x∈ n m →
        absᵣ (seqΣ (flip (flip s x) x∈ ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ rat (fst ε)

 IsUCauchyFSequence : FSeq → Type
 IsUCauchyFSequence s =
   ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ x x∈ m n → N ℕ.< n → N ℕ.< m →
     absᵣ ((flip (flip s x) x∈ n) +ᵣ (-ᵣ (flip (flip s x) x∈  m))) <ᵣ rat (fst ε))



 isCauchyFSequenceAt : ∀ s → IsUCauchyFSequence s →
      ∀ x x∈ → IsCauchySequence' (flip (flip s x) x∈)
 isCauchyFSequenceAt s icfs x x∈ ε =
   map-snd ((_$ x∈)∘(_$ x)) (icfs ε)


 IsUConvSeries' : FSeq → Type
 IsUConvSeries' s =
     ∀ (ε : ℚ₊) →
      Σ[ N ∈ ℕ ] ∀ x x∈ n m →
        absᵣ (seqΣ ((flip (flip s x) x∈)
          ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ rat (fst ε)


 IsUConvSeries'SubSeq : ∀ s
  → (spd : ∀ n → Σ _ (n ℕ.≤_))
  → (∀ k → (fst (spd k) ℕ.< fst (spd (suc k))))
  → (∀ n x x∈ → 0 ≤ᵣ s n x x∈)
  → IsUConvSeries' s
  → IsUConvSeries' (s ∘ fst ∘ spd)
 IsUConvSeries'SubSeq s spd sIncr 0≤s =
   (map-snd (λ {N} X x x∈ m m' →
     let k , p = snd (spd (predℕ m' ℕ.+ (m ℕ.+ suc N)))
     in isTrans≤<ᵣ _ _ _
          (subst2 _≤ᵣ_
            (sym (abs[seqΣ]≡seqΣ
              (λ n → s (fst (spd (n ℕ.+ (m ℕ.+ suc N)))) x x∈)
              m'
              λ n → 0≤s (fst (spd (n ℕ.+ (m ℕ.+ suc N)))) x x∈))
            (sym (abs[seqΣ]≡seqΣ
              (λ n → s (n ℕ.+ (m ℕ.+ suc N)) x x∈)
              (m' ℕ.+ k)
              λ n → 0≤s (n ℕ.+ (m ℕ.+ suc N)) x x∈))

            ((series-subSeqLemma (λ n → s n x x∈)
              (λ n → 0≤s n x x∈) spd sIncr (m ℕ.+ suc N) m'))
              )
        (X x x∈ m (m' ℕ.+ k)))) ∘_


 IsUConvSeries'-fromConvBound : ∀ fs fs'
    → (∀ n x x∈ → absᵣ (fs' n x x∈) ≤ᵣ fs n x x∈)
    → IsUConvSeries' fs
    → IsUConvSeries' fs'
 IsUConvSeries'-fromConvBound fs fs' ∣fs'∣<fs =
   map-snd (λ X x x∈ n m →
     isTrans≤<ᵣ _ _ _
      (isTrans≤ᵣ _ _ _
        (abs[seqΣ]≤seqΣ[abs]
          (λ n' → fs' (n' ℕ.+ (n ℕ.+ suc _)) x x∈) m)
        (isTrans≤≡ᵣ _ _ _
          (Seq'≤→Σ≤
            (λ n' → absᵣ (fs' (n' ℕ.+ (n ℕ.+ suc _)) x x∈))
            (λ n' → fs (n' ℕ.+ (n ℕ.+ suc _)) x x∈)
            (λ n' → ∣fs'∣<fs (n' ℕ.+ (n ℕ.+ suc _)) x x∈)
            m)
          (sym (abs[seqΣ]≡seqΣ
            (λ n' → fs (n' ℕ.+ (n ℕ.+ suc _)) x x∈)
            m
            λ n' → isTrans≤ᵣ _ _ _ (0≤absᵣ _)
              (∣fs'∣<fs (n' ℕ.+ (n ℕ.+ suc _)) x x∈)))))
      (X x x∈ n m))
    ∘_

 IsUContFSequence : FSeq → Type
 IsUContFSequence s = ∀ n → IsUContinuousℙ P (s n)

 IsUContFSequenceΣSeq : ∀ s → IsUContFSequence s →
             IsUContFSequence λ n x x∈ → seqΣ (flip (flip s x) x∈ ) n
 IsUContFSequenceΣSeq s x zero =
  restrIsUContinuousℙ P _ (IsUContinuousConst _)
 IsUContFSequenceΣSeq s x (suc n) =
   IsUContinuousℙ+ᵣ₂ P _ _
    (IsUContFSequenceΣSeq s x n) (x n)



 opaque
  fromUCauchyFSequence : ∀ s
        → IsUCauchyFSequence s
        → IsUContFSequence s
        → Σ[ f ∈ (∀ x → x ∈ P → ℝ) ] (IsUContinuousℙ P f)
  fromUCauchyFSequence s icfs iucs = f , icf

   where
   f : ∀ x → x ∈ P → ℝ
   f x x∈ = fromCauchySequence' (λ z → s z x x∈) (isCauchyFSequenceAt s icfs x x∈)

   icf : IsUContinuousℙ P f
   icf ε =
     let N , X = h ((ε /2₊) /2₊)
         (δ , Y) = iucs (suc N) (ε /2₊)

     in δ , λ u v u∈ v∈ u∼v →
          subst∼
            ℚ!
            (triangle∼ (sym∼ _ _ _ (X u u∈ (suc N) ℕ.≤-refl))
            (triangle∼ (Y u v u∈ v∈ u∼v) (X v v∈ (suc N) ℕ.≤-refl)))
    where

     h : ∀ ε → Σ[ N ∈ ℕ ]
            (∀ x x∈ n → N ℕ.< n →
              s n x x∈ ∼[ ε ] f x x∈)
     h ε =
      let (N' , X') = icfs ((ε /2₊) /2₊)
      in N' , λ x x∈ n N<n →

         let u = (𝕣-lim-self _
                (fromCauchySequence'-isCA _
                  (isCauchyFSequenceAt s icfs x x∈))
                  ((ε /2₊) /2₊) (ε /2₊))

         in subst∼ ℚ!
              (triangle∼ (invEq (∼≃abs<ε _ _ ((ε /2₊) /2₊))
                    ((X'  x x∈ _ _  N<n (ℕ.≤-refl {suc N'})) )) u)

  fromCauchySequence'₁≡fromUCauchyFSequence : ∀ (fs : ℕ → ∀ x → x ∈ P  → ℝ) x x∈ →
     ∀ fucsₙ fcₙ fcs  →
     fromCauchySequence'₁ (flip (flip fs x ) x∈) fcs ≡
      fst (fromUCauchyFSequence fs fucsₙ fcₙ) x x∈
  fromCauchySequence'₁≡fromUCauchyFSequence fs x x∈ fucsₙ fcₙ =
   PT.elim (λ _ → isSetℝ _ _)
    λ fcs → fromCauchySequence'-≡-lem
      (λ n → fs n x x∈)
      fcs
      (isCauchyFSequenceAt fs fucsₙ x x∈)

  fromCauchySequence'-at≡fromUCauchyFSequence :
    ∀ (fs : ℕ → ∀ x → x ∈ P  → ℝ) x x∈ →
     ∀ fucsₙ fcₙ  →
     fromCauchySequence' (flip (flip fs x ) x∈)
       (isCauchyFSequenceAt _ fucsₙ  x x∈) ≡
      fst (fromUCauchyFSequence fs fucsₙ fcₙ) x x∈
  fromCauchySequence'-at≡fromUCauchyFSequence _ _ _ _ _ = refl

  IsUCauchyFSequence-lim :
    ∀ s → ∀ iufs iucs →
        ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ]
    (∀ x x∈ n → N ℕ.< n →
      absᵣ ((s n x x∈) -ᵣ (fst (fromUCauchyFSequence s iufs iucs) x x∈))
        <ᵣ (rat (fst ε)))

  IsUCauchyFSequence-lim s iufs iucs ε =
     let (N , X) = iufs (ε /4₊)
     in N , λ x x∈ n N<n →
       let u = (𝕣-lim-self _ (fromCauchySequence'-isCA (λ n → s n x x∈)
                  (isCauchyFSequenceAt s iufs x x∈)) (ε /4₊) (ε /4₊))
           u' = fst (∼≃abs<ε _ _ _)
                (triangle∼ (invEq (∼≃abs<ε _ _ (ε /4₊))
                  ((X  _ _  (suc N) n N<n (ℕ.≤-refl {suc N})) )) u)
       in isTrans<ᵣ _ _ _ u'
                (<ℚ→<ᵣ _ _ <≤ℚ!)

  opaque
   unfolding _+ᵣ_
   fromUCauchyFSequence-+ : ∀ s uca uc s' uca' uc' uca+ uc+
      → ∀ x x∈ →
        fst (fromUCauchyFSequence s uca uc) x x∈
          +ᵣ fst (fromUCauchyFSequence s' uca' uc') x x∈ ≡
            fst (fromUCauchyFSequence
              (λ n x x∈ → s n x x∈ +ᵣ s' n x x∈ )
              uca+
              uc+)
              x x∈
   fromUCauchyFSequence-+ s uca uc s' uca' uc' uca+ uc+ x x∈ =
     let sₓ = λ n → s n x x∈
         s'ₓ = λ n → s' n x x∈
         sumₓ = λ n → s n x x∈ +ᵣ s' n x x∈
         cs = isCauchyFSequenceAt s uca x x∈
         cs' = isCauchyFSequenceAt s' uca' x x∈
         cs+ = isCauchyFSequenceAt (λ n x x∈ → s n x x∈ +ᵣ s' n x x∈) uca+ x x∈
         mapped = mapNE-fromCauchySequence' sumR sₓ cs s'ₓ cs'
     in snd mapped ∙ fromCauchySequence'-≡-lem sumₓ (fst mapped) cs+


  IsoIsUConvSeries'IsCauchy'SequenceSum : (s : FSeq) →
    Iso (IsUConvSeries' s)
        (IsUCauchyFSequence
           λ n x x∈ → seqΣ (flip (flip s x) x∈) n)
  IsoIsUConvSeries'IsCauchy'SequenceSum fs =
     codomainIsoDep λ ε →
       Σ-cong-iso-snd λ N →
         isProp→Iso (isPropΠ4 λ _ _ _ _ → isProp<ᵣ _ _)
         (isPropΠ6 λ _ _ _ _ _ _ → isProp<ᵣ _ _)

         (λ f x x∈ → let s = (flip (flip fs x) x∈) in
            ℕ.elimBy≤
           (λ n n' X <n <n' → subst (_<ᵣ rat (fst ε))
             (minusComm-absᵣ _ _) (X <n' <n))
           λ n n' n≤n' N<n' N<n →
              subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
                 (cong (λ x → seqΣ (s ∘ (ℕ._+ x)) (n' ∸ n))
                    (ℕ.[n-m]+m (suc N) n N<n)
                   ∙∙ sym (seriesDiff s n (n' ∸ n)) ∙∙
                   cong (_+ᵣ (-ᵣ seqΣ s n))
                     (cong (seqΣ s)
                       (ℕ.[n-m]+m n n' n≤n')))
                 (f x x∈ (n ∸ (suc N)) (n' ∸ n)))

         λ f x x∈ n m → let s = (flip (flip fs x) x∈) in
           subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
             (seriesDiff s (n ℕ.+ suc N) m)
               (f x x∈ (n ℕ.+ (suc N)) (m ℕ.+ (n ℕ.+ suc N))
               (subst (N ℕ.<_) (sym (ℕ.+-assoc m n (suc N)))
                 (ℕ.≤SumRight {suc N} {m ℕ.+ n}))
               (ℕ.≤SumRight {suc N} {n}))

 isUCauchyFSequence-ᵣ : ∀ s → IsUCauchyFSequence s
                            → IsUCauchyFSequence (λ n x x∈ → -ᵣ (s n x x∈))
 isUCauchyFSequence-ᵣ s =
    map-snd (λ X _ _ _ _ n< m<
      → isTrans≡<ᵣ _ _ _ (cong absᵣ (sym (-ᵣDistr _ _))
        ∙ sym (-absᵣ _))
        (X _ _ _ _ n< m<)) ∘_

 isUCauchyFSequence+ᵣ : ∀ s s'
    → IsUCauchyFSequence s
    → IsUCauchyFSequence s'
    → IsUCauchyFSequence (λ n x x∈ → (s n x x∈) +ᵣ (s' n x x∈))
 isUCauchyFSequence+ᵣ s s' iucs iucs' ε =
   let (N  , X) = iucs (ε /2₊)
       (N' , X') = iucs' (ε /2₊)
       N⊔N' = ℕ.max N N'
   in N⊔N' , λ x x∈ m n <n <m →
     isTrans≡<ᵣ _ _ _
      (cong absᵣ (ℝ!))
      (isTrans≤<ᵣ _ _ _
       (absᵣ-triangle _ _)
       (isTrans<≡ᵣ _ _ _
         (<ᵣMonotone+ᵣ _ _ _ _
            (X x x∈ _ _ (ℕ.≤<-trans (ℕ.left-≤-max {N} {N'}) <n)
             (ℕ.≤<-trans (ℕ.left-≤-max {N} {N'}) <m))
           (X' x x∈ _ _
              (ℕ.≤<-trans (ℕ.right-≤-max {N'} {N}) <n)
              (ℕ.≤<-trans (ℕ.right-≤-max {N'} {N}) <m)))
           (+ᵣ-rat _ _ ∙
            cong rat ℚ!!)))

IsUCauchyFSequence-∘+ : ∀ P fs m
  → IsUCauchyFSequence P fs
  → IsUCauchyFSequence P (fs ∘ (m ℕ.+_))
IsUCauchyFSequence-∘+ P fs k X =
  map-snd (λ X x x∈ n m <m <n →
    X x x∈ _ _
     (ℕ.≤-+-< ℕ.zero-≤ <m)
     (ℕ.≤-+-< ℕ.zero-≤ <n)) ∘ X

IsUContFSequence-∘+ : ∀ P fs m
  → IsUContFSequence P fs
  → IsUContFSequence P (fs ∘ (m ℕ.+_))
IsUContFSequence-∘+ P fs k = _∘ (k ℕ.+_)

IsUConvSeries'onℚIntervals→IsCauchySequence' :
  (s : ℕ → ℝ → ℝ) → (∀ a b → (rat a) <ᵣ (rat b) →
     IsUConvSeries'
       (intervalℙ (rat a) (rat b)) λ n x∈ _ → s n x∈)
  → ∀ x → ∥ IsCauchySequence' (seqΣ (flip s x)) ∥₁
IsUConvSeries'onℚIntervals→IsCauchySequence' s ucs x = do
  (a , b) , _ , (a< , <b) ← ∃rationalApprox x 1
  ∣ isCauchyFSequenceAt (intervalℙ (rat a) (rat b))
     (λ n x _ → (seqΣ (flip s x)) n)
       (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) λ z x₁ _ → s z x₁)
         (ucs a b (isTrans<ᵣ _ _ _ a< <b)))
     x (<ᵣWeaken≤ᵣ _ _ a< , <ᵣWeaken≤ᵣ _ _ <b) ∣₁

clampDistᵣ
   : (L L' : ℝ) (x y : ℝ) →
     absᵣ (clampᵣ L L' y -ᵣ clampᵣ L L' x) ≤ᵣ
     absᵣ (y -ᵣ x)
clampDistᵣ L L' x y =
 ≤Cont₂
   {λ L L' → absᵣ (clampᵣ L L' y -ᵣ clampᵣ L L' x)}
   {λ _ _ → absᵣ (y -ᵣ x)}
  (cont∘₂ IsContinuousAbsᵣ
    (IsContinuous-₂∘ (IsContinuousClamp₂ y) (IsContinuousClamp₂ x)))
     (cont₂-id _)
  (λ u u' → clampDistᵣ' u u' x y)
  L L'

opaque
 unfolding maxᵣ
 maxᵣ-dist : ∀ a b c → absᵣ (maxᵣ a c -ᵣ maxᵣ b c) ≤ᵣ absᵣ (a -ᵣ b)
 maxᵣ-dist a b c = isTrans≡≤ᵣ _ _ _
  (cong absᵣ (cong₂ _-ᵣ_
    (maxᵣComm _ _ ∙ sym (≤→minᵣ _ (maxᵣ (maxᵣ a b) c)
      (isTrans≤≡ᵣ _ _ _ (≤maxᵣ _ b) (sym (maxᵣAssoc _ _ _) ∙ maxᵣComm _ _))))
    ((maxᵣComm _ _ ∙ sym (≤→minᵣ _ (maxᵣ (maxᵣ a b) c)
      (isTrans≤≡ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _
       (isTrans≡≤ᵣ _ _ _ (maxᵣComm _ _)
        (≤maxᵣ _ _)) (maxᵣComm _ _)) (maxᵣAssoc _ _ _)))))))
  (clampDistᵣ c (maxᵣ (maxᵣ a b) c) b a)

 IsUContinuousMaxᵣ : ∀ x → IsUContinuous (maxᵣ x)
 IsUContinuousMaxᵣ x = Lipschitiz→IsUContinuous 1 (maxᵣ x)
   λ u v ε x₁ → NonExpanding₂-Lemmas.NE.go∼R _ maxR x u v (1 ·₊ ε)
     (subst∼ (sym (Rℚ.·IdL _)) x₁)

IsUContinuousℙ→pointwise : ∀ P f →
  IsUContinuousℙ P f → IsContinuousWithPred P f
IsUContinuousℙ→pointwise P f x u ε u∈P =
  ∣ map-snd (λ X → λ v v∈P → X u v u∈P v∈P) (x ε) ∣₁

IsUContinuousℙ→IsContinuous : ∀ f →
 (∀ a b → rat a <ᵣ rat b →
  IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x _ → f x))
       → IsContinuous f
IsUContinuousℙ→IsContinuous f ucf x ε = do
  (a , b) , _ , (a< , <b) ← ∃rationalApprox x 1
  let x∈ = (isTrans<ᵣ _ _ _
             (isTrans<≡ᵣ _  _ _ (<ℚ→<ᵣ _ _
               ((ℚ.<-o+ _ _ a (ℚ.decℚ<? { -1 } {0}))))
              (cong rat (ℚ.+IdR a))) a<) ,
             (isTrans<ᵣ _ _ _ <b
              (isTrans≡<ᵣ _  _ _ (cong rat (sym (ℚ.+IdR b)))
                (<ℚ→<ᵣ _ _  (ℚ.<-o+ _ _ b (ℚ.decℚ<? {0} {1})))))

      (δ , X) = ucf (a ℚ.- 1) (b ℚ.+ 1)
            (isTrans<ᵣ _ _ _ (fst x∈) (snd x∈)) ε
  ∣ min₊ δ 1 , (λ y x∼y →
    let zz = fst (∼≃abs<ε _ _ _) x∼y
    in X x y
       (ointervalℙ⊆intervalℙ (rat (a ℚ.- 1)) (rat (b ℚ.+ 1)) x x∈)
        (isTrans≤ᵣ _ _ _
          (isTrans≡≤ᵣ _ _ _
           (sym (+ᵣ-rat _ _))
           (≤ᵣMonotone+ᵣ _ _ _ _
             (<ᵣWeaken≤ᵣ _ _ a<)
             (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 1))
              (-ᵣ≤ᵣ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) 1))))))
          (<ᵣWeaken≤ᵣ _ _ (a-b<c⇒a-c<b _ _ _
           (isTrans≤<ᵣ _ _ _ (≤absᵣ _) zz)))
       , isTrans≤ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _
        (a-b≤c⇒a≤c+b _ _ _
        (isTrans≤ᵣ _ _ _ (≤absᵣ _)
         (isTrans≡≤ᵣ _ _ _ (minusComm-absᵣ _ _) (<ᵣWeaken≤ᵣ _ _ zz))))
         (+ᵣComm _ _))
           (isTrans≤≡ᵣ _ _ _
             (≤ᵣMonotone+ᵣ _ _ _ _
              (<ᵣWeaken≤ᵣ _ _ <b)
              (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) 1)))
             (+ᵣ-rat _ _)))
       (∼-monotone≤ (ℚ.min≤ _ _) x∼y)) ∣₁


record DichotomyRec {ℓ : Level} (n : ℚ) (P : ∀ m → rat n ≤ᵣ rat m  → Type ℓ) :
     Type ℓ where
  no-eta-equality
  field
    eq-case : P n (≤ᵣ-refl (rat n))
    gt-case : ∀ m → (p : rat n <ᵣ rat m) → P m (<ᵣWeaken≤ᵣ _ _ p)

  go : ∀ m → (n ≡ m) ⊎ (n ℚ.< m) → ∀ ≤m → P m ≤m
  go m (inr x) ≤m = subst (P m) (isProp≤ᵣ _ _ _ _) (gt-case m (<ℚ→<ᵣ _ _ x))
  go m (inl x) ≤m = subst (uncurry P) (Σ≡Prop (λ _ → isProp≤ᵣ _ _) x) eq-case


  goMax : ∀ m m∈ → P (ℚ.max n m) m∈
  goMax m = go (ℚ.max n m) (ℚ.≤→<⊎≡ n (ℚ.max n m) (ℚ.≤max _ _))


byDichotomyMax : ∀ x₀ → {A : ∀ m → rat x₀ ≤ᵣ rat m → Type} →
  DichotomyRec x₀ A → ∀ (x : ℚ) x₀≤ → A (ℚ.max x₀ x) x₀≤

byDichotomyMax x₀ r x _ = DichotomyRec.goMax r x _

byDichotomyMax₂ : ∀ x₀ y₀
  → {A : ∀ m → rat x₀ ≤ᵣ rat m → ∀ m' → rat y₀ ≤ᵣ rat m' → Type}
  → DichotomyRec x₀
    (λ m x₀≤m → DichotomyRec y₀ (A m x₀≤m)) → ∀ x x₀≤ y y₀≤
    → A (ℚ.max x₀ x) x₀≤
        (ℚ.max y₀ y) y₀≤
byDichotomyMax₂ x₀ y₀ r x x₀≤ y y₀≤ =
 byDichotomyMax y₀
  (byDichotomyMax x₀ r x _) y _

IsUContinuousℙ→pointwiseℙ : ∀ P f →
            (IsUContinuousℙ P (λ x x∈ → f x x∈)) →
            IsContinuousWithPred P f
IsUContinuousℙ→pointwiseℙ P f x u ε u∈P =
  ∣ map-snd (λ X v v∈P → X u v u∈P v∈P) (x ε) ∣₁
