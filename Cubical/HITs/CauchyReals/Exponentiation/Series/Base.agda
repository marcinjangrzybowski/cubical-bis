module Cubical.HITs.CauchyReals.Exponentiation.Series.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Archimedean using
  (∃ℚ₊LargerThanℝ₀₊)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Power.Order using (^ⁿ-Monotone)
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Limits using
  ( fromCauchySequence'₁-≡-lem )
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0<)
open import Cubical.HITs.CauchyReals.Analysis.Uniform using
  ( x∈interval-bound
  ; IsUContinuousℙC·ᵣ
  ; IsUContinuousℙ^ⁿ
  ; IsUConvSeries'
  ; IsUConvSeries'SubSeq
  ; IsUContFSequence
  ; IsUContFSequenceΣSeq
  )
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

expℝ : ℝ → ℝ
expℝ r = fromCauchySequence'₁ (seqΣ (expSeq r)) (expℝ-cauchySeq r)

expSeq' : ℝ → Seq
expSeq' x n = (x ^ⁿ n) ／ᵣ₊ ℚ₊→ℝ₊ (!₊ n)

expSeq'≡expSeq : ∀ x n → expSeq' x n ≡ expSeq x n
expSeq'≡expSeq x zero =
 cong (λ pp → rat [ pos 1 , (1+ 0) ] ·ᵣ
      fst
      (invℝ₊
       (rat [ pos 1 , (1+ 0) ] , pp)))
       (isProp<ᵣ _ _ _ _)
 ∙ cong₂ _·ᵣ_ refl (cong fst (invℝ₊1)) ∙ Rℝ.·IdR 1
expSeq'≡expSeq x (suc n) =
    cong₂ _·ᵣ_ refl
     (cong (fst ∘ invℝ₊)
          (ℝ₊≡ (cong rat (sym (ℚ.ℕ·→ℚ· (suc n) (n !)))
          ∙ rat·ᵣrat [ pos (suc n) / 1 ] _))
      ∙

      cong fst (invℝ₊· (ℚ₊→ℝ₊ [  (1+ n) / 1 ]₊)
       (ℚ₊→ℝ₊ (!₊ n)))
      ∙ ·ᵣComm _ _)

  ∙ cong₂ _·ᵣ_ (·ᵣComm x _) (cong₂ _·ᵣ_ refl (cong (fst ∘ invℝ₊) (ℝ₊≡ refl)))
  ∙ ((·ᵣAssoc _ _ _ ∙
   cong₂ _·ᵣ_ (Rℝ.·CommAssocr _ _ _) refl)
     ∙ sym (·ᵣAssoc _ _ _))
  ∙ cong₂ _·ᵣ_ (expSeq'≡expSeq x n) refl
  ∙ ·ᵣAssoc _ _ _
  ∙ sym (/nᵣ-／ᵣ₊ _ _) ∙ snd (redℝ _)

expSeq'NonNeg : ∀ x → 0 ≤ᵣ x → ∀ n → 0 ≤ᵣ expSeq' x n
expSeq'NonNeg x 0≤x n =
 isTrans≡≤ᵣ _ _ _
   (rat·ᵣrat 0 0)
   (≤ᵣ₊Monotone·ᵣ _ _ _ _
     (0≤x^ⁿ x n 0≤x) (≤ᵣ-refl 0)
     (0≤x^ⁿ x n 0≤x)
      (<ᵣWeaken≤ᵣ _ _ $ snd (invℝ₊
       (ℚ₊→ℝ₊ ((!₊ n))))))

expSeqNonNeg : ∀ x → 0 ≤ᵣ x → ∀ n → 0 ≤ᵣ expSeq x n
expSeqNonNeg x 0≤x n = isTrans≤≡ᵣ _ _ _
  (expSeq'NonNeg x 0≤x n) (expSeq'≡expSeq x n)

absᵣ∘expSeq≡expSeq∘absᵣ : ∀ n x →
   absᵣ (expSeq x n) ≡ expSeq (absᵣ x) n
absᵣ∘expSeq≡expSeq∘absᵣ n x =
     cong absᵣ (sym (expSeq'≡expSeq x n))
  ∙∙ ·absᵣ _ _
     ∙ cong₂ _·ᵣ_
       (absᵣ^ⁿ x n)
       (absᵣPos _
         (snd (invℝ₊
                  (ℚ₊→ℝ₊
                  ((!₊ n))))))
         ∙∙ expSeq'≡expSeq (absᵣ x) n

uConvExpSer : ∀ a b → a <ᵣ b →
  ∥ IsUConvSeries' (intervalℙ a b) (λ n x _ → expSeq x n) ∥₁
uConvExpSer a b a<b = do
  (b' , b<b') ← ∃ℚ₊LargerThanℝ₀₊ ((maxᵣ (absᵣ a) (absᵣ b)) ,
     isTrans≤ᵣ _ _ _ (0≤absᵣ _) (≤maxᵣ _ _))
  return
     ((λ {u} → map-snd λ X x x∈ →
           (expℝ-convSeriesF x _ (isTrans≤<ᵣ _ _ _
              (x∈interval-bound a b x x∈) b<b')
             u _ X))
       ∘ expSeriesConvergesAtℚ₊ (fst b') (snd b'))

opaque
 unfolding maxᵣ NonExpanding₂.go
 uConvExpSer<ℚ : ∀ a b →
   IsUConvSeries' (intervalℙ (rat a) (rat b)) (λ n x _ → expSeq x n)
 uConvExpSer<ℚ a b =
  let b' : ℚ₊
      b' = ℚ.max (abs a) (abs b) ℚ.+ 1 ,

             ((ℚ.≤<Monotone+ 0 _ 0 _
              (ℚ.≤MonotoneMax
               0 _ 0 _
               (0≤abs a) (0≤abs b))
              (ℚ.decℚ<? {0} {1})))
      b<b' : ℚ.max (abs a) (abs b) ℚ.< fst b'
      b<b' = <≤ℚ!
   in (λ {u} → map-snd λ X x x∈ →
            (expℝ-convSeriesF x _
              (isTrans≤<ᵣ _ _ _
               (x∈interval-bound (rat a) (rat b) x x∈)
                (isTrans≡<ᵣ _ _ _ (cong₂ maxᵣ
                  (absᵣ-rat _) (absᵣ-rat _))
                 (<ℚ→<ᵣ _ _ b<b')))
              u _ X))
        ∘ expSeriesConvergesAtℚ₊ (fst b') (snd b')

opaque
 unfolding maxᵣ NonExpanding₂.go
 uConvExpSer<ℚ-absᵣ : ∀ a b
   → IsUConvSeries' (intervalℙ (rat a) (rat b))
       (λ n x _ → expSeq (absᵣ x) n)
 uConvExpSer<ℚ-absᵣ a b =
  let b' : ℚ₊
      b' = ℚ.max (abs a) (abs b) ℚ.+ 1 ,
            ((ℚ.≤<Monotone+ 0 _ 0 _
              (ℚ.≤MonotoneMax
               0 _ 0 _
               (0≤abs a) (0≤abs b))
              (ℚ.decℚ<? {0} {1})))
      b<b' : ℚ.max (abs a) (abs b) ℚ.< fst b'
      b<b' = <≤ℚ!
   in (λ {u} → map-snd λ X x x∈ →
            (expℝ-convSeriesF (absᵣ x) _
              (isTrans≤<ᵣ _ _ _
               (isTrans≡≤ᵣ _ _ _
               (absᵣIdemp x)
               (x∈interval-bound (rat a) (rat b) x x∈))
                (isTrans≡<ᵣ _ _ _ (cong₂ maxᵣ
                  (absᵣ-rat _) (absᵣ-rat _))
                 (<ℚ→<ᵣ _ _ b<b')))
              u _ X))
        ∘ expSeriesConvergesAtℚ₊ (fst b') (snd b')

1+expSeq : ∀ n x → 1 +ᵣ (seqΣ (expSeq x ∘ suc) n) ≡ (seqΣ (expSeq x) (suc n))
1+expSeq n x = (cong (1 +ᵣ_) (seqSumUpTo≡seqSumUpTo' ((expSeq x) ∘ suc) n)
     ∙∙ (sym (seqSumUpTo-suc (expSeq x) n))
     ∙∙ (cong₂ (_+ᵣ_)
       (sym (seqSumUpTo≡seqSumUpTo' (expSeq x) n))
       refl))

isUContFSequenceExpSer : ∀ a b → rat a ≤ᵣ rat b →
   IsUContFSequence (intervalℙ (rat a) (rat b))
      (λ z x _ → expSeq x z)
isUContFSequenceExpSer a b a≤b n =
  subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
    (funExt₂ λ _ _ → cong₂ _·ᵣ_ refl (sym (invℝ₊-rat  _))
       ∙ expSeq'≡expSeq _ n)
    (IsUContinuousℙC·ᵣ (intervalℙ (rat a) (rat b)) _ _
      (IsUContinuousℙ^ⁿ a b a≤b n))

isUContFSequenceExp : ∀ a b → rat a ≤ᵣ rat b →
   IsUContFSequence (intervalℙ (rat a) (rat b))
      (λ z x _ → seqΣ (expSeq x) z)
isUContFSequenceExp a b a≤b = IsUContFSequenceΣSeq
 (intervalℙ (rat a) (rat b)) (λ z x _ → expSeq x z) (isUContFSequenceExpSer a b a≤b)

expℝ0=1 : expℝ 0 ≡ 1
expℝ0=1 = fromCauchySequence'₁≡
  (seqΣ (expSeq 0)) (expℝ-cauchySeq 0) 1
   λ ε → ∣ 0 , (λ n (n' , p) →
    isTrans≡<ᵣ _ _ _
     (cong absᵣ (Rℝ.+InvR' _ _
       ((cong (seqΣ (expSeq 0)) (sym p ∙ ℕ.+-suc n' 0))
          ∙ sym (1+expSeq (n' ℕ.+ 0) 0)  ∙
          Rℝ.+IdR' _ _
            (seqSumUpTo≡seqSumUpTo' (expSeq 0 ∘ suc) (n' ℕ.+ 0) ∙
              (cong seqΣ' (funExt λ k → sym (expSeq'≡expSeq 0 (suc k)) ∙
                Rℝ.0LeftAnnihilates' _ _ (0^ⁿ k))
               ≡$ (n' ℕ.+ 0)) ∙ seqSumUpToConst 0 (n' ℕ.+ 0) ∙
                Rℝ.0LeftAnnihilates _) )) ∙ absᵣ0)
     (snd (ℚ₊→ℝ₊ ε))) ∣₁

expℚ-bound : ∀ (x : ℚ) → 0 ℚ.≤ x → Σ[ q ∈ ℚ₊ ] expℝ (rat x) <ᵣ rat (fst q)
expℚ-bound x = ⊎.rec
   (λ 0=x → 2 , isTrans≡<ᵣ _ _ _
     (cong (expℝ ∘ rat) (sym 0=x) ∙ expℝ0=1)
       (decℚ<ᵣ? {1} {2}))
   (λ 0<x →
     let s = seqΣ (expSeq (rat x))
         ics = fst (IsConvSeries'≃IsCauchySequence'Sum (expSeq (rat x)))
               (expSeriesConvergesAtℚ₊ x 0<x)
         N , X = fromCauchySequence'-lim s ics 1

         q , p = expSeries-rat x (suc N)
         Z : ℚ.0< (1 ℚ.+ abs q)
         Z = ℚ<→0< (1 ℚ.+ abs q) (ℚ.<≤Monotone+ 0 _ 0 _
            (ℚ.decℚ<? {0} {1}) (0≤abs q))
         ZZ = isTrans<≡ᵣ _ _ _

                 (isTrans<≤ᵣ _ _ _(a-b<c⇒a<c+b _ _ _ (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                  (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _)
                   (X (suc N) (ℕ.≤-refl {suc N}))
                   )))
                   (≤ᵣ-o+ _ _ _ (≤absᵣ _)))
                   (cong (1 +ᵣ_) (cong absᵣ p ∙
                     absᵣ-rat _)
                   ∙ +ᵣ-rat _ _ )
     in (_ , Z) ,
         isTrans≡<ᵣ _ _ _
          (fromCauchySequence'₁-≡-lem s (expℝ-cauchySeq (rat x)) ∣ ics ∣₁) ZZ)
   ∘ (ℚ.≤→<⊎≡ 0 x)

monotone-expℝ : ∀ a b → 0 ≤ᵣ a → a ≤ᵣ b → expℝ a ≤ᵣ expℝ b
monotone-expℝ a b 0≤a a≤b =
  fromCauchySequence'₁≤
   (seqΣ (expSeq a))
   (seqΣ (expSeq b))
   (expℝ-cauchySeq a)
   (expℝ-cauchySeq b)
   λ n → subst2 _≤ᵣ_
      (λ i → seqSumUpTo≡seqSumUpTo' (λ n → expSeq'≡expSeq a n i) n (~ i))
      (λ i → seqSumUpTo≡seqSumUpTo' (λ n → expSeq'≡expSeq b n i) n (~ i))
      (seqSumUpTo≤ _ _
       (λ n →
         ≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ _)))
          (^ⁿ-Monotone n 0≤a a≤b))
       n)

1≤expℝ[pos] : ∀ x → 0 ≤ᵣ x → 1 ≤ᵣ expℝ x
1≤expℝ[pos] x 0≤x =
  isTrans≡≤ᵣ _ _ _
    (sym expℝ0=1) (monotone-expℝ 0 x (≤ᵣ-refl 0) 0≤x)

expℝ-pos : ∀ x → 0 ≤ᵣ x → 0 <ᵣ expℝ x
expℝ-pos x 0≤x = isTrans<≤ᵣ _ _ _
  (decℚ<ᵣ? {0} {1}) (1≤expℝ[pos] x 0≤x)

expBounded : ∀ a b → 0 ≤ᵣ rat a → rat a ≤ᵣ rat b →
  Bounded (intervalℙ (rat a) (rat b)) (λ x _  → expℝ x)
expBounded a b 0≤a a≤b =
  let q₊ , X = expℚ-bound b (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _ 0≤a a≤b))
  in q₊ , λ x x∈ → isTrans≤ᵣ _ _ _
        (isTrans≡≤ᵣ _ _ _
          (absᵣPos _ (expℝ-pos x (isTrans≤ᵣ _ _ _ 0≤a (fst x∈))))
          (monotone-expℝ _ _ (isTrans≤ᵣ _ _ _ 0≤a (fst x∈))
            (snd x∈)))
        (<ᵣWeaken≤ᵣ _ _ X)
