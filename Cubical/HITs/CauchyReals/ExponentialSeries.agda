module Cubical.HITs.CauchyReals.ExponentialSeries where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Uniform using
  ( x∈interval-bound
  ; IsUContinuousℙC·ᵣ
  ; IsUContinuousℙ^ⁿ
  ; IsUConvSeries'
  ; IsUConvSeries'SubSeq
  ; IsUContFSequence
  ; IsUContFSequenceΣSeq
  )
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.RationalsImports

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

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

expSeq'der : ∀ n x →
           derivativeOf flip expSeq' (suc n) at x is
             expSeq' x n
expSeq'der n x =
  let z = C·Derivative (fst 1/n!) x (_^ⁿ suc n) _ (derivative-^ⁿ n x)
  in substDer₂ (λ x → ·ᵣComm _ (x ^ⁿ suc n))
     (·ᵣAssoc _ _ _  ∙ ·ᵣComm _ _ ∙
       cong₂ _·ᵣ_ refl
        (cong₂ _·ᵣ_ (cong (fst ∘ invℝ₊)
           ((ℝ₊≡ (cong rat (sym (ℚ.ℕ·→ℚ· (suc n) (n !)))
             ∙ rat·ᵣrat _ _)))
           ∙ cong fst (invℝ₊· (ℚ₊→ℝ₊ [ (1+ n) / 1 ]₊)
             (ℚ₊→ℝ₊ (!₊ n)))
                ∙ ·ᵣComm _ _) refl
         ∙ [x/₊y]·yᵣ _ _)) z
 where
 1/n! = invℝ₊ $ ℚ₊→ℝ₊ (!₊ (suc n))

expSerDer : ∀ n x →
    derivativeOf (λ x → expSeq x (suc n))
               at x is (expSeq x      n)
expSerDer n x = substDer₂
  (λ x → expSeq'≡expSeq x (suc n))
  (expSeq'≡expSeq x n)
  (expSeq'der n x)

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
