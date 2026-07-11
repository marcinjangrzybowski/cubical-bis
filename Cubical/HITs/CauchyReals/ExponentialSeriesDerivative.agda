module Cubical.HITs.CauchyReals.ExponentialSeriesDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.FundamentalTheoremOfCalculus
open import Cubical.HITs.CauchyReals.Uniform using
  ( isCauchySequence-∘+
  ; IsUCauchyFSequence
  ; IsUContFSequence-∘+
  ; IsUCauchyFSequence-∘+
  ; IsoIsUConvSeries'IsCauchy'SequenceSum
  ; fromCauchySequence'₁≡fromUCauchyFSequence
  ; fromUCauchyFSequence
  )
open import Cubical.HITs.CauchyReals.PowerDerivative
open import Cubical.HITs.CauchyReals.ExponentialSeries
open import Cubical.HITs.CauchyReals.RationalsImports

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

IsUCauchyFSequenceExp : ∀ a b → a <ᵣ b →
  ∥ IsUCauchyFSequence (intervalℙ a b)
      (λ n x _ → seqΣ (expSeq x) n) ∥₁
IsUCauchyFSequenceExp a b a<b =
  PT.map (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
    (intervalℙ a b) (λ n x _ → expSeq x n)))
    (uConvExpSer a b a<b)

expSer'UDer : ∀ a b → rat a <ᵣ rat b → ∀ n →
  uDerivativeOfℙ (intervalℙ (rat a) (rat b))
    , (λ r _ → expSeq' r (suc n)) is
      (λ r _ → expSeq' r n)
expSer'UDer a b a<b n =
  let f = λ r _ → r ^ⁿ (suc n)
      f' = λ r _ → fromNat (suc n) ·ᵣ (r ^ⁿ n)
      z = C·uDerivativeℙ (intervalℙ (rat a) (rat b)) (fst 1/n!)
            f f'
            (uDerivativeOfℙ-^ⁿ a b a<b n)
  in subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ r _ → ·ᵣComm (fst 1/n!) (r ^ⁿ (suc n)))
    (funExt₂ λ _ _ →
      ·ᵣAssoc _ _ _  ∙ ·ᵣComm _ _ ∙
       cong₂ _·ᵣ_ refl
        (cong₂ _·ᵣ_ (cong (fst ∘ invℝ₊)
           ((ℝ₊≡ (cong rat (sym (ℚ.ℕ·→ℚ· (suc n) (n !)))
             ∙ rat·ᵣrat _ _)))
           ∙ cong fst (invℝ₊· (ℚ₊→ℝ₊ [ (1+ n) / 1 ]₊)
             (ℚ₊→ℝ₊ (!₊ n)))
                ∙ ·ᵣComm _ _) refl
         ∙ [x/₊y]·yᵣ _ _))
    z
 where
  1/n! = invℝ₊ $ ℚ₊→ℝ₊ (!₊ (suc n))

-- Previous name: expSeq'der.
DerivativeOfℙ-expSeq' : ∀ a b → rat a <ᵣ rat b → ∀ n →
  DerivativeOfℙ (intervalℙ (rat a) (rat b))
    , (λ r _ → expSeq' r (suc n)) is
      (λ r _ → expSeq' r n)
DerivativeOfℙ-expSeq' a b a<b n =
  uDerivativeOfℙ→DerivativeOfℙ
    (intervalℙ (rat a) (rat b))
    (λ r _ → expSeq' r (suc n))
    (λ r _ → expSeq' r n)
    (expSer'UDer a b a<b n)

expSerUDer : ∀ a b → rat a <ᵣ rat b → ∀ n →
  uDerivativeOfℙ (intervalℙ (rat a) (rat b))
    , (λ r _ → expSeq r (suc n)) is
      (λ r _ → expSeq r n)
expSerUDer a b a<b n =
  subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
   (funExt₂ (λ x _ → expSeq'≡expSeq x (suc n)))
   (funExt₂ (λ x _ → expSeq'≡expSeq x n))
   (expSer'UDer a b a<b n)

-- Previous name: expSerDer.
DerivativeOfℙ-expSeq : ∀ a b → rat a <ᵣ rat b → ∀ n →
  DerivativeOfℙ (intervalℙ (rat a) (rat b))
    , (λ r _ → expSeq r (suc n)) is
      (λ r _ → expSeq r n)
DerivativeOfℙ-expSeq a b a<b n =
  uDerivativeOfℙ→DerivativeOfℙ
    (intervalℙ (rat a) (rat b))
    (λ r _ → expSeq r (suc n))
    (λ r _ → expSeq r n)
    (expSerUDer a b a<b n)

expSeqUDer : ∀ a b → rat a <ᵣ rat b → ∀ n →
  uDerivativeOfℙ (intervalℙ (rat a) (rat b))
    , (λ r _ → seqΣ (expSeq r) (suc n)) is
      (λ r _ → seqΣ (expSeq r) n)
expSeqUDer a b a<b zero =
  uDerivativeℙ-const (intervalℙ (rat a) (rat b)) (0 +ᵣ 1)
expSeqUDer a b a<b (suc n) =
  +uDerivativeℙ (intervalℙ (rat a) (rat b))
   (λ r _ → seqΣ (expSeq r) (suc n))
   (λ r _ → seqΣ (expSeq r) n)
   (λ r _ → expSeq r (suc n))
   (λ r _ → expSeq r n)
   (expSeqUDer a b a<b n) (expSerUDer a b a<b n)

DerivativeOfℙ-expSeqΣ : ∀ a b → rat a <ᵣ rat b → ∀ n →
  DerivativeOfℙ (intervalℙ (rat a) (rat b))
    , (λ r _ → seqΣ (expSeq r) (suc n)) is
      (λ r _ → seqΣ (expSeq r) n)
DerivativeOfℙ-expSeqΣ a b a<b n =
  uDerivativeOfℙ→DerivativeOfℙ
    (intervalℙ (rat a) (rat b))
    (λ r _ → seqΣ (expSeq r) (suc n))
    (λ r _ → seqΣ (expSeq r) n)
    (expSeqUDer a b a<b n)

uDerivativeOfℙ-expℝ : ∀ a b → rat a <ᵣ rat b
  → uDerivativeOfℙ (intervalℙ (rat a) (rat b))
      , (λ x _ → expℝ x) is (λ x _ → expℝ x)
uDerivativeOfℙ-expℝ a b a<b = PT.rec (isPropΠ λ _ → squash₁) (λ x → x) $ do
  z ← IsUCauchyFSequenceExp (rat a) (rat b) a<b
  let f = λ n x _ → seqΣ (expSeq x) n
      F = f ∘ (1 ℕ.+_)
      ucf = isUContFSequenceExp a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b)
      uF = IsUContFSequence-∘+ (intervalℙ (rat a) (rat b)) f 1 ucf
      zF = IsUCauchyFSequence-∘+ (intervalℙ (rat a) (rat b)) f 1 z
      zz = uCauchyDer
           (rat a)
           (rat b)
           a<b
           f
           F

           z
           ucf
           uF
           zF
           (expSeqUDer a b a<b)
  return (subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ x x∈ →
      let ics = PT.map (isCauchySequence-∘+ (seqΣ (expSeq x)) 1)
                  (expℝ-cauchySeq x)
      in sym (fromCauchySequence'₁≡fromUCauchyFSequence
           (intervalℙ (rat a) (rat b)) F x x∈
           zF
           uF
           ics)
       ∙ sym (fromCauchySequence'₁-∘+ (seqΣ (expSeq x)) 1
           (expℝ-cauchySeq x) ics))
    (funExt₂ λ x x∈ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence
        (intervalℙ (rat a) (rat b)) f x x∈
        z
        ucf
        (expℝ-cauchySeq x)))
    zz)

DerivativeOfℙ-expℝ : ∀ a b → rat a <ᵣ rat b
  → DerivativeOfℙ (intervalℙ (rat a) (rat b))
      , (λ x _ → expℝ x) is (λ x _ → expℝ x)
DerivativeOfℙ-expℝ a b a<b =
  uDerivativeOfℙ→DerivativeOfℙ
    (intervalℙ (rat a) (rat b))
    (λ x _ → expℝ x)
    (λ x _ → expℝ x)
    (uDerivativeOfℙ-expℝ a b a<b)
