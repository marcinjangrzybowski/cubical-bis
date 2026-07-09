
module Cubical.HITs.CauchyReals.TrigBase where

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
import Cubical.Data.Int.Fast.Order as ℤ
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
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Signs
open import Cubical.HITs.CauchyReals.Inverse
-- open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Sequence.Limits
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Uniform using
  ( x∈interval-bound
  ; IsUContinuousConst
  ; IsUContinuousℙ-transl
  ; IsUContinuousℙ+ᵣ₂
  ; <ε-lemma
  ; IsUContinuousℙ·ᵣ₂
  ; IsUContinuousℙC·ᵣ
  ; IsUContinuousℙ-ᵣ∘
  ; IsUContinuousId
  ; IsUContinuousℙ-const
  ; IsUContinuousℙ→pointwise
  ; bounded-id
  ; bounded-+
  ; bounded-ᵣ
  ; -ᵣbounded
  ; bounded-·
  ; bounded-^ⁿ
  ; IsUContinuousℙ^ⁿ
  ; IsUCauchyFSequence-∘+
  ; IsUContFSequence-∘+
  ; clampDistᵣ
  ; maxᵣ-dist
  ; IsUContinuousMaxᵣ
  ; FSeq
  ; IsUConvFSeries'
  ; IsUCauchyFSequence
  ; isCauchyFSequenceAt
  ; IsUConvSeries'
  ; IsUConvSeries'SubSeq
  ; IsUConvSeries'-fromConvBound
  ; IsUContFSequence
  ; IsUContFSequenceΣSeq
  ; fromUCauchyFSequence
  ; fromCauchySequence'₁≡fromUCauchyFSequence
  ; fromCauchySequence'-at≡fromUCauchyFSequence
  ; IsUCauchyFSequence-lim
  ; fromUCauchyFSequence-+
  ; IsoIsUConvSeries'IsCauchy'SequenceSum
  ; isUCauchyFSequence-ᵣ
  ; isUCauchyFSequence+ᵣ
  ; IsUConvSeries'onℚIntervals→IsCauchySequence'
  )
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore hiding
  ( IsUContinuousConst
  ; IsUContinuous+ᵣ₂
  ; IsUContinuousC·ᵣ
  ; IsUContinuous-ᵣ₂
  ; clampDistᵣ
  ; IsUContinuousMaxᵣ
  )
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.FundamentalTheoremOfCalculus
open import Cubical.HITs.CauchyReals.ExponentialSeries
-- open import Cubical.HITs.CauchyReals.Exponentiation


open import Cubical.HITs.CauchyReals.LiftingExpr


open import Cubical.HITs.CauchyReals.RationalsImports 


open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- FTOC⇒* : ∀ a b → a ≤ᵣ b
--           → (f F : ∀ x → x ∈ intervalℙ a b →  ℝ)

--           → (ax⊆ab : ∀ x → (x∈ : x ∈ intervalℙ a b) →
--                  ∀ y → y ∈ intervalℙ a x
--                      → y ∈ intervalℙ a b)
--           → (∀ x → (x∈ : x ∈ intervalℙ a b) →
--                 on[ a , x ]IntegralOf (λ y ≤y y≤ →
--                   f y (ax⊆ab x x∈ y (≤y , y≤)))
--                  is (F x x∈))
--           → (ucf : IsUContinuousℙ (intervalℙ a b) f)
--           → uDerivativeOfℙ (intervalℙ a b) , F is f
-- FTOC⇒* a b a≤b f F ax⊆ab X ucf  =
--   subst
--     (λ F → uDerivativeOfℙ (intervalℙ a b) , F is f)
--     (funExt₂ (λ y y∈ →
--       let p = (λ x x∈ →
--                  cong (f x) (∈-isProp (intervalℙ _ _) _ _ _))
--       in Integrate-UContinuousℙ-≡ _ _ _ _ _ _
--               (IsUContinuousℙ-restr _ _ _ _ ucf)
--                p
--             ∙ (IntegralUniq a y (fst y∈)
--      _ _ _
--      (snd (Integrate-UContinuousℙ a _ _ _ _))
--      (X y y∈)))
--      )
--     (FTOC⇒' a b a≤b f ucf)

sinSeries cosSeries : ℕ → ℝ → ℝ
sinSeries n x = -1ⁿ· n (expSeq x (suc (n ℕ.· 2)))
cosSeries n x = -1ⁿ· n (expSeq x (n ℕ.· 2))

sinSeq≤expSeq-1 : ∀ n x → seqΣ (flip sinSeries x) n ≤ᵣ
                             seqΣ (expSeq (absᵣ x) ∘ suc) (n ℕ.· 2)
sinSeq≤expSeq-1 n x =
   isTrans≤≡ᵣ _ _ _
     (Seq'≤→Σ≤ _ _
      (λ n →
         isTrans≤ᵣ _ _ _
         (≤absᵣ _) (isTrans≡≤ᵣ _ _ _
           (absᵣ∘-1ⁿ· n _ ∙ sym (+IdR _))
           (≤ᵣMonotone+ᵣ _ _ _ _
            (≡ᵣWeaken≤ᵣ _ _ (absᵣ∘expSeq≡expSeq∘absᵣ (suc (n ℕ.· 2)) x))
            (expSeqNonNeg _ (0≤absᵣ x) (suc (suc (n ℕ.· 2))))))) n)
     (sym (seqΣ∘·2 (expSeq (absᵣ x) ∘ suc) n))


cosSeq≤expSeq : ∀ n x → seqΣ (flip cosSeries x) n ≤ᵣ
                             seqΣ (expSeq (absᵣ x)) (n ℕ.· 2)
cosSeq≤expSeq n x =
   isTrans≤≡ᵣ _ _ _
     (Seq'≤→Σ≤ _ _
      (λ n →
         isTrans≤ᵣ _ _ _
         (≤absᵣ _) (isTrans≡≤ᵣ _ _ _
           (absᵣ∘-1ⁿ· n _ ∙ sym (+IdR _))
           (≤ᵣMonotone+ᵣ _ _ _ _
            (≡ᵣWeaken≤ᵣ _ _ (absᵣ∘expSeq≡expSeq∘absᵣ (n ℕ.· 2) x))
            (expSeqNonNeg _ (0≤absᵣ _) _)))) n)
     (sym (seqΣ∘·2 (expSeq (absᵣ x)) n))

-cosSeq≤expSeq : ∀ n x → -ᵣ (seqΣ (flip cosSeries x) n) ≤ᵣ
                             seqΣ (expSeq (absᵣ x)) (n ℕ.· 2)
-cosSeq≤expSeq n x =
   isTrans≡≤ᵣ _ _ _
     (-seqΣ' (flip cosSeries x) n)
    (isTrans≤≡ᵣ _ _ _
     (Seq'≤→Σ≤ _ _
      (λ n →
         isTrans≤ᵣ _ _ _
         (isTrans≤≡ᵣ _ _ _
           (≤absᵣ _) (sym (-absᵣ _)))
         (isTrans≡≤ᵣ _ _ _
           (absᵣ∘-1ⁿ· n _ ∙ sym (+IdR _))
           (≤ᵣMonotone+ᵣ _ _ _ _
            (≡ᵣWeaken≤ᵣ _ _ (absᵣ∘expSeq≡expSeq∘absᵣ (n ℕ.· 2) x))
            (expSeqNonNeg _ (0≤absᵣ _) _)))) n)
     (sym (seqΣ∘·2 (expSeq (absᵣ x)) n)))

-- -- cosSer'=-sinSer : ∀ a b → rat a <ᵣ rat b → ∀ n →
-- --    uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
-- --       (λ r _ → flip cosSeries r (suc n)) is
-- --       (λ r _ → -ᵣ (flip sinSeries r n))
-- -- cosSer'=-sinSer a b a<b n =
-- --   subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
-- --     (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
-- --     (funExt₂ λ _ _ → cong₂ _·ᵣ_  (-1ⁿ-suc n) refl
-- --       ∙ -ᵣ· _ _ ∙ cong -ᵣ_ (sym (-1ⁿ·≡· n _)))
-- --     (C·uDerivativeℙ _ (rat (-1ⁿ (suc n))) _ _
-- --      (expSerUDer a b a<b (suc (n ℕ.· 2))))



-- -- sinSer'=cosSer : ∀ a b → rat a <ᵣ rat b → ∀ n →
-- --  uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → (flip sinSeries x) n)
-- --                              is (λ x _ → (flip cosSeries x) n)
-- -- sinSer'=cosSer a b a<b n =
-- --   subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
-- --     (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
-- --     (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
-- --     (C·uDerivativeℙ _ (rat (-1ⁿ n)) _ _
-- --      (expSerUDer a b a<b (n ℕ.· 2)))



-- -- sinSeq'=cosSeq : ∀ a b → rat a <ᵣ rat b → ∀ n →
-- --  uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → seqΣ (flip sinSeries x) n)
-- --                       is (λ x _ → seqΣ (flip cosSeries x) n)
-- -- sinSeq'=cosSeq a b a<b zero = uDerivativeℙ-const _ _
-- -- sinSeq'=cosSeq a b a<b (suc n) =
-- --   +uDerivativeℙ _ _ _ _ _
-- --     (sinSeq'=cosSeq a b a<b n) (sinSer'=cosSer a b a<b n)

-- -- cosSeq'=-sinSeq : ∀ a b → rat a <ᵣ rat b → ∀ n →
-- --  uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → seqΣ (flip cosSeries x) (suc n))
-- --                       is (λ x _ → -ᵣ (seqΣ (flip sinSeries x) n))
-- -- cosSeq'=-sinSeq a b a<b zero =
-- --    subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ _ _ → 0 +ᵣ 1) is_)
-- --     (funExt₂ λ _ _ → sym (-ᵣ-rat 0))
-- --     (uDerivativeℙ-const _ (0 +ᵣ 1))
-- -- cosSeq'=-sinSeq a b a<b (suc n) =
-- --    subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
-- --      (λ x _ → seqΣ (flip cosSeries x) (suc (suc n))) is_)
-- --     (funExt₂ λ _ _ → sym (-ᵣDistr _ _))
-- --   (+uDerivativeℙ _ _ _ _ _
-- --     (cosSeq'=-sinSeq a b a<b n) (cosSer'=-sinSer a b a<b n))

sin-conv : ∀ a b → (rat a) <ᵣ (rat b) →
  IsUConvSeries' (intervalℙ (rat a) (rat b))
    λ n x _ → sinSeries n x
sin-conv a b a<b  =
  IsUConvSeries'-fromConvBound
    (intervalℙ (rat a) (rat b))
      (λ n x _ → expSeq (absᵣ x) (suc (n ℕ.· 2))) (λ n x _ → sinSeries n x)
     (λ n x x∈ →
       ≡ᵣWeaken≤ᵣ _ _
         (absᵣ∘-1ⁿ· n _ ∙ absᵣ∘expSeq≡expSeq∘absᵣ _ _))
     (IsUConvSeries'SubSeq (intervalℙ (rat a) (rat b))
       (λ n x _ → expSeq (absᵣ x) n)
       (λ n → (suc (n ℕ.· 2)) ,
           subst (ℕ._≤ (suc (n ℕ.· 2))) (·-identityʳ n)
            (ℕ.≤-suc (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1}))))
        (λ k → ℕ.suc-≤-suc ℕ.≤-sucℕ)
            (λ n x x∈ → expSeqNonNeg _ (0≤absᵣ x) n) (uConvExpSer<ℚ-absᵣ a b))

cos-conv : ∀ a b → (rat a) <ᵣ (rat b) →
  IsUConvSeries' (intervalℙ (rat a) (rat b))
    λ n x _ → cosSeries n x
cos-conv a b a<b =
  IsUConvSeries'-fromConvBound
    (intervalℙ (rat a) (rat b))
      (λ n x _ → expSeq (absᵣ x) ((n ℕ.· 2))) (λ n x _ → cosSeries n x)
     (λ n x x∈ →
       ≡ᵣWeaken≤ᵣ _ _
         (absᵣ∘-1ⁿ· n (expSeq x (n ℕ.· 2)) ∙
          absᵣ∘expSeq≡expSeq∘absᵣ (n ℕ.· 2) x))
     (IsUConvSeries'SubSeq (intervalℙ (rat a) (rat b))
       (λ n x _ → expSeq (absᵣ x) n)
       (λ n → (n ℕ.· 2) ,
           subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
            ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1}))))
       (λ k → ℕ.≤-sucℕ)
            (λ n x x∈ → expSeqNonNeg _ (0≤absᵣ x) n) (uConvExpSer<ℚ-absᵣ a b))

sin-ch : ∀ x → ∥ IsCauchySequence' (seqΣ (λ x₁ → sinSeries x₁ x)) ∥₁
sin-ch = IsUConvSeries'onℚIntervals→IsCauchySequence' _ sin-conv

cos-ch : ∀ x → ∥ IsCauchySequence' (seqΣ (λ x₁ → cosSeries x₁ x)) ∥₁
cos-ch = IsUConvSeries'onℚIntervals→IsCauchySequence' _ cos-conv


opaque
 sin cos : ℝ → ℝ
 sin x = fromCauchySequence'₁ (seqΣ (flip sinSeries x)) (sin-ch x)
 cos x = fromCauchySequence'₁ (seqΣ (flip cosSeries x)) (cos-ch x)

 sinImpl : ∀ x → sin x ≡ fromCauchySequence'₁ (seqΣ (flip sinSeries x)) (sin-ch x)
 sinImpl x = refl
 cosImpl : ∀ x → cos x ≡ fromCauchySequence'₁ (seqΣ (flip cosSeries x)) (cos-ch x)
 cosImpl x = refl


 cos0=1 : cos 0 ≡ 1
 cos0=1 = fromCauchySequence'₁≡ (seqΣ (λ x → cosSeries x 0))
   (cos-ch 0) 1
    λ ε → ∣ 0 ,
     (λ { zero <0 → ⊥.rec (ℕ.¬-<-zero <0)
        ; (suc n) _ → isTrans≡<ᵣ _ _ _
                (cong absᵣ (Rℝ.+InvR' _ _
                 ( seqSumUpTo≡seqSumUpTo' (λ x → cosSeries x 0) (suc n)
                  ∙ Rℝ.+IdR' _ _
                   (seqΣ'0≡0 _ n
                     λ n →
                       -1ⁿ·≡· (suc n) _ ∙
                        cong₂ _·ᵣ_ refl (sym (expSeq'≡expSeq 0 ((suc n ℕ.· 2))))
                        ∙ Rℝ.0RightAnnihilates' _ _
                         (Rℝ.0LeftAnnihilates' _ _
                          (0^ⁿ (suc (n ℕ.· 2)))))))
                 ∙ absᵣ0)
                (snd (ℚ₊→ℝ₊ ε))
        }) ∣₁

 sin0=0 : sin 0 ≡ 0
 sin0=0 = fromCauchySequence'₁≡ (seqΣ (λ x → sinSeries x 0))
   (sin-ch 0) 0
    λ ε → ∣ 0 ,
      (λ n _ →
        isTrans≡<ᵣ _ _ _
                (cong absᵣ (Rℝ.+InvR' _ _
                 ( seqSumUpTo≡seqSumUpTo' (λ x → sinSeries x 0) n
                  ∙ (seqΣ'0≡0 _ n
                     λ n →
                       -1ⁿ·≡· n _ ∙
                        cong₂ _·ᵣ_ refl (sym (expSeq'≡expSeq 0 (suc (n ℕ.· 2))))
                        ∙ Rℝ.0RightAnnihilates' _ _
                         (Rℝ.0LeftAnnihilates' _ _
                          (0^ⁿ (n ℕ.· 2))))))
                 ∙ absᵣ0)
                (snd (ℚ₊→ℝ₊ ε))) ∣₁


 sin-odd : ∀ x → -ᵣ (sin x) ≡ sin (-ᵣ x)
 sin-odd x =
  let u , v =  (map-fromCauchySequence'₁ 1 _ (sin-ch x) (-ᵣ_) -ᵣ-lip)
  in v
    ∙
    fromCauchySequence'₁-≡ _ _ u (sin-ch _)
         λ n →
           (-ᵣ_ ∘ seqΣ (λ x₁ → sinSeries x₁ x)) n
             ≡⟨ -seqΣ' (λ x₁ → sinSeries x₁ x) n ⟩
           (seqΣ (λ x₁ → -ᵣ (sinSeries x₁ x))) n ≡⟨

            cong seqΣ (funExt
              (λ k →
                  cong (-ᵣ_) (cong (-1ⁿ· k)
                      ((sym (expSeq'≡expSeq x (suc (k ℕ.· 2)))))
                       ∙ -1ⁿ·≡· k (expSeq' x (suc (k ℕ.· 2))) )
                ∙ sym (·-ᵣ _ _)
                ∙ sym (-1ⁿ·≡· k _)
                ∙ cong (-1ⁿ· k) (
                    (sym (-ᵣ· _ _))
                  ∙ cong₂ _·ᵣ_ (^ⁿ-odd k x) refl
                  ∙ expSeq'≡expSeq (-ᵣ x) (suc (k ℕ.· 2)))
               ))
              ≡$ n
              ⟩
            seqΣ (λ x₁ → sinSeries x₁ (-ᵣ x)) n ∎

 cos-even : ∀ x → cos x ≡ cos (-ᵣ x)
 cos-even x = fromCauchySequence'₁-≡ _ _ (cos-ch _) (cos-ch _)
         (cong seqΣ (funExt
          (λ k → cong (-1ⁿ· k)
           (sym (expSeq'≡expSeq x (k ℕ.· 2)) ∙∙
            cong₂ _·ᵣ_
             ( ^ⁿ-even k x)
             refl
            ∙∙ expSeq'≡expSeq (-ᵣ x) (k ℕ.· 2))))
          ≡$_)


 IsUContFSequenceSin :  ∀ a b → (a<b : rat a <ᵣ rat b) →
    IsUContFSequence (intervalℙ (rat a) (rat b))
       (λ z x _ → seqΣ (λ x₁ → sinSeries x₁ x) z)
 IsUContFSequenceSin a b a<b =
   IsUContFSequenceΣSeq ((intervalℙ (rat a) (rat b))) _
    (subst (IsUContFSequence (intervalℙ (rat a) (rat b)))
      (funExt₃ λ x _ _ → ·ᵣComm _ _ ∙ sym (-1ⁿ·≡·  x _))
      λ n → IsUContinuousℙC·ᵣ (intervalℙ (rat a) (rat b)) (-1ⁿ n) _
       (isUContFSequenceExpSer a b (<ᵣWeaken≤ᵣ _ _ a<b) (suc (n ℕ.· 2))))

 IsUContFSequenceCos :  ∀ a b → (a<b : rat a <ᵣ rat b) →
    IsUContFSequence (intervalℙ (rat a) (rat b))
       (λ z x _ → seqΣ (λ x₁ → cosSeries x₁ x) z)
 IsUContFSequenceCos a b a<b =
   IsUContFSequenceΣSeq (intervalℙ (rat a) (rat b)) _
    (subst (IsUContFSequence (intervalℙ (rat a) (rat b)))
      (funExt₃ λ x _ _ → ·ᵣComm _ _ ∙ sym (-1ⁿ·≡· x _))
      λ n → IsUContinuousℙC·ᵣ (intervalℙ (rat a) (rat b)) (-1ⁿ n) _
       (isUContFSequenceExpSer a b (<ᵣWeaken≤ᵣ _ _ a<b) (n ℕ.· 2)))


-- -- sin'=cos-uder : ∀ a b → (a<b : rat a <ᵣ rat b) →
-- --       uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,
-- --        (λ x _ → sin x) is (λ x _ → cos x)
-- -- sin'=cos-uder a b a<b =
-- --    subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
-- --     (funExt₂ λ _ _ →
-- --       sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
-- --       ∙ sym (sinImpl _))
-- --     (funExt₂ λ _ _ →
-- --       sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
-- --       ∙ sym (cosImpl _))
-- --     (uCauchyDer (rat a) (rat b) a<b
-- --          (λ z x _ → seqΣ (flip cosSeries x) z)
-- --          (λ z x _ → seqΣ (flip sinSeries x) z)
-- --          uconvcos uccos ucsin uconvsin
-- --         (sinSeq'=cosSeq a b a<b))

-- --     where
-- --     ucsin : IsUContFSequence (intervalℙ (rat a) (rat b)) _
-- --     ucsin = IsUContFSequenceSin a b a<b


-- --     uconvcos : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
-- --     uconvcos =
-- --       Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
-- --          (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b)

-- --     uconvsin : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
-- --     uconvsin =
-- --       Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
-- --          (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b)


-- --     uccos : IsUContFSequence (intervalℙ (rat a) (rat b)) _
-- --     uccos = IsUContFSequenceCos a b a<b


-- -- cos'=-sin-uder : ∀ a b → (a<b : rat a <ᵣ rat b) →
-- --       uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,
-- --                 (λ x _ → cos x)
-- --               is (λ x _ → -ᵣ (sin x))
-- -- cos'=-sin-uder a b a<b =
-- --   subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
-- --     (funExt₂ λ x x∈ →

-- --         sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _
-- --           uconvcos
-- --           _
-- --           (PT.map (fst ∘ (cauchySequenceFaster
-- --             (seqΣ λ n → cosSeries n x)
-- --             λ n → (suc n) , (ℕ.≤-sucℕ {n})))
-- --            (cos-ch x)))
-- --         ∙
-- --         sym (fromCauchySequence'₁-∘+  _ 1 _ _)
-- --       ∙ sym (cosImpl _)
-- --       )
-- --     (funExt₂ λ x x∈ →
-- --        sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
-- --        ∙
-- --        sym (snd (map-fromCauchySequence'₁
-- --       1 (λ n → seqΣ (flip sinSeries x) n)
-- --        (sin-ch x)
-- --         _ -ᵣ-lip)) ∙ cong -ᵣ_ (sym (sinImpl _)))

-- --     (uCauchyDer (rat a) (rat b) a<b _ _
-- --          (isUCauchyFSequence-ᵣ _ _ uconvsin)
-- --          (λ n →
-- --            subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
-- --               (funExt₂ λ _ _ → ·ᵣComm _ _ ∙ sym (-ᵣ≡[-1·ᵣ] _))
-- --             (IsUContinuousℙC·ᵣ (intervalℙ (rat a) (rat b)) -1
-- --             _ (IsUContFSequenceSin a b a<b n)) )
-- --          (IsUContFSequenceCos a b a<b ∘ suc)
-- --          uconvcos
-- --         (cosSeq'=-sinSeq a b a<b))

-- --     where
-- --     ucsin : IsUContFSequence (intervalℙ (rat a) (rat b)) _
-- --     ucsin = IsUContFSequenceSin a b a<b


-- --     uconvcos : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
-- --     uconvcos = map-snd
-- --       (λ X x x∈ m n <n <m →
-- --         X x x∈ (suc m) (suc n) (ℕ.≤-suc <n) (ℕ.≤-suc <m))
-- --       ∘ (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
-- --          (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b))

-- --     uconvsin : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
-- --     uconvsin =
-- --       Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
-- --          (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b)


-- -- cos'=-sin-uder' : ∀ a b → (a<b : a <ᵣ b) →
-- --       uDerivativeOfℙ (intervalℙ a b) ,
-- --                 (λ x _ → cos x)
-- --               is (λ x _ → -ᵣ (sin x))
-- -- cos'=-sin-uder' a b a<b =
-- --   PT.rec2
-- --      (isPropΠ λ _ → squash₁)
-- --      (λ (a' , _ , a'<a) (b' , b<b' , _) →
-- --        uDerivativeOfℙ-restr (intervalℙ (rat a') (rat b'))
-- --          (intervalℙ a b) _ _
-- --          (λ x x∈ → isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a'<a) (fst x∈) ,
-- --                    isTrans≤ᵣ _ _ _ (snd x∈) (<ᵣWeaken≤ᵣ _ _ b<b'))
-- --          (cos'=-sin-uder a' b' (isTrans<ᵣ _ _ _ a'<a
-- --            (isTrans<ᵣ _ _ _ a<b b<b')))

-- --            )
-- --    (denseℚinℝ (a +ᵣ (rat -1)) a (isTrans<≡ᵣ _ _ _

-- --         (<ᵣ-o+ _ _ a (decℚ<ᵣ? { -1 } {0}))
-- --         (+IdR a)))
-- --    (denseℚinℝ b (b +ᵣ 1) (isTrans≡<ᵣ _ _ _
-- --         (sym (+IdR b))
-- --         (<ᵣ-o+ _ _ b (decℚ<ᵣ? {0} {1}))) )

-- -- sin'=cos-uder' : ∀ a b → (a<b : a <ᵣ b) →
-- --       uDerivativeOfℙ (intervalℙ (a) (b)) ,
-- --        (λ x _ → sin x) is (λ x _ → cos x)
-- -- sin'=cos-uder' a b a<b =
-- --   PT.rec (isPropΠ λ _ → squash₁)
-- --     (λ ((a' , b') , (a'≤a , b≤b')) →
-- --       uDerivativeOfℙ-restr
-- --         (intervalℙ (rat a') (rat b'))
-- --         (intervalℙ a b)
-- --         (λ x _ → sin x)
-- --         (λ r _ → cos r)
-- --        (λ x x∈ →
-- --           (isTrans≤ᵣ _ _ _ a'≤a (fst x∈))
-- --          , (isTrans≤ᵣ _ _ _ (snd x∈) b≤b' ))
-- --        (sin'=cos-uder a' b'
-- --          ((isTrans≤<ᵣ _ _ _ a'≤a
-- --            (isTrans<≤ᵣ _ _ _ a<b b≤b')))))
-- --    (∃enclosingℚInterval a b)

-- -- sinSeq≤expSeq : ∀ n x → seqΣ (flip sinSeries x) n ≤ᵣ
-- --                              seqΣ (expSeq (absᵣ x)) (suc (n ℕ.· 2))
-- -- sinSeq≤expSeq n x = isTrans≤ᵣ _ _ _
-- --   (sinSeq≤expSeq-1 n x)
-- --   (isTrans≤≡ᵣ _ _ _
-- --     (isTrans≡≤ᵣ _ _ _
-- --       (sym (+IdL _))
-- --       (≤ᵣ-+o _ _ _ (decℚ≤ᵣ? {0} {1}) )) --(≤ᵣMonotone+ᵣ _ _ _ _ ? ?)
-- --     (1+expSeq (n ℕ.· 2) (absᵣ x) ))

-- -- sin≤exp : ∀ x → sin x ≤ᵣ expℝ (absᵣ x)
-- -- sin≤exp x = isTrans≡≤ᵣ _ _ _ (sinImpl _) $
-- --   PT.elim2
-- --     (λ ich ich' →
-- --        isProp≤ᵣ
-- --         (fromCauchySequence'₁ _ ich)
-- --         (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
-- --     (λ ich ich' →
-- --       isTrans≤≡ᵣ _ _ _
-- --         (fromCauchySequence'≤ _ _ _ _
-- --           (flip sinSeq≤expSeq x))
-- --         (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
-- --           (λ n → suc (n ℕ.· 2) ,
-- --            subst (ℕ._≤ suc (n ℕ.· 2)) (·-identityʳ n)
-- --             (ℕ.≤-suc (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
-- --     (sin-ch x)
-- --     (expℝ-cauchySeq (absᵣ x))

-- -- cos≤exp : ∀ x → cos x ≤ᵣ expℝ (absᵣ x)
-- -- cos≤exp x = isTrans≡≤ᵣ _ _ _ (cosImpl _) $
-- --    PT.elim2
-- --     (λ ich ich' →
-- --        isProp≤ᵣ
-- --         (fromCauchySequence'₁ _ ich)
-- --         (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
-- --     (λ ich ich' →
-- --       isTrans≤≡ᵣ _ _ _
-- --         (fromCauchySequence'≤ _ _ _ _
-- --           (flip cosSeq≤expSeq x))
-- --         (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
-- --           (λ n → (n ℕ.· 2) ,
-- --            subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
-- --             ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
-- --     (cos-ch x)
-- --     (expℝ-cauchySeq (absᵣ x))


-- -- -cos≤exp : ∀ x → -ᵣ (cos x) ≤ᵣ expℝ (absᵣ x)
-- -- -cos≤exp x =
-- --    isTrans≡≤ᵣ _ _ _
-- --     (cong -ᵣ_ (cosImpl _) ∙ snd (map-fromCauchySequence'₁
-- --       1 _ _
-- --         _ -ᵣ-lip))
-- --     (PT.elim2
-- --     (λ ich ich' →
-- --        isProp≤ᵣ
-- --         (fromCauchySequence'₁ _ ich)
-- --         (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
-- --     (λ ich ich' →
-- --       isTrans≤≡ᵣ _ _ _
-- --         (fromCauchySequence'≤ _ _ _ _
-- --           (flip -cosSeq≤expSeq x))
-- --         (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
-- --           (λ n → (n ℕ.· 2) ,
-- --            subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
-- --             ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
-- --     (fst (map-fromCauchySequence'₁
-- --       1 _ _
-- --         _ -ᵣ-lip))
-- --     (expℝ-cauchySeq (absᵣ x)))


-- -- opaque
-- --  unfolding maxᵣ
-- --  pre-bounded-sin : ∀ a b → rat a <ᵣ rat b →
-- --               Bounded (intervalℙ (rat a) (rat b)) (λ x _ → sin x)
-- --  pre-bounded-sin a b a<b =
-- --    let (bd , ≤bd) = expBounded 0 (ℚ.max (ℚ.abs a) (ℚ.abs b))
-- --                      (≤ᵣ-refl _)
-- --                      (≤ℚ→≤ᵣ _ _
-- --                        (ℚ.isTrans≤ _ _ _ (ℚ.0≤abs a) (ℚ.≤max _ _)))
-- --    in bd , λ x x∈ → isTrans≤ᵣ _ _ _
-- --             (isTrans≤ᵣ _ _ _
-- --               (isTrans≡≤ᵣ _ _ _ (abs-max (sin x))
-- --                 (max≤-lem _ _ _
-- --                   (sin≤exp x)
-- --                   (subst2 _≤ᵣ_
-- --                     (sym (sin-odd x))
-- --                     (cong expℝ (sym (-absᵣ x)))
-- --                     (sin≤exp (-ᵣ x)))))
-- --               (≤absᵣ _))
-- --            (≤bd (absᵣ x) (0≤absᵣ x ,
-- --              isTrans≤≡ᵣ _ _ _
-- --                (x∈interval-bound _ _ x x∈)
-- --                (cong₂ maxᵣ (absᵣ-rat a) (absᵣ-rat b))))

-- -- opaque
-- --  unfolding maxᵣ
-- --  pre-bounded-cos : ∀ a b → rat a <ᵣ rat b →
-- --               Bounded (intervalℙ (rat a) (rat b)) (λ x _ → cos x)
-- --  pre-bounded-cos a b a<b =
-- --    let (bd , ≤bd) = expBounded 0 (ℚ.max (ℚ.abs a) (ℚ.abs b))
-- --                      (≤ᵣ-refl _)
-- --                      (≤ℚ→≤ᵣ _ _
-- --                        (ℚ.isTrans≤ _ _ _ (ℚ.0≤abs a) (ℚ.≤max _ _)))
-- --    in bd , λ x x∈ → isTrans≤ᵣ _ _ _
-- --             (isTrans≤ᵣ _ _ _
-- --               (isTrans≡≤ᵣ _ _ _ (abs-max (cos x))
-- --                 (max≤-lem _ _ _
-- --                   (cos≤exp x)
-- --                   (-cos≤exp x)))
-- --               (≤absᵣ _))

-- --            (≤bd (absᵣ x) (0≤absᵣ x ,
-- --              isTrans≤≡ᵣ _ _ _
-- --                (x∈interval-bound _ _ x x∈)
-- --                (cong₂ maxᵣ (absᵣ-rat a) (absᵣ-rat b))))

-- -- pre-uContSin : ∀ a b → rat a <ᵣ rat b →
-- --   IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x₁ _ → sin x₁)
-- -- pre-uContSin a b a<b =
-- --  subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
-- --    ((funExt₂ λ _ _ →
-- --       sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
-- --        ∙ sym (sinImpl _))
-- --       )
-- --    (snd (fromUCauchyFSequence (intervalℙ (rat a) (rat b)) _
-- --     (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
-- --          (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b))
-- --     (IsUContFSequenceSin a b a<b)))


-- -- pre-uContCos : ∀ a b → rat a <ᵣ rat b →
-- --   IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x₁ _ → cos x₁)
-- -- pre-uContCos a b a<b =
-- --  subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
-- --    ((funExt₂ λ _ _ →
-- --       sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
-- --       ∙ sym (cosImpl _)))
-- --    (snd (fromUCauchyFSequence (intervalℙ (rat a) (rat b)) _
-- --     (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
-- --          (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b))
-- --     (IsUContFSequenceCos a b a<b)))

-- -- isContinuousSin : IsContinuous sin
-- -- isContinuousSin = IsUContinuousℙ→IsContinuous _ pre-uContSin

-- -- isContinuousCos : IsContinuous cos
-- -- isContinuousCos = IsUContinuousℙ→IsContinuous _ pre-uContCos


-- -- sin²+cos²=1 : ∀ x → ((sin x) ^ⁿ 2) +ᵣ ((cos x) ^ⁿ 2) ≡ 1
-- -- sin²+cos²=1 = ≡Continuous _ _
-- --   (cont₂+ᵣ  _ _
-- --     (IsContinuous∘ _ _ (IsContinuous^ⁿ 2) isContinuousSin)
-- --     (IsContinuous∘ _ _ (IsContinuous^ⁿ 2) isContinuousCos))
-- --    (IsContinuousConst 1)
-- --   ((_∙ sin0²+cos0²≡1) ∘ ℚ.byTrichotomy 0 h)

-- --   where

-- --   h' : ∀ a b → rat a <ᵣ rat b →
-- --     (sin (rat a) ^ⁿ 2) +ᵣ (cos (rat a) ^ⁿ 2)
-- --       ≡ (sin (rat b) ^ⁿ 2) +ᵣ (cos (rat b) ^ⁿ 2)
-- --   h' a b a<b =
-- --     nullDerivative→const (rat a) (rat b)
-- --        (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ a<b)
-- --        (<ᵣWeaken≤ᵣ _ _ a<b , ≤ᵣ-refl _)
-- --       a<b
-- --       _
-- --       h

-- --     where
-- --     h : uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
-- --           (λ x _ → ((sin x) ^ⁿ 2) +ᵣ ((cos x) ^ⁿ 2)) is
-- --         (λ _ _ → rat [ pos 0 / 1+ 0 ])
-- --     h = subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
-- --       (funExt₂ λ _ _ →
-- --         cong₂ _+ᵣ_
-- --           (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
-- --           (cong₂ _·ᵣ_ (sym (·IdL _)) refl))
-- --       (funExt₂ λ _ _ →
-- --         cong₂ _+ᵣ_ (cong₂ _+ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _))
-- --            (cong₂ _+ᵣ_ (-ᵣ· _ _) (-ᵣ· _ _)
-- --              ∙ sym (-ᵣDistr _ _))
-- --           ∙ Rℝ.+InvR' _ _ refl)
-- --       (+uDerivativeℙ _ _ _ _ _
-- --         h1 h2)

-- --        where
-- --        h1 = (uDerivativeOfℙ· (rat a) (rat b) a<b
-- --           _ _ _ _
-- --           (pre-bounded-sin a b a<b)
-- --           (pre-bounded-sin a b a<b)
-- --           (pre-uContSin a b a<b)
-- --           (pre-bounded-cos a b a<b)
-- --         (sin'=cos-uder a b a<b)
-- --         (sin'=cos-uder a b a<b)
-- --         )
-- --        h2 = (uDerivativeOfℙ· (rat a) (rat b) a<b
-- --           _ _ _ _
-- --           (pre-bounded-cos a b a<b) (pre-bounded-cos a b a<b)
-- --           (pre-uContCos a b a<b)
-- --           (map-snd (λ X x x∈ → isTrans≡≤ᵣ _ _ _
-- --                (sym (-absᵣ _)) (X x x∈)) (pre-bounded-sin a b a<b))
-- --         (cos'=-sin-uder a b a<b) (cos'=-sin-uder a b a<b))

-- --   sin0²+cos0²≡1 : (sin 0 ^ⁿ 2) +ᵣ (cos 0 ^ⁿ 2) ≡ 1
-- --   sin0²+cos0²≡1 = Rℝ.+IdL' _ _ (cong (_^ⁿ 2) sin0=0 ∙ (0^ⁿ 1))
-- --     ∙ cong (_^ⁿ 2) cos0=1 ∙ 1^ⁿ 2

-- --   h : ℚ.TrichotomyRec 0
-- --        (λ z → (sin (rat z) ^ⁿ 2) +ᵣ (cos (rat z) ^ⁿ 2) ≡
-- --         (sin 0 ^ⁿ 2) +ᵣ (cos 0 ^ⁿ 2))
-- --   h .ℚ.TrichotomyRec.lt-case x x<0 =
-- --     h' x 0 (<ℚ→<ᵣ _ _ x<0)
-- --   h .ℚ.TrichotomyRec.eq-case = refl
-- --   h .ℚ.TrichotomyRec.gt-case x 0<x =
-- --     sym (h' 0 x (<ℚ→<ᵣ _ _ 0<x))


-- -- sin·sin+cos·cos=1 : ∀ x → ((sin x) ·ᵣ (sin x)) +ᵣ ((cos x) ·ᵣ (cos x)) ≡ 1
-- -- sin·sin+cos·cos=1 x =
-- --  cong₂ _+ᵣ_
-- --    (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
-- --    (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
-- --   ∙ sin²+cos²=1 x

-- -- cos·cos=1-sin·sin : ∀ x → ((cos x) ·ᵣ (cos x)) ≡ 1 -ᵣ ((sin x) ·ᵣ (sin x))
-- -- cos·cos=1-sin·sin x = sym (Rℝ.plusMinus _ _)
-- --   ∙ cong (_-ᵣ ((sin x) ·ᵣ (sin x))) (+ᵣComm _ _ ∙ sin·sin+cos·cos=1 x)
