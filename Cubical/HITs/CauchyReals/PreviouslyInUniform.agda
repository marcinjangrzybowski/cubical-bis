{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.PreviouslyInUniform where

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

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.Uniform using
  ( <ε-lemma
  ; IsUContinuousℙ·ᵣ₂
  ; IsUContinuousℙC·ᵣ
  ; IsUContinuousℙ-ᵣ∘
  ; IsUContinuousId
  ; IsUContinuousℙ-const
  ; IsUContinuousℙ+ᵣ₂
  ; IsUContinuousℙ-transl
  ; x∈interval-bound
  ; bounded-id
  ; bounded-+
  ; bounded-ᵣ
  ; -ᵣbounded
  ; bounded-·
  ; bounded-^ⁿ
  ; IsUContinuousℙ^ⁿ
  ; IsUContinuousℙ→pointwise
  ; IsUContinuousℙ→pointwiseℙ
  ; IsUContinuousℙ→IsContinuous
  ; isCauchySequence-∘+
  ; IsUCauchyFSequence-∘+
  ; IsUContFSequence-∘+
  ; fromCauchySequence'₁-≡-lem
  ; fromCauchySequence'₁-≡
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
  ; maxᵣ-dist
  ; IsUContinuousMaxᵣ
  ; DichotomyRec
  ; byDichotomyMax
  ; byDichotomyMax₂
  )
open import Cubical.HITs.CauchyReals.Power using
  ( ^ⁿ-odd
  ; ^ⁿ-even
  ; x·x≡∣x∣·∣x∣
  ; abs[x^²ⁿ]
  ; absᵣ^ⁿ
  ; 0^ⁿ
  ; 1^ⁿ
  )
open import Cubical.HITs.CauchyReals.Signs using
  ( -1ⁿ
  ; absᵣ[-1ⁿ]≡1
  ; -1ⁿ·
  ; -1ⁿ·-suc
  ; -1ⁿ·-·2
  ; -1ⁿ-suc
  ; -1ⁿ·≡·
  ; absᵣ∘-1ⁿ·
  )
open import Cubical.HITs.CauchyReals.ExponentialSeries using
  ( expSeq'
  ; expSeq'≡expSeq
  ; expSeq'NonNeg
  ; expSeqNonNeg
  ; absᵣ∘expSeq≡expSeq∘absᵣ
  ; expSeq'der
  ; expSerDer
  ; uConvExpSer
  ; uConvExpSer<ℚ
  ; uConvExpSer<ℚ-absᵣ
  ; 1+expSeq
  ; isUContFSequenceExpSer
  ; isUContFSequenceExp
  )
open import Cubical.HITs.CauchyReals.TrigBase using
  ( sinSeries
  ; cosSeries
  ; sinSeq≤expSeq-1
  ; cosSeq≤expSeq
  ; -cosSeq≤expSeq
  ; sin-conv
  ; cos-conv
  ; sin-ch
  ; cos-ch
  ; sin
  ; cos
  ; sinImpl
  ; cosImpl
  ; cos0=1
  ; sin0=0
  ; sin-odd
  ; cos-even
  ; IsUContFSequenceSin
  ; IsUContFSequenceCos
  )


-- Basic integral extensionality and uniform-continuity algebra that used to
-- live here have been migrated to Integration and Uniform.


FTOC⇒' : ∀ a b → a ≤ᵣ b
          → (f : ∀ x → x ∈ intervalℙ a b →  ℝ)

          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → (uDerivativeOfℙ (intervalℙ a b) ,
                        (λ x (a≤x , x≤b) →
                          fst (Integrate-UContinuousℙ a x a≤x
                             (λ x x∈ → f x (fst x∈ , isTrans≤ᵣ _ _ _
                               (snd x∈) x≤b))
                           (map-snd
                             (λ X → λ u v u∈ v∈ u∼v →
                              X u v ((fst u∈ , isTrans≤ᵣ _ _ _
                               (snd u∈) x≤b))
                               (((fst v∈ , isTrans≤ᵣ _ _ _
                               (snd v∈) x≤b))) u∼v)
                             ∘ ucf)))
                        is f)
FTOC⇒' a b a≤b f ucf ε = do
 (δ , X) ← FTOC⇒ a (λ x → f (clampᵣ a b x)
       (clampᵣ∈ℚintervalℙ a b a≤b x))
       (map-snd (λ X u v u∼v →
        X _ _ (clampᵣ∈ℚintervalℙ a b a≤b u)
              (clampᵣ∈ℚintervalℙ a b a≤b v)
               (clampᵣ∼ u∼v)) ∘ ucf) ε
 ∣ δ , (λ x x∈ h h∈ 0＃h ∣h∣<δ →
    let z = X x (fst x∈) h (fst h∈)
            0＃h ∣h∣<δ
     in isTrans≡<ᵣ _ _ _
         (cong absᵣ
            (cong₂ _-ᵣ_
              (cong (uncurry f)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 (∈ℚintervalℙ→clampᵣ≡  a b x x∈)))
              (cong₂ _·ᵣ_
               (cong₂ _-ᵣ_
                 (Integrate-UContinuous-≡-∈ a _ _ _ _ _ _
                   λ x' x'∈ → cong (uncurry f)
                       (Σ≡Prop (∈-isProp _)
                         (sym (∈ℚintervalℙ→clampᵣ≡  a _ x' x'∈)
                           ∙ ∈ℚintervalℙ→clampᵣ≡  a b x' (fst x'∈ ,
                             isTrans≤ᵣ _ _ _ (snd x'∈) (snd h∈)))))

                        ((Integrate-UContinuous-≡-∈ a _ _ _ _ _ _
                   λ x' x'∈ → cong (uncurry f)
                       (Σ≡Prop (∈-isProp _)
                         (sym (∈ℚintervalℙ→clampᵣ≡  a _ x' x'∈)
                           ∙ ∈ℚintervalℙ→clampᵣ≡  a b x' (fst x'∈ ,
                             isTrans≤ᵣ _ _ _ (snd x'∈) (snd x∈)))))))
                refl)))
         z) ∣₁

FTOC⇒* : ∀ a b → a ≤ᵣ b
          → (f F : ∀ x → x ∈ intervalℙ a b →  ℝ)

          → (ax⊆ab : ∀ x → (x∈ : x ∈ intervalℙ a b) →
                 ∀ y → y ∈ intervalℙ a x
                     → y ∈ intervalℙ a b)
          → (∀ x → (x∈ : x ∈ intervalℙ a b) →
                on[ a , x ]IntegralOf (λ y ≤y y≤ →
                  f y (ax⊆ab x x∈ y (≤y , y≤)))
                 is (F x x∈))
          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → uDerivativeOfℙ (intervalℙ a b) , F is f
FTOC⇒* a b a≤b f F ax⊆ab X ucf  =
  subst
    (λ F → uDerivativeOfℙ (intervalℙ a b) , F is f)
    (funExt₂ (λ y y∈ →
      let p = (λ x x∈ →
                 cong (f x) (∈-isProp (intervalℙ _ _) _ _ _))
      in Integrate-UContinuousℙ-≡ _ _ _ _ _ _
              (IsUContinuousℙ-restr _ _ _ _ ucf)
               p
            ∙ (IntegralUniq a y (fst y∈)
     _ _ _
     (snd (Integrate-UContinuousℙ a _ _ _ _))
     (X y y∈)))
     )
    (FTOC⇒' a b a≤b f ucf)


-- Uniform Cauchy/function-sequence machinery and max-distance helpers
-- have been migrated to Uniform.

opaque
 unfolding maxᵣ minᵣ
 extendℝFnLeft : ∀ (x₀ y₀ : ℝ) →
         (f : (Σ _ (x₀ <ᵣ_)) → (Σ _ (y₀ <ᵣ_)))
       → at x₀ limitOfℙ pred> x₀ , (λ x x₀<x _ → fst (f (x , x₀<x )) ) is' y₀

       → IsUContinuousℙ (pred> x₀) (curry (fst ∘ f))
       → (∀ x y → fst x ≤ᵣ fst y → fst (f x) ≤ᵣ fst (f y))
       → Σ[ f' ∈ ((Σ _ (x₀ ≤ᵣ_)) → (Σ _ (y₀ ≤ᵣ_))) ]
          (((fst (f' (_ , ≤ᵣ-refl _)) ≡ y₀) ×
            (∀ x → fst (f' (_ , (<ᵣWeaken≤ᵣ _ _ (snd x)))) ≡ fst (f x)  ))
              × IsUContinuousℙ (pred≥ x₀) (curry (fst ∘ f')))
 extendℝFnLeft x₀ y₀ f x₀lim ucf f-mon  =
   (λ x → fst g (fst x) (snd x) ,
      isTrans≤≡ᵣ _ _ _
        (≤Cont
          {f₁ = λ x → (fst g) ((maxᵣ 0 x) +ᵣ x₀)
               (isTrans≡≤ᵣ _ _ _ (sym (+IdL _))
                (≤ᵣ-+o _ _ _ (≤maxᵣ 0 x))) }
          (IsContinuousConst y₀)
           (IsContinuousWithPred∘IsContinuous _ _ _
             _
             (IsUContinuousℙ→pointwise _ _ (snd g))
             (IsContinuous∘ _ _
                 (IsContinuous+ᵣR x₀) (IsContinuousMaxL 0)))
          (λ u → y₀≤g u (isTrans≡≤ᵣ x₀ (0 +ᵣ x₀) (maxᵣ 0 (rat u) +ᵣ x₀)
        (λ i → +IdL x₀ (~ i))
        (≤ᵣ-+o 0 (maxᵣ 0 (rat u)) x₀ (≤maxᵣ 0 (rat u)))))
          (fst x -ᵣ x₀))
        (cong (uncurry (fst g))
         ((Σ≡Prop (isProp≤ᵣ _) ((cong₂ _+ᵣ_ (≤→maxᵣ 0 _ (x≤y→0≤y-x _ _ (snd x)))
         refl ∙ 𝐑'.minusPlus (fst x) x₀)))) ))
    , (g[x₀]=y₀ , λ x → g[x₀<x]=f x (<ᵣWeaken≤ᵣ x₀ (x .fst) (snd x))) ,
     snd g
  where

  f-mon-inv : ∀ x y → fst (f x) <ᵣ fst (f y) → fst x ≤ᵣ fst y
  f-mon-inv x y fx<fy = ≯ᵣ→≤ᵣ _ _
   λ y<x → ≤ᵣ→≯ᵣ _ _ (f-mon y x (<ᵣWeaken≤ᵣ _ _ y<x)) fx<fy

  g-hlp : ℚ₊ → ℚ₊ → ℝ → ℝ
  g-hlp δ δ' x =
    let z = isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ)))
        z' = isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ')))
    in maxᵣ (fst (f (x₀ +ᵣ rat (fst δ) , z)))
         (fst (f ((maxᵣ (x₀ +ᵣ rat (fst δ'))
           x) , isTrans<≤ᵣ _ _ _ z' (≤maxᵣ _ _) )))

  g-hlpCont : ∀ δ δ' → IsContinuous (g-hlp δ δ')
  g-hlpCont δ δ' = IsContinuous∘ _ _
    (IsContinuousMaxL _)
    (IsContinuousWithPred∘IsContinuous
       _ _ _ _
         (IsUContinuousℙ→pointwise _ _ ucf)
          (IsContinuousMaxL _))

  g-hlp-min-max : ∀ δ  δ' x → g-hlp δ δ x ≡ g-hlp δ (ℚ.min₊ δ' δ) x
  g-hlp-min-max δ δ' x =
   cong (g-hlp δ δ) (sym (𝐑'.minusPlus x x₀))
    ∙∙ ≡Continuous
     (λ x → g-hlp δ δ (x +ᵣ x₀))
     (λ x → g-hlp δ (ℚ.min₊ δ' δ) (x +ᵣ x₀))
    (IsContinuous∘ _ _ (g-hlpCont _ _)
      (IsContinuous+ᵣR x₀))
    ((IsContinuous∘ _ _ (g-hlpCont _ _)
      (IsContinuous+ᵣR x₀)))
    (λ q → ⊎.rec
        (λ q≤δ →
         let ineq = (Σ≡Prop (λ _ → isProp<ᵣ _ _)
              (maxᵣComm _ _ ∙ ≤→maxᵣ _ _ (isTrans≡≤ᵣ _ _ _ (+ᵣComm _ _)
               (≤ᵣ-o+ _ _ _ (≤ℚ→≤ᵣ _ _ q≤δ)))))
         in (maxᵣComm _ _ ∙ ≤→maxᵣ _ _
          (≡ᵣWeaken≤ᵣ _ _ (cong (fst ∘ f) ineq)))
          ∙
           sym (maxᵣComm _ _ ∙ ≤→maxᵣ _ _
            (f-mon _ _
              (max≤-lem _ _ _
               (≤ᵣ-o+ _ _ _ (min≤ᵣ' (rat (fst δ')) _))
              (isTrans≡≤ᵣ _ _ _ (+ᵣComm _ _) ((≤ᵣ-o+ _ _ _ (≤ℚ→≤ᵣ _ _ q≤δ))))))))
        (λ δ≤q →
          let ineq = (isTrans≤ᵣ _ _ _
                  (isTrans≤≡ᵣ _ _ _
                   (≤ᵣ-o+ _ _ _ (≤ℚ→≤ᵣ _ _ δ≤q))
                   (+ᵣComm _ _))
                  (isTrans≤≡ᵣ _ _ _
                 (≤maxᵣ _ _) (maxᵣComm _ _)))
              zz = ≤→maxᵣ _ _ ((isTrans≡≤ᵣ _ _ _ (+ᵣComm _ _)
               ((≤ᵣ-+o _ _ _ (≤ℚ→≤ᵣ _ _ δ≤q)))))
                ∙ sym (≤→maxᵣ _ _ (
                 (isTrans≡≤ᵣ _ _ _ (+ᵣComm _ _)
                  ((≤ᵣ-+o _ _ _ (isTrans≤ᵣ _ _ _
                   (≤ℚ→≤ᵣ _ _ (ℚ.min≤' _ _)) (≤ℚ→≤ᵣ _ _ δ≤q)))))))
          in ≤→maxᵣ _ _ (f-mon _ _ (isTrans≤≡ᵣ _ _ _ ineq
                (sym zz))) ∙∙ cong (fst ∘ f)
                  (Σ≡Prop (λ _ → isProp<ᵣ _ _)
                  zz) ∙∙
             sym (≤→maxᵣ _  _
                (f-mon _ _ ineq)))
     (ℚ.≤cases q (fst δ)))
       (x -ᵣ x₀)
   ∙∙
   cong (g-hlp δ (ℚ.min₊ δ' δ)) (𝐑'.minusPlus x x₀)

  g-seq : FSeq (pred≥ x₀)
  g-seq n x _ =
    let δ = /2₊ (fst (x₀lim ([ 1 / 1+ n ]  , tt)))

    in g-hlp δ δ x

  g-cauchy : IsUCauchyFSequence (pred≥ x₀) g-seq
  g-cauchy ε =
    let (1+ N , 1/N<) = ℚ.lowerBoundℕ⁻¹ (/2₊ ε)
    in suc N , λ x x∈ m n <n <m →
        let δ  , Y = x₀lim ([ 1 / 1+ n ]  , tt)
            δ' , Y' = x₀lim ([ 1 / 1+ m ]  , tt)
            zz = _
            zz' = _
            <ε/2 = isTrans<≤ᵣ _ _ _
               (Y _ zz (inl zz)
                ((isTrans≡<ᵣ _ _ _
                 (cong absᵣ (sym (L𝐑.lem--050)) ∙
                   sym (-absᵣ _) ∙ absᵣPos _ (snd (ℚ₊→ℝ₊ (/2₊ δ))))
                 (<ℚ→<ᵣ _ _ (x/2<x δ))
                 ) )) (≤ℚ→≤ᵣ _ _

                   (ℚ.isTrans≤ [ 1 / 1+ n ] [ 1 / 1+ N ] (fst ε ℚ.· [ 1 / 2 ])
                    ((fst (ℚ.invℚ₊-≤-invℚ₊ ([ pos (suc N) / 1 ] , _) ([ pos (suc n) / 1 ] , _))
                      (ℚ.≤ℤ→≤ℚ _ _ (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _) (ℕ.≤-suc (ℕ.<-weaken <n))))))
                       (ℚ.<Weaken≤ [ 1 / 1+ N ] _ 1/N<))
                       )
            <ε/2' = isTrans<≤ᵣ _ _ _
               (Y' _ zz' (inl zz')
                (isTrans≡<ᵣ _ _ _
                 (cong absᵣ (sym (L𝐑.lem--050)) ∙
                   sym (-absᵣ _) ∙ absᵣPos _ (snd (ℚ₊→ℝ₊ (/2₊ δ'))))
                 (<ℚ→<ᵣ _ _ (x/2<x δ'))
                 )) ((≤ℚ→≤ᵣ _ _

                   (ℚ.isTrans≤ [ 1 / 1+ m ] [ 1 / 1+ N ] (fst ε ℚ.· [ 1 / 2 ])
                    ((fst (ℚ.invℚ₊-≤-invℚ₊ ([ pos (suc N) / 1 ] , _) ([ pos (suc m) / 1 ] , _))
                      (ℚ.≤ℤ→≤ℚ _ _ (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _) (ℕ.≤-suc (ℕ.<-weaken <m))))))
                       (ℚ.<Weaken≤ [ 1 / 1+ N ] _ 1/N<))
                       ))
        in isTrans≡<ᵣ _ _ _
          (cong absᵣ (cong₂ _-ᵣ_
            (g-hlp-min-max (/2₊ δ) (/2₊ δ') x)
            (g-hlp-min-max (/2₊ δ') (/2₊ δ) x ∙
              cong (flip (g-hlp (/2₊ δ')) x) (ℚ₊≡
               {ℚ.min₊ _ _}
               {ℚ.min₊ (/2₊ δ') (/2₊ δ)}
               (ℚ.minComm (fst (/2₊ δ )) (fst (/2₊ δ' )))))))
          (isTrans≤<ᵣ _ _ _
            (isTrans≤ᵣ _ _ _ (maxᵣ-dist _ _ _)
              (absᵣ-triangle-midpt _ y₀ _))
            ((isTrans<≡ᵣ _ _ _ (<ᵣMonotone+ᵣ _ _ _ _
                (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) <ε/2)
                (<ε/2'))
               (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst ε))))))

  g-cs : IsUContFSequence (pred≥ x₀) g-seq
  g-cs n = IsUContinuous∘ℙ (pred≥ x₀) (IsUContinuousMaxᵣ _)
      (IsUContinuousℙ∘ℙ _ _ _ ucf
        (restrIsUContinuousℙ _ _ (IsUContinuousMaxᵣ _)))

  g : Σ-syntax ((x : ℝ) → x ∈ pred≥ x₀ → ℝ) (IsUContinuousℙ (pred≥ x₀))
  g = fromUCauchyFSequence (pred≥ x₀) g-seq g-cauchy g-cs

  g[x₀]=y₀ : fst g x₀ (≤ᵣ-refl x₀) ≡ y₀
  g[x₀]=y₀ = sym
   (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _
     _ _ _ ∣ w ∣₁)
     ∙ fromCauchySequence'≡ (λ n → g-seq n x₀ (≤ᵣ-refl x₀))
       w _
      λ ε →
        let (1+ N , 1/N<) = ℚ.lowerBoundℕ⁻¹ ε
        in ∣ suc N ,
              (λ n SN<n →
               let zz = (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
                           (<ᵣ-o+ _ _ _ (
                            (snd (ℚ₊→ℝ₊ (/2₊
                              (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))))
               in isTrans≡<ᵣ _ _ _
                  (minusComm-absᵣ _ _ ∙
                    cong (absᵣ ∘ (_-ᵣ_ y₀))
                     (cong (maxᵣ _) (cong (fst ∘ f)
                      (Σ≡Prop (λ _ → isProp<ᵣ _ _)
                       (maxᵣComm _ _ ∙ ≤→maxᵣ _ _
                         (<ᵣWeaken≤ᵣ _ _ zz)))) ∙
                       maxᵣIdem _))
                  (isTrans<ᵣ _ _ _
                  (snd (x₀lim ([ 1 / 1+ n ]  , tt))
                    _ _ (inl zz)
                    (isTrans≡<ᵣ _ _ _
                      (cong absᵣ (sym (L𝐑.lem--050)) ∙
                       sym (-absᵣ _) ∙
                        absᵣPos _ (snd
                         (ℚ₊→ℝ₊ (/2₊ (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))
                      (<ℚ→<ᵣ _ _ (x/2<x (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))
                  (<ℚ→<ᵣ _ _ (ℚ.isTrans< [ 1 / 1+ n ] [ 1 / 1+ N ] _
                    (fst (ℚ.invℚ₊-<-invℚ₊ (fromNat (suc N)) (fromNat (suc n)))
                     (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
                      (ℕ.≤-suc SN<n)))) 1/N<)))) ∣₁
   where
    w : IsCauchySequence' (flip (flip g-seq x₀) (≤ᵣ-refl x₀))
    w = isCauchyFSequenceAt _ g-seq  g-cauchy x₀ (≤ᵣ-refl x₀)


  g[x₀<x]=f : ∀ (x : Σ ℝ (_<ᵣ_ x₀)) (p : x .fst ∈ pred≥ x₀)  →
                fst g (x .fst) p ≡ fst (f x)
  g[x₀<x]=f (x , x₀<x) p = (sym
   (fromCauchySequence'-at≡fromUCauchyFSequence _ _ _ _ _ _)
     ∙ fromCauchySequence'≡ (λ n → g-seq n x (<ᵣWeaken≤ᵣ _ _ x₀<x))
       _ _
        λ ε → PT.rec
            squash₁
            (λ (δ , 0<δ , δ<fx-y₀) →
             let (1+ N , 1/N<) = ℚ.lowerBoundℕ⁻¹
                   (δ , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<δ ))

             in ∣ suc N , (λ n <n →
              let zzz = (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
                           (<ᵣ-o+ _ _ _ (
                            (snd (ℚ₊→ℝ₊ (/2₊
                              (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))))
                  zz :
                      (x₀ +ᵣ rat (fst (/2₊ (fst (x₀lim ([ 1 / 1+ n ] , tt))))))
                        ≤ᵣ x
                  zz =
                    (f-mon-inv (_ , zzz) _ (
                     isTrans<ᵣ _ _ _
                      (a-b<c⇒a<c+b _ _ _
                       (isTrans≤<ᵣ _ _ _
                         (isTrans≤≡ᵣ _ _ _ (≤absᵣ _) (minusComm-absᵣ _ _))
                           ((isTrans<ᵣ _ _ _
                      (snd (x₀lim ([ 1 / 1+ n ]  , tt))
                        _ _ (inl zzz)
                        (isTrans≡<ᵣ _ _ _
                          (cong absᵣ (sym (L𝐑.lem--050)) ∙
                           sym (-absᵣ _) ∙
                            absᵣPos _ (snd
                             (ℚ₊→ℝ₊ (/2₊ (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))
                          (<ℚ→<ᵣ _ _ (x/2<x (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))
                      (<ℚ→<ᵣ _ _ (ℚ.isTrans< [ 1 / 1+ n ] [ 1 / 1+ N ] _
                        (fst (ℚ.invℚ₊-<-invℚ₊ (fromNat (suc N)) (fromNat (suc n)))
                         (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
                          (ℕ.≤-suc <n)))) 1/N<))))))
                          (a<b-c⇒a+c<b _ _ _ δ<fx-y₀)))
              in isTrans≡<ᵣ _ _ _
                  (cong absᵣ (𝐑'.+InvR' _ _
                    (≤→maxᵣ _ _ ((f-mon _ _ (≤maxᵣ _ _)))
                     ∙ cong (fst ∘ f)
                      (Σ≡Prop (isProp<ᵣ _)
                       (≤→maxᵣ _ _ zz))))
                 ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))) ∣₁)
             (denseℚinℝ _ _ (x<y→0<y-x _ _ (snd (f (x , x₀<x))))))



  y₀≤g : (u : ℚ) → (p : x₀ ≤ᵣ maxᵣ 0 (rat u) +ᵣ x₀) → y₀ ≤ᵣ fst g (rat (ℚ.max 0 u) +ᵣ x₀) p
  y₀≤g = ℚ.byTrichotomy 0 w
   where
   w : ℚ.TrichotomyRec 0 λ z →
                            (p : x₀ ≤ᵣ maxᵣ 0 (rat z) +ᵣ x₀) →
                            y₀ ≤ᵣ fst g (rat (ℚ.max 0 z) +ᵣ x₀) p
   w .ℚ.TrichotomyRec.lt-case m m<0 _ =

     ≡ᵣWeaken≤ᵣ y₀ (fst g (rat (ℚ.max 0 m) +ᵣ x₀ ) _) (sym g[x₀]=y₀ ∙
       cong (uncurry (fst g)) (Σ≡Prop (isProp≤ᵣ _)
        (sym (𝐑'.+IdL' _ x₀ (maxᵣComm 0 (rat m) ∙
          ≤→maxᵣ (rat m) 0 (<ᵣWeaken≤ᵣ (rat m) 0 (<ℚ→<ᵣ m 0 m<0))))))  )

   w .ℚ.TrichotomyRec.eq-case _ = ≡ᵣWeaken≤ᵣ _ _
     (sym g[x₀]=y₀ ∙
      cong (uncurry (fst g)) (Σ≡Prop (isProp≤ᵣ _)
       (sym (𝐑'.+IdL' _ _ refl))))
   w .ℚ.TrichotomyRec.gt-case m 0<m p =
     isTrans≤≡ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _
      (snd (f (rat (ℚ.max 0 m) +ᵣ x₀ , isTrans≡<ᵣ _ _ _
       (sym (+IdL _))
       (<ᵣ-+o _ _ x₀ (isTrans<≡ᵣ _ _ _ (<ℚ→<ᵣ _ _ 0<m)
         (cong rat (sym (ℚ.≤→max 0 m (ℚ.<Weaken≤ 0 m 0<m))))))))))
      (sym (g[x₀<x]=f
       (rat (ℚ.max 0 m) +ᵣ x₀ , _) p) )



-- extendℝFnLeft< : ∀ (x₀ y₀ x₁ y₁ : ℝ) → x₀ <ᵣ x₁
--       → (f : (Σ _ (_∈ ointervalℙ x₀ x₁)) → (Σ _ (_∈ ointervalℙ y₀ y₁)))
--       → at x₀ limitOfℙ (ointervalℙ x₀ x₁) , (λ x x∈ _ → fst (f (x , x∈ )))
--          is' y₀

--       → IsUContinuousℙ (ointervalℙ x₀ x₁) (curry (fst ∘ f))
--       → (∀ x y → fst x ≤ᵣ fst y → fst (f x) ≤ᵣ fst (f y))
--       → Σ[ f' ∈ ((Σ _ (_∈ pred≤< x₀ x₁)) → (Σ _ (_∈ pred≤< y₀ y₁))) ]
--          ((∀ x∈ → (fst (f' (x₀ , x∈)) ≡ y₀) ×
--            (∀ x x∈ → fst (f' (fst x , x∈)) ≡ fst (f x)  ))
--              × IsUContinuousℙ (pred≤< x₀ x₁) (curry (fst ∘ f')))
-- extendℝFnLeft< = {!!}

opaque
 extendℝFnRight : ∀ (x₀ y₀ : ℝ) →
         (f : (Σ _ (_<ᵣ x₀)) → (Σ _ (_<ᵣ y₀)))
       → at x₀ limitOfℙ pred< x₀ , (λ x x<x₀ _ → fst (f (x , x<x₀ )) ) is' y₀
       → IsUContinuousℙ (pred< x₀) (curry (fst ∘ f))
       → (∀ x y → fst x ≤ᵣ fst y → fst (f x) ≤ᵣ fst (f y))
       → Σ[ f' ∈ ((Σ _ (_≤ᵣ x₀)) → (Σ _ (_≤ᵣ y₀))) ]
          (((fst (f' (_ , ≤ᵣ-refl _)) ≡ y₀) ×
            (∀ x → fst (f' (_ , (<ᵣWeaken≤ᵣ _ _ (snd x)))) ≡ fst (f x)  ))
              × IsUContinuousℙ (pred≤ x₀) (curry (fst ∘ f')))
 extendℝFnRight x₀ y₀ f x x₁ x₂ =
   Iso.fun (reverseHalfLineFn' x₀ y₀) (fst w) ,
     ((cong (-ᵣ_ ∘ fst ∘ (w .fst)) (Σ≡Prop (λ _ → isProp≤ᵣ _ _)
       refl)
     ∙∙ cong (-ᵣ_) (fst (fst (snd w))) ∙∙
     -ᵣInvol _) ,
     λ (x , x<x₀) →
       cong (-ᵣ_ ∘ fst ∘ (w .fst)) (Σ≡Prop (λ _ → isProp≤ᵣ _ _)
       refl)
        ∙∙ cong (-ᵣ_) (snd (fst (snd w)) (-ᵣ x , -ᵣ<ᵣ _ _ x<x₀ ))
        ∙∙ (-ᵣInvol _ ∙ cong (fst ∘ f)
         (Σ≡Prop (λ _ → isProp<ᵣ _ _) (-ᵣInvol _)))) ,
          IsUContinuousℙ-ᵣ∘ _ _ (IsUContinuousℙ∘ℙ (pred≤ x₀) (pred≥ (-ᵣ x₀))
            (λ x x∈ → -ᵣ≤ᵣ _ _ x∈)
            (snd (snd w))
            (
             restrIsUContinuousℙ _ _
              (Lipschitiz→IsUContinuous 1 -ᵣ_ -ᵣ-lip)))


  where
  ww : at -ᵣ x₀ limitOfℙ pred> (-ᵣ x₀) ,
        (λ x₃ x₀<x _ →
           -ᵣ
            f
            (-ᵣ x₃ ,
             isTrans<≡ᵣ (-ᵣ x₃) (-ᵣ (-ᵣ x₀)) x₀ (-ᵣ<ᵣ (-ᵣ x₀) x₃ x₀<x)
             (-ᵣInvol x₀))
            .fst)
        is' (-ᵣ y₀)
  ww ε .fst = x ε .fst
  ww ε .snd r r∈ x＃r <ε =
    isTrans≡<ᵣ _ _ _
     (cong absᵣ (sym (-ᵣDistr _ _) ) ∙
      sym (-absᵣ _))
     (x ε .snd (-ᵣ r) (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ r∈) (-ᵣInvol _))
      (subst (_＃ _) (-ᵣInvol _) (-＃ _ _ x＃r))
      (isTrans≡<ᵣ _ _ _ ((-absᵣ _)
       ∙ cong absᵣ (cong -ᵣ_ (cong₂ _+ᵣ_ refl (sym (sym (-ᵣInvol _))))
        ∙ -ᵣDistr _ _ )) <ε))

  w : Σ-syntax (Σ ℝ (_≤ᵣ_ (-ᵣ x₀)) → Σ ℝ (_≤ᵣ_ (-ᵣ y₀)))
       (λ f' →
          ((fst (f' (-ᵣ x₀ , ≤ᵣ-refl (-ᵣ x₀))) ≡ -ᵣ y₀) ×
           ((x₃ : Σ ℝ (_<ᵣ_ (-ᵣ x₀))) →
            fst (f' (x₃ .fst , <ᵣWeaken≤ᵣ (-ᵣ x₀) (x₃ .fst) (snd x₃))) ≡
            fst (Iso.inv (reverseHalfLineFnStrict' x₀ y₀) f x₃)))
          × IsUContinuousℙ (pred≥ (-ᵣ x₀)) (curry ((λ r → fst r) ∘ f')))
  w = extendℝFnLeft (-ᵣ x₀) (-ᵣ y₀)
        (Iso.inv (reverseHalfLineFnStrict' x₀ y₀)
          f)
         ww
         (IsUContinuousℙ-ᵣ∘ _ _ (IsUContinuousℙ∘ℙ (pred> (-ᵣ x₀)) (pred< x₀)
            (λ x x∈ → isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ x∈) (-ᵣInvol _))
            x₁
            (restrIsUContinuousℙ _ _
              (Lipschitiz→IsUContinuous 1 -ᵣ_ -ᵣ-lip))))
         λ x₃ y x₄ → -ᵣ≤ᵣ _ _ (x₂ _ _ (-ᵣ≤ᵣ _ _ x₄))


-- extendℝFnRight≤ : ∀ (x₀ y₀ : ℝ) →
--         (f : (Σ _ (_<ᵣ x₀)) → (Σ _ (_<ᵣ y₀)))
--       → at x₀ limitOfℙ pred< x₀ , (λ x x<x₀ _ → fst (f (x , x<x₀ )) ) is' y₀
--       → IsUContinuousℙ (pred< x₀) (curry (fst ∘ f))
--       → (∀ x y → fst x ≤ᵣ fst y → fst (f x) ≤ᵣ fst (f y))
--       → Σ[ f' ∈ ((Σ _ (_≤ᵣ x₀)) → (Σ _ (_≤ᵣ y₀))) ]
--          (((fst (f' (_ , ≤ᵣ-refl _)) ≡ y₀) ×
--            (∀ x → fst (f' (_ , (<ᵣWeaken≤ᵣ _ _ (snd x)))) ≡ fst (f x)  ))
--              × IsUContinuousℙ (pred≤ x₀) (curry (fst ∘ f')))
-- extendℝFnRight≤ x₀ y₀ f x x₁ x₂ = {!!}


-- extendℝFnBothSides : ∀ (x₀ y₀ x₁ y₁ : ℝ) → x₀ <ᵣ x₁ →
--         (f : (Σ _ (_∈ ointervalℙ x₀ x₁)) → (Σ _ (_∈ ointervalℙ y₀ y₁)))

--       → at x₀ limitOfℙ (ointervalℙ x₀ x₁)
--              , (λ x x∈ _ → fst (f (x , x∈ ))) is' y₀
--       → at x₁ limitOfℙ (ointervalℙ x₀ x₁)
--              , (λ x x∈ _ → fst (f (x , x∈ ))) is' y₁
--       → IsUContinuousℙ (ointervalℙ x₀ x₁) (curry (fst ∘ f))
--       → (∀ x y → fst x ≤ᵣ fst y → fst (f x) ≤ᵣ fst (f y))
--       → Σ[ f' ∈ ((Σ _ (_∈ intervalℙ x₀ x₁)) → (Σ _ (_∈ intervalℙ y₀ y₁))) ]
--           ( (((∀ x∈ → fst (f' (x₀ , x∈)) ≡ y₀)) ×
--              ((∀ x∈ → fst (f' (x₁ , x∈)) ≡ y₁)))
--           × ((∀ x x∈ → fst (f' ((fst x) , x∈)) ≡ fst (f x)  )))
--            × IsUContinuousℙ (intervalℙ x₀ x₁) (curry (fst ∘ f'))

-- extendℝFnBothSides x₀ y₀ x₁ y₁ x₀<x₁ f lim₀ lim₁ ucf f-mon =
--   {!!}
--  where
--   wL : _
--   wL = extendℝFnLeft< x₀ y₀ x₁ y₁ x₀<x₁ f lim₀ ucf f-mon

--   wR : {!!}
--   wR = {!!}

opaque
 nth-rootNonNegDef : ∀ (n : ℕ₊₁) → Σ (Σ ℝ (_≤ᵣ_ 0) → Σ ℝ (_≤ᵣ_ 0))
                                 (λ f' →
                                    ((fst (f' (0 , ≤ᵣ-refl 0)) ≡ 0) ×
                                     ((x : Σ ℝ (_<ᵣ_ 0)) →
                                      fst (f' (x .fst , <ᵣWeaken≤ᵣ 0 (x .fst) (snd x))) ≡
                                      root (1+ n .ℕ₊₁.n) (x .fst , x .snd) .fst))
                                    × IsUContinuousℙ (pred≥ 0) (curry ((λ r → fst r) ∘ f')))
 nth-rootNonNegDef n@(1+ n') = extendℝFnLeft 0 0
   (root n)
    (λ ε → (ε ℚ₊^ⁿ suc n') ,
      λ r r∈ x＃r x →
        isTrans<≡ᵣ _ _ _
         (isTrans≡<ᵣ _ _ _
           ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ (snd (root (1+ n .ℕ₊₁.n) (r , r∈))))
           (ₙ√-StrictMonotone n (subst2 _<ᵣ_
            ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ r∈)
            (sym (cong fst (^ℤ-rat _ (pos (suc n')))))
            x)))
           (cong fst (Iso.leftInv (nth-pow-root-iso n)
            (ℚ₊→ℝ₊ ε))) )
    (uContRoot n) λ _ _ → ₙ√-Monotone n


nth-rootNonNeg : ℕ₊₁ → Σ ℝ (_≤ᵣ_ 0) → Σ ℝ (_≤ᵣ_ 0)
nth-rootNonNeg n = fst (nth-rootNonNegDef n)

nth-rootNonNeg0 : ∀ n (p : 0 ≤ᵣ 0) → 0 ≡ fst (nth-rootNonNeg n (0 , p))
nth-rootNonNeg0 n p = sym (fst (fst (snd (nth-rootNonNegDef n))))
  ∙ cong (λ p → fst (nth-rootNonNeg n (0 , p)))
   (isProp≤ᵣ 0 0 _ _)

-- Interval boundedness and boundedness closure lemmas have been migrated to
-- Uniform.

IsUCauchyFSequenceExp : ∀ a b → a <ᵣ b →
               ∥ (IsUCauchyFSequence (intervalℙ a b)
                      λ n x _ → seqΣ (expSeq x) n) ∥₁
IsUCauchyFSequenceExp a b a<b =
 PT.map (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ a b) (λ n x _ → expSeq x n))) (uConvExpSer a b a<b )


uCauchy∫ : ∀ a b → a ≤ᵣ b →
              (fₙ Fₙ : ℕ → ∀ x → x ∈ intervalℙ a b → ℝ)
            → (∀ n x x∈ →
                on[ a , x ]IntegralOf (λ x ≤x x≤ → fₙ n x (≤x ,
                  isTrans≤ᵣ _ _ _ x≤ (snd x∈)))
                  is (Fₙ n) x x∈)
            → (icf : IsUCauchyFSequence (intervalℙ a b) fₙ)
            → ∀ ucf
            → ∀ iucF ucF → ∀ x x∈
            → on[ a , x ]IntegralOf
                    (λ x ≤x x≤ →
                       fst (fromUCauchyFSequence _ _ icf ucf) x
                        (≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)))
                   is
                 (fst (fromUCauchyFSequence (intervalℙ a b) Fₙ iucF ucF) x x∈)

uCauchy∫ a b a≤b fₙ Fₙ fₙ≡∫Fₙ icf ucf iucF uF x x∈ ε = do
  (η₊ , b-a<η₊) ← ∃ℚ₊LargerThanℝ₀₊ ((b -ᵣ a) , x≤y→0≤y-x _ _ a≤b)
  let Nf , Xf = IsUCauchyFSequence-lim (intervalℙ a b)
              fₙ icf ucf
        ((/2₊ (/2₊ ε)) ℚ₊· invℚ₊ η₊)
      NF , XF = IsUCauchyFSequence-lim (intervalℙ a b) _
                 iucF uF (/2₊ (/2₊ ε))
      Nf⊔NF = ℕ.max Nf NF
  (δ , Xδ) ← fₙ≡∫Fₙ (suc Nf⊔NF) x x∈ (/2₊ ε)
  return
    (δ , λ tp msh≤ →
          fst (∼≃abs<ε _ _ ε)
              (subst∼ (ℚ.+Comm _ _ ∙  (ℚ.+Assoc _ _ _)
                ∙ cong₂ ℚ._+_ (ℚ.ε/2+ε/2≡ε (fst (/2₊ ε))) refl
                 ∙ ℚ.ε/2+ε/2≡ε (fst ε))
                (triangle∼
                  (triangle∼ {ε = (/2₊ (/2₊ ε))}
                     (sym∼ _ _ _ $ invEq (∼≃abs<ε _ _ (/2₊ (/2₊ ε)))
                        (isTrans≡<ᵣ _ _ _
                          (cong absᵣ (riemannSum- (snd tp) _ _
                           ∙ riemannSum-clamp (snd tp) _))
                          (isTrans≤<ᵣ _ _ _
                            (isTrans≤ᵣ _ _ _
                             (riemannSum'-absᵣ≤ (snd tp) _)
                             (riemannSum'≤ (snd tp) _ _
                               λ r ≤x x≤ →
                                <ᵣWeaken≤ᵣ _ _
                                  (Xf _ _ (suc Nf⊔NF)
                                  (ℕ.suc-≤-suc  (ℕ.left-≤-max {Nf} {NF})))))
                            (isTrans≡<ᵣ _ _ _
                              (riemannSum'Const (snd tp) _
                               ∙ cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl
                               ∙ sym (·ᵣAssoc _ _ _)
                               ∙ cong₂ _·ᵣ_ refl (·ᵣComm _ _))
                              (isTrans<≡ᵣ _ _ _
                                 (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ (/2₊ (/2₊ ε)))
                                  (isTrans≡<ᵣ _ _ _
                                    (cong₂ _·ᵣ_ refl (sym (invℝ₊-rat η₊)))
                                    (invEq (z/y<x₊≃z<y₊·x _ _ _)
                                     (isTrans<≡ᵣ _ _ _
                                       (isTrans≤<ᵣ _ _ _
                                         (≤ᵣ-+o _ _ (-ᵣ a) (snd x∈)) b-a<η₊)
                                       (sym (·IdR _))))))
                                 (·IdR _))))))
                    (invEq (∼≃abs<ε _ _ (/2₊ ε)) (Xδ tp msh≤)))
                  (invEq (∼≃abs<ε _ _ (/2₊ (/2₊ ε))) (XF x x∈ (suc Nf⊔NF)
                    (ℕ.suc-≤-suc (ℕ.right-≤-max {NF} {Nf})))))))

Integral-additive : ∀ a b c a≤b b≤c → ∀ f s s' s+s' →
  on[ a , b ]IntegralOf (λ x ≤x x≤ → f x ≤x (isTrans≤ᵣ _ _ _ x≤ b≤c)) is s →
  on[ b , c ]IntegralOf (λ x ≤x x≤ → f x (isTrans≤ᵣ _ _ _ a≤b ≤x ) x≤) is s' →
  on[ a , c ]IntegralOf f is s+s' →
  s +ᵣ s' ≡ s+s'
Integral-additive a b c a≤b b≤c f s s' s+s' ∫ab ∫bc ∫ac =
  Integral'-additive a b c a≤b b≤c
   (λ x → f (clampᵣ a c x)
     (≤clampᵣ a c x (isTrans≤ᵣ _ _ _ a≤b b≤c))
     (clamp≤ᵣ a c x))
   s s' s+s'
     (Integral'≡ _ _ a≤b  _ _
         s (λ x x∈@(≤x , x≤) →
              cong (uncurry (uncurry ∘ f))
         (Σ≡Prop (∈-isProp (intervalℙ a c))
           (sym (∈ℚintervalℙ→clampᵣ≡  a b x x∈) ∙
             ∈ℚintervalℙ→clampᵣ≡  a c x
               (≤x , isTrans≤ᵣ _ _ _ x≤ b≤c))))
         (invEq (clampᵣ-IntegralOf' a b a≤b _ s) ∫ab))
        (Integral'≡ _ _ b≤c  _ _
         s' (λ x x∈@(≤x , x≤) →
              cong (uncurry (uncurry ∘ f))
         (Σ≡Prop (∈-isProp (intervalℙ a c))
           ((sym (∈ℚintervalℙ→clampᵣ≡  b c x x∈) ∙
             ∈ℚintervalℙ→clampᵣ≡  a c x
               (isTrans≤ᵣ _ _ _ a≤b ≤x , x≤ )))))
          (invEq (clampᵣ-IntegralOf' b c b≤c _ s') ∫bc))
    (invEq (clampᵣ-IntegralOf' a c (isTrans≤ᵣ _ _ _ a≤b b≤c)
     (uncurry ∘ f) s+s') ∫ac)

FTOC⇐'' : ∀ a b (a<b : a <ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → uDerivativeOfℙ (intervalℙ a b) , F is f
          → ∀ x x∈
          → on[ a , x ]IntegralOf
              (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is
              (F x x∈ -ᵣ F a (≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _ a<b ))
FTOC⇐'' a b a<b f F ucf fd x x∈ =
  PT.rec (isPropΠ λ _ → squash₁)
    (⊎.rec
     (λ x<b →
       let zz = FTOC⇐ x b x<b
                (λ x₁ (≤x , x≤)
                  → f x₁ (isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤))
                (λ x₁ (≤x , x≤)
                  → F x₁ (isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤))
                  (IsUContinuousℙ-restr _ _ _
                    (λ x (≤x , x≤) → isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤) ucf)
                   (uDerivativeOfℙ-restr _ _ _ _
                    (λ x (≤x , x≤) → isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤) fd)
           zzzW = (snd (Integrate-UContinuousℙ a x (fst x∈) _
                           ((IsUContinuousℙ-restr _ _ _
                        (λ x (≤x , x≤) →
                         ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) ucf))))
           zzz = Integral-additive a x b (fst x∈) (snd x∈)
                        _ _ _ _
                        zzzW
                        zz
                        (FTOC⇐ a b a<b _ _ ucf fd)
       in subst (on[ a , x ]IntegralOf
              (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is_)
               (sym (𝐑'.plusMinus _ _)
                ∙∙ cong₂ _-ᵣ_ zzz
                   (cong₂ _-ᵣ_
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl)))
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl))))
                ∙∙ L𝐑.lem--062)
               zzzW)
      λ a<x →
       subst (on[ a , x ]IntegralOf _ is_)
        (cong₂ _-ᵣ_
         (cong (uncurry F)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 refl))
        (cong (uncurry F)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 refl)))
        (FTOC⇐ a x a<x
         (λ x₁ (≤x , x≤)
           → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈)))
         (λ x₁ (≤x , x≤)
           → F x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈)))
           (IsUContinuousℙ-restr _ _ _
             (λ x (≤x , x≤) → ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) ucf)
            (uDerivativeOfℙ-restr _ _ _ _
             (λ x (≤x , x≤) → ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) fd)))
    (Dichotomyℝ' a x b a<b)


uCauchyDer : ∀ a b → a <ᵣ b → ∀ fₙ Fₙ →
             ∀ (icf : IsUCauchyFSequence (intervalℙ a b) fₙ)

             uf uF
             (icF : IsUCauchyFSequence (intervalℙ a b) Fₙ)
             → (∀ n → uDerivativeOfℙ (intervalℙ a b) , Fₙ n is fₙ n)
             → uDerivativeOfℙ (intervalℙ a b) ,
                  (fst (fromUCauchyFSequence _ _ icF uF))
                  is
                  (fst (fromUCauchyFSequence _ _ icf uf))
uCauchyDer a b a<b fₙ Fₙ  icf uf uF icF Fₙ'=fₙ =
   uDerivativeℙ-cancelConst
   _ _ _ _ uzu2
 where
 a≤b = <ᵣWeaken≤ᵣ a b a<b
 F-F-ucfs : IsUContFSequence (intervalℙ a b)
      (λ n x₁ x∈₁ → Fₙ n x₁ x∈₁ -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
 F-F-ucfs n = IsUContinuousℙ+ᵣ₂ _ _ _
    (uF n)
    (IsUContinuousℙ-const _ _)

 icf-a = isUCauchyFSequence-ᵣ _ _
                   (map-snd (λ X _ _ m n x₃ x₄ →
                     X _ _ m n x₃ x₄)
                     ∘ icF)

 F-F-uchfs : IsUCauchyFSequence (intervalℙ a b)
      (λ n x₁ x∈₁ → Fₙ n x₁ x∈₁ -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
 F-F-uchfs = isUCauchyFSequence+ᵣ _ _ _
    icF icf-a

 icaFa :
      IsCauchySequence' (λ z → -ᵣ Fₙ z a (≤ᵣ-refl a , a≤b))
 icaFa =
   fst (map-fromCauchySequence'
  1 _ (isCauchyFSequenceAt _ _ icF a (≤ᵣ-refl a , a≤b))
   _ -ᵣ-lip)

 uzu2 : uDerivativeOfℙ intervalℙ a b ,
        (λ r z → fst
           (fromUCauchyFSequence (intervalℙ a b)
            Fₙ icF uF)
           r z +ᵣ _)
        is
        (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf .fst)
 uzu2 = subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
           (funExt₂ λ x x∈@(≤x , x≤) →
              IntegralUniq a x (≤x) _ _ _
             (snd ((Integrate-UContinuousℙ a x ≤x
              (λ x₁ x∈₁ →
                 fromUCauchyFSequence (intervalℙ a b) fₙ icf uf .fst x₁
                 (fst x∈₁ , isTrans≤ᵣ x₁ x b (snd x∈₁) x≤))
              (map-snd
               (λ X u v u∈ v∈ →
                  X u v (fst u∈ , isTrans≤ᵣ u x b (snd u∈) x≤)
                  (fst v∈ , isTrans≤ᵣ v x b (snd v∈) (x∈ .snd)))
               ∘ snd (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf)))))
             (uCauchy∫ _ _ a≤b fₙ
                     (λ n x x∈ → Fₙ n x x∈ -ᵣ Fₙ n a (≤ᵣ-refl _ , a≤b))
                    (λ n x x∈ →
                       FTOC⇐'' a b a<b (fₙ n) (Fₙ n) (uf n)
                     (Fₙ'=fₙ n) x x∈)
                      icf uf
                      F-F-uchfs
                      F-F-ucfs
                      x x∈)
               ∙ sym (fromUCauchyFSequence-+ (intervalℙ a b) _ _ _ _
                 icf-a
                 (λ n → IsUContinuousℙ-const _ _ )
                 _ _
                    x _)
                 ∙ cong₂ _+ᵣ_ refl
                  (sym
                   (fromCauchySequence'₁≡fromUCauchyFSequence
                    _ _ _ _ _ _ ∣ icaFa ∣₁)))
           refl
           (FTOC⇒' a b a≤b _
            (snd (fromUCauchyFSequence (intervalℙ a b) fₙ icf
                 uf)))

expℝ0=1 : expℝ 0 ≡ 1
expℝ0=1 = fromCauchySequence'₁≡
  (seqΣ (expSeq 0)) _ 1
   λ ε → ∣ 0 , (λ n (n' , p) →
    isTrans≡<ᵣ _ _ _
     (cong absᵣ (𝐑'.+InvR' _ _
       ((cong (seqΣ (expSeq 0)) (sym p ∙ ℕ.+-suc _ _))
          ∙ sym (1+expSeq _ _)  ∙
          𝐑'.+IdR' _ _
            (seqSumUpTo≡seqSumUpTo' _ _ ∙
              (cong seqΣ' (funExt λ k → sym (expSeq'≡expSeq _ _) ∙
                𝐑'.0LeftAnnihilates' _ _ (0^ⁿ _))
               ≡$ (n' ℕ.+ 0)) ∙ seqSumUpToConst 0 _ ∙
                𝐑'.0LeftAnnihilates _) )) ∙ absᵣ0)
     (snd (ℚ₊→ℝ₊ ε))) ∣₁


expℚ-bound : ∀ (x : ℚ) → 0 ℚ.≤ x → Σ[ q ∈ ℚ₊ ] expℝ (rat x) <ᵣ rat (fst q)
expℚ-bound x = ⊎.rec
   (λ 0=x → 2 , isTrans≡<ᵣ _ _ _
     (cong (expℝ ∘ rat) (sym 0=x) ∙ expℝ0=1)
       (decℚ<ᵣ? {1} {2}))
   (λ 0<x →
     let N , X = fromCauchySequence'-lim _
             (fst (IsConvSeries'≃IsCauchySequence'Sum (expSeq (rat x)))
               (expSeriesConvergesAtℚ₊ x 0<x)) 1

         q , p = expSeries-rat x (suc N)
         Z : ℚ.0< (1 ℚ.+ ℚ.abs q)
         Z = ℚ.<→0< (1 ℚ.+ ℚ.abs q) (ℚ.<≤Monotone+ 0 _ 0 _
            (ℚ.decℚ<? {0} {1}) (ℚ.0≤abs q))
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
          (fromCauchySequence'₁-≡-lem (seqΣ (expSeq (rat x))) _ ∣ _ ∣₁) ZZ)
   ∘ (ℚ.≤→<⊎≡ 0 x)


monotone-expℝ : ∀ a b → 0 ≤ᵣ a → a ≤ᵣ b → expℝ a ≤ᵣ expℝ b
monotone-expℝ a b 0≤a a≤b =
  fromCauchySequence'₁≤ _ _ _ _
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

expBounded : ∀ a b → 0 ≤ᵣ rat a →  rat a ≤ᵣ rat b →
  Bounded (intervalℙ (rat a) (rat b))
          (λ x _  → expℝ x)
expBounded a b 0≤a a≤b =
  let q₊ , X = expℚ-bound b (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _ 0≤a a≤b) )
  in q₊ , λ x x∈ → isTrans≤ᵣ _ _ _
        (isTrans≡≤ᵣ _ _ _
          (absᵣPos _ (expℝ-pos x (isTrans≤ᵣ _ _ _ 0≤a (fst x∈)) ))
          (monotone-expℝ _ _ (isTrans≤ᵣ _ _ _ 0≤a (fst x∈))
            (snd x∈)))
        (<ᵣWeaken≤ᵣ _ _ X)




uDerivativeOfℙ^n : ∀ a b → rat a <ᵣ rat b
  → ∀ n
  → uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → x ^ⁿ (suc n))
    is λ x _ → fromNat (suc n) ·ᵣ (x ^ⁿ n)
uDerivativeOfℙ^n a b a<b zero =
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → sym (·IdL _))
    (funExt₂ λ _ _ → sym (·IdL _))
    (uDerivativeℙ-id _)
uDerivativeOfℙ^n a b a<b (suc n) =
 subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → x ^ⁿ (suc (suc n))) is_)
    (funExt₂ λ x _ →
      (+ᵣComm _ _ ∙ cong₂ _+ᵣ_
       refl (sym (·ᵣAssoc _ _ _)) ∙
       sym (·DistR+ _ _ _) ∙
        cong (_·ᵣ ((x ^ⁿ n) ·ᵣ idfun ℝ x))
         (+ᵣ-rat _ _ ∙ cong rat (ℚ.ℕ+→ℚ+ _ _))))
    (uDerivativeOfℙ· (rat a) (rat b) a<b
      _ _ _ _ (bounded-^ⁿ a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b) (suc n))
              (bounded-id a b)
              (IsUContinuousℙ^ⁿ a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b) (suc n))
              (1 , λ _ _ → ≡ᵣWeaken≤ᵣ _ _ (absᵣ-rat 1))
      (uDerivativeOfℙ^n a b a<b n)
      (uDerivativeℙ-id _))


expSer'UDer : ∀ a b → rat a <ᵣ rat b → ∀ n →
      uDerivativeOfℙ intervalℙ (rat a) (rat b)
                           , (λ r _ → expSeq' r (suc n)) is
                             (λ r _ → expSeq' r n)
expSer'UDer a b a<b n =
  let z = C·uDerivativeℙ _ (fst 1/n!)
            _ _
            (uDerivativeOfℙ^n a b a<b n)
  in subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → ·ᵣComm _ _)
    (funExt₂ λ _ _ →
      ·ᵣAssoc _ _ _  ∙ ·ᵣComm _ _ ∙
       cong₂ _·ᵣ_ refl
        (cong₂ _·ᵣ_ (cong (fst ∘ invℝ₊)
           ((ℝ₊≡ (cong rat (sym (ℚ.ℕ·→ℚ· (suc n) (n !)))
             ∙ rat·ᵣrat _ _)))
           ∙ cong fst (invℝ₊· (ℚ₊→ℝ₊ _)
             ((ℚ₊→ℝ₊ (_ , ℚ.<→0< ([ pos (n !) / 1 ])
               (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! n)))))))
                ∙ ·ᵣComm _ _) refl
         ∙ [x/₊y]·yᵣ _ _))
    z


 where
 1/n! = invℝ₊ $ ℚ₊→ℝ₊ ([ pos (suc n !) / 1 ] ,
  ℚ.<→0< ([ pos ((suc n) !) / 1 ])
   (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.0<! (suc n)))))


expSerUDer : ∀ a b → rat a <ᵣ rat b → ∀ n →
      uDerivativeOfℙ intervalℙ (rat a) (rat b)
                           , (λ r _ → expSeq r (suc n)) is
                             (λ r _ → expSeq r n)
expSerUDer a b a<b n =
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
   (funExt₂ (λ x _ → expSeq'≡expSeq x (suc n)))
   (funExt₂ (λ x _ → expSeq'≡expSeq x n))
   (expSer'UDer a b a<b n)

expSeqUDer : ∀ a b → rat a <ᵣ rat b → ∀ n →
      uDerivativeOfℙ intervalℙ (rat a) (rat b)
                           , (λ r _ → seqΣ (expSeq r) (suc n)) is
                             (λ r _ → seqΣ (expSeq r) n)
expSeqUDer a b a<b zero = uDerivativeℙ-const _ _
expSeqUDer a b a<b (suc n) =
  +uDerivativeℙ _ _ _ _ _
   (expSeqUDer a b a<b n) (expSerUDer a b a<b n)


uDerivativeOfℙ-expℝ : ∀ a b → (rat a) <ᵣ (rat b)

  → uDerivativeOfℙ (intervalℙ (rat a) (rat b))
        , (λ x _ → expℝ x) is (λ x _ → expℝ x)
uDerivativeOfℙ-expℝ a b a<b = PT.rec (isPropΠ λ _ → squash₁) (λ x → x) $ do
  z ← IsUCauchyFSequenceExp (rat a) (rat b) a<b
  let f = λ n x _ → seqΣ (expSeq x) n
      zz = uCauchyDer
           (rat a)
           (rat b)
           a<b
           f
            _

           z
           (isUContFSequenceExp a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b))
           (IsUContFSequence-∘+ _ _ 1
             (isUContFSequenceExp a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b)))
           (IsUCauchyFSequence-∘+ _ _ 1 z)
           (expSeqUDer a b a<b)
  return (subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → let ics = _ in
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _

          (PT.map (isCauchySequence-∘+ _ 1) ics))
       ∙ sym (fromCauchySequence'₁-∘+ _ 1 ics _))
    (funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _))
    zz)


cosSer'=-sinSer : ∀ a b → rat a <ᵣ rat b → ∀ n →
   uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
      (λ r _ → flip cosSeries r (suc n)) is
      (λ r _ → -ᵣ (flip sinSeries r n))
cosSer'=-sinSer a b a<b n =
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
    (funExt₂ λ _ _ → cong₂ _·ᵣ_  (-1ⁿ-suc n) refl
      ∙ -ᵣ· _ _ ∙ cong -ᵣ_ (sym (-1ⁿ·≡· n _)))
    (C·uDerivativeℙ _ (rat (-1ⁿ (suc n))) _ _
     (expSerUDer a b a<b (suc (n ℕ.· 2))))



sinSer'=cosSer : ∀ a b → rat a <ᵣ rat b → ∀ n →
 uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → (flip sinSeries x) n)
                             is (λ x _ → (flip cosSeries x) n)
sinSer'=cosSer a b a<b n =
  subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
    (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
    (funExt₂ λ _ _ → sym (-1ⁿ·≡· _ _))
    (C·uDerivativeℙ _ (rat (-1ⁿ n)) _ _
     (expSerUDer a b a<b (n ℕ.· 2)))



sinSeq'=cosSeq : ∀ a b → rat a <ᵣ rat b → ∀ n →
 uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → seqΣ (flip sinSeries x) n)
                      is (λ x _ → seqΣ (flip cosSeries x) n)
sinSeq'=cosSeq a b a<b zero = uDerivativeℙ-const _ _
sinSeq'=cosSeq a b a<b (suc n) =
  +uDerivativeℙ _ _ _ _ _
    (sinSeq'=cosSeq a b a<b n) (sinSer'=cosSer a b a<b n)

cosSeq'=-sinSeq : ∀ a b → rat a <ᵣ rat b → ∀ n →
 uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ x _ → seqΣ (flip cosSeries x) (suc n))
                      is (λ x _ → -ᵣ (seqΣ (flip sinSeries x) n))
cosSeq'=-sinSeq a b a<b zero =
   subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) , (λ _ _ → 0 +ᵣ 1) is_)
    (funExt₂ λ _ _ → sym (-ᵣ-rat 0))
    (uDerivativeℙ-const _ (0 +ᵣ 1))
cosSeq'=-sinSeq a b a<b (suc n) =
   subst (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
     (λ x _ → seqΣ (flip cosSeries x) (suc (suc n))) is_)
    (funExt₂ λ _ _ → sym (-ᵣDistr _ _))
  (+uDerivativeℙ _ _ _ _ _
    (cosSeq'=-sinSeq a b a<b n) (cosSer'=-sinSer a b a<b n))

sin'=cos-uder : ∀ a b → (a<b : rat a <ᵣ rat b) →
      uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,
       (λ x _ → sin x) is (λ x _ → cos x)
sin'=cos-uder a b a<b =
   subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
      ∙ sym (sinImpl _))
    (funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
      ∙ sym (cosImpl _))
    (uCauchyDer (rat a) (rat b) a<b
         (λ z x _ → seqΣ (flip cosSeries x) z)
         (λ z x _ → seqΣ (flip sinSeries x) z)
         uconvcos uccos ucsin uconvsin
        (sinSeq'=cosSeq a b a<b))

    where
    ucsin : IsUContFSequence (intervalℙ (rat a) (rat b)) _
    ucsin = IsUContFSequenceSin a b a<b


    uconvcos : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvcos =
      Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b)

    uconvsin : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvsin =
      Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b)


    uccos : IsUContFSequence (intervalℙ (rat a) (rat b)) _
    uccos = IsUContFSequenceCos a b a<b


cos'=-sin-uder : ∀ a b → (a<b : rat a <ᵣ rat b) →
      uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,
                (λ x _ → cos x)
              is (λ x _ → -ᵣ (sin x))
cos'=-sin-uder a b a<b =
  subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ x x∈ →

        sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _
          uconvcos
          _
          (PT.map (fst ∘ (cauchySequenceFaster
            (seqΣ λ n → cosSeries n x)
            λ n → (suc n) , (ℕ.≤-sucℕ {n})))
           (cos-ch x)))
        ∙
        sym (fromCauchySequence'₁-∘+  _ 1 _ _)
      ∙ sym (cosImpl _)
      )
    (funExt₂ λ x x∈ →
       sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
       ∙
       sym (snd (map-fromCauchySequence'₁
      1 (λ n → seqΣ (flip sinSeries x) n)
       (sin-ch x)
        _ -ᵣ-lip)) ∙ cong -ᵣ_ (sym (sinImpl _)))

    (uCauchyDer (rat a) (rat b) a<b _ _
         (isUCauchyFSequence-ᵣ _ _ uconvsin)
         (λ n →
           subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
              (funExt₂ λ _ _ → ·ᵣComm _ _ ∙ sym (-ᵣ≡[-1·ᵣ] _))
            (IsUContinuousℙC·ᵣ (intervalℙ (rat a) (rat b)) -1
            _ (IsUContFSequenceSin a b a<b n)) )
         (IsUContFSequenceCos a b a<b ∘ suc)
         uconvcos
        (cosSeq'=-sinSeq a b a<b))

    where
    ucsin : IsUContFSequence (intervalℙ (rat a) (rat b)) _
    ucsin = IsUContFSequenceSin a b a<b


    uconvcos : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvcos = map-snd
      (λ X x x∈ m n <n <m →
        X x x∈ (suc m) (suc n) (ℕ.≤-suc <n) (ℕ.≤-suc <m))
      ∘ (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b))

    uconvsin : IsUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    uconvsin =
      Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b)


cos'=-sin-uder' : ∀ a b → (a<b : a <ᵣ b) →
      uDerivativeOfℙ (intervalℙ a b) ,
                (λ x _ → cos x)
              is (λ x _ → -ᵣ (sin x))
cos'=-sin-uder' a b a<b =
  PT.rec2
     (isPropΠ λ _ → squash₁)
     (λ (a' , _ , a'<a) (b' , b<b' , _) →
       uDerivativeOfℙ-restr (intervalℙ (rat a') (rat b'))
         (intervalℙ a b) _ _
         (λ x x∈ → isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a'<a) (fst x∈) ,
                   isTrans≤ᵣ _ _ _ (snd x∈) (<ᵣWeaken≤ᵣ _ _ b<b'))
         (cos'=-sin-uder a' b' (isTrans<ᵣ _ _ _ a'<a
           (isTrans<ᵣ _ _ _ a<b b<b')))

           )
   (denseℚinℝ (a +ᵣ (rat -1)) a (isTrans<≡ᵣ _ _ _

        (<ᵣ-o+ _ _ a (decℚ<ᵣ? { -1 } {0}))
        (+IdR a)))
   (denseℚinℝ b (b +ᵣ 1) (isTrans≡<ᵣ _ _ _
        (sym (+IdR b))
        (<ᵣ-o+ _ _ b (decℚ<ᵣ? {0} {1}))) )

sin'=cos-uder' : ∀ a b → (a<b : a <ᵣ b) →
      uDerivativeOfℙ (intervalℙ (a) (b)) ,
       (λ x _ → sin x) is (λ x _ → cos x)
sin'=cos-uder' a b a<b =
  PT.rec (isPropΠ λ _ → squash₁)
    (λ ((a' , b') , (a'≤a , b≤b')) →
      uDerivativeOfℙ-restr
        (intervalℙ (rat a') (rat b'))
        (intervalℙ a b)
        (λ x _ → sin x)
        (λ r _ → cos r)
       (λ x x∈ →
          (isTrans≤ᵣ _ _ _ a'≤a (fst x∈))
         , (isTrans≤ᵣ _ _ _ (snd x∈) b≤b' ))
       (sin'=cos-uder a' b'
         ((isTrans≤<ᵣ _ _ _ a'≤a
           (isTrans<≤ᵣ _ _ _ a<b b≤b')))))
   (∃enclosingℚInterval a b)

sinSeq≤expSeq : ∀ n x → seqΣ (flip sinSeries x) n ≤ᵣ
                             seqΣ (expSeq (absᵣ x)) (suc (n ℕ.· 2))
sinSeq≤expSeq n x = isTrans≤ᵣ _ _ _
  (sinSeq≤expSeq-1 n x)
  (isTrans≤≡ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _
      (sym (+IdL _))
      (≤ᵣ-+o _ _ _ (decℚ≤ᵣ? {0} {1}) )) --(≤ᵣMonotone+ᵣ _ _ _ _ ? ?)
    (1+expSeq (n ℕ.· 2) (absᵣ x) ))

sin≤exp : ∀ x → sin x ≤ᵣ expℝ (absᵣ x)
sin≤exp x = isTrans≡≤ᵣ _ _ _ (sinImpl _) $
  PT.elim2
    (λ ich ich' →
       isProp≤ᵣ
        (fromCauchySequence'₁ _ ich)
        (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
    (λ ich ich' →
      isTrans≤≡ᵣ _ _ _
        (fromCauchySequence'≤ _ _ _ _
          (flip sinSeq≤expSeq x))
        (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
          (λ n → suc (n ℕ.· 2) ,
           subst (ℕ._≤ suc (n ℕ.· 2)) (·-identityʳ n)
            (ℕ.≤-suc (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
    (sin-ch x)
    (expℝ-cauchySeq (absᵣ x))

cos≤exp : ∀ x → cos x ≤ᵣ expℝ (absᵣ x)
cos≤exp x = isTrans≡≤ᵣ _ _ _ (cosImpl _) $
   PT.elim2
    (λ ich ich' →
       isProp≤ᵣ
        (fromCauchySequence'₁ _ ich)
        (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
    (λ ich ich' →
      isTrans≤≡ᵣ _ _ _
        (fromCauchySequence'≤ _ _ _ _
          (flip cosSeq≤expSeq x))
        (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
          (λ n → (n ℕ.· 2) ,
           subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
            ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
    (cos-ch x)
    (expℝ-cauchySeq (absᵣ x))


-cos≤exp : ∀ x → -ᵣ (cos x) ≤ᵣ expℝ (absᵣ x)
-cos≤exp x =
   isTrans≡≤ᵣ _ _ _
    (cong -ᵣ_ (cosImpl _) ∙ snd (map-fromCauchySequence'₁
      1 _ _
        _ -ᵣ-lip))
    (PT.elim2
    (λ ich ich' →
       isProp≤ᵣ
        (fromCauchySequence'₁ _ ich)
        (fromCauchySequence'₁ (seqΣ (expSeq (absᵣ x))) ich'))
    (λ ich ich' →
      isTrans≤≡ᵣ _ _ _
        (fromCauchySequence'≤ _ _ _ _
          (flip -cosSeq≤expSeq x))
        (sym (snd (cauchySequenceFaster (seqΣ (expSeq (absᵣ x)))
          (λ n → (n ℕ.· 2) ,
           subst (ℕ._≤ (n ℕ.· 2)) (·-identityʳ n)
            ( (ℕ.≤-k· {1} {2} {n} (ℕ.≤-sucℕ {1})))) ich'))))
    (fst (map-fromCauchySequence'₁
      1 _ _
        _ -ᵣ-lip))
    (expℝ-cauchySeq (absᵣ x)))


opaque
 unfolding maxᵣ
 pre-bounded-sin : ∀ a b → rat a <ᵣ rat b →
              Bounded (intervalℙ (rat a) (rat b)) (λ x _ → sin x)
 pre-bounded-sin a b a<b =
   let (bd , ≤bd) = expBounded 0 (ℚ.max (ℚ.abs a) (ℚ.abs b))
                     (≤ᵣ-refl _)
                     (≤ℚ→≤ᵣ _ _
                       (ℚ.isTrans≤ _ _ _ (ℚ.0≤abs a) (ℚ.≤max _ _)))
   in bd , λ x x∈ → isTrans≤ᵣ _ _ _
            (isTrans≤ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _ (abs-max (sin x))
                (max≤-lem _ _ _
                  (sin≤exp x)
                  (subst2 _≤ᵣ_
                    (sym (sin-odd x))
                    (cong expℝ (sym (-absᵣ x)))
                    (sin≤exp (-ᵣ x)))))
              (≤absᵣ _))
           (≤bd (absᵣ x) (0≤absᵣ x ,
             isTrans≤≡ᵣ _ _ _
               (x∈interval-bound _ _ x x∈)
               (cong₂ maxᵣ (absᵣ-rat a) (absᵣ-rat b))))

opaque
 unfolding maxᵣ
 pre-bounded-cos : ∀ a b → rat a <ᵣ rat b →
              Bounded (intervalℙ (rat a) (rat b)) (λ x _ → cos x)
 pre-bounded-cos a b a<b =
   let (bd , ≤bd) = expBounded 0 (ℚ.max (ℚ.abs a) (ℚ.abs b))
                     (≤ᵣ-refl _)
                     (≤ℚ→≤ᵣ _ _
                       (ℚ.isTrans≤ _ _ _ (ℚ.0≤abs a) (ℚ.≤max _ _)))
   in bd , λ x x∈ → isTrans≤ᵣ _ _ _
            (isTrans≤ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _ (abs-max (cos x))
                (max≤-lem _ _ _
                  (cos≤exp x)
                  (-cos≤exp x)))
              (≤absᵣ _))

           (≤bd (absᵣ x) (0≤absᵣ x ,
             isTrans≤≡ᵣ _ _ _
               (x∈interval-bound _ _ x x∈)
               (cong₂ maxᵣ (absᵣ-rat a) (absᵣ-rat b))))

pre-uContSin : ∀ a b → rat a <ᵣ rat b →
  IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x₁ _ → sin x₁)
pre-uContSin a b a<b =
 subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
   ((funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
       ∙ sym (sinImpl _))
      )
   (snd (fromUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (sin-conv a b a<b))
    (IsUContFSequenceSin a b a<b)))


pre-uContCos : ∀ a b → rat a <ᵣ rat b →
  IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x₁ _ → cos x₁)
pre-uContCos a b a<b =
 subst (IsUContinuousℙ (intervalℙ (rat a) (rat b)))
   ((funExt₂ λ _ _ →
      sym (fromCauchySequence'₁≡fromUCauchyFSequence _ _ _ _ _ _ _)
      ∙ sym (cosImpl _)))
   (snd (fromUCauchyFSequence (intervalℙ (rat a) (rat b)) _
    (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ (rat a) (rat b)) _) (cos-conv a b a<b))
    (IsUContFSequenceCos a b a<b)))

isContinuousSin : IsContinuous sin
isContinuousSin = IsUContinuousℙ→IsContinuous _ pre-uContSin

isContinuousCos : IsContinuous cos
isContinuousCos = IsUContinuousℙ→IsContinuous _ pre-uContCos


sin²+cos²=1 : ∀ x → ((sin x) ^ⁿ 2) +ᵣ ((cos x) ^ⁿ 2) ≡ 1
sin²+cos²=1 = ≡Continuous _ _
  (cont₂+ᵣ  _ _
    (IsContinuous∘ _ _ (IsContinuous^ⁿ 2) isContinuousSin)
    (IsContinuous∘ _ _ (IsContinuous^ⁿ 2) isContinuousCos))
   (IsContinuousConst 1)
  ((_∙ sin0²+cos0²≡1) ∘ ℚ.byTrichotomy 0 h)

  where

  h' : ∀ a b → rat a <ᵣ rat b →
    (sin (rat a) ^ⁿ 2) +ᵣ (cos (rat a) ^ⁿ 2)
      ≡ (sin (rat b) ^ⁿ 2) +ᵣ (cos (rat b) ^ⁿ 2)
  h' a b a<b =
    nullDerivative→const (rat a) (rat b)
       (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ a<b)
       (<ᵣWeaken≤ᵣ _ _ a<b , ≤ᵣ-refl _)
      a<b
      _
      h

    where
    h : uDerivativeOfℙ intervalℙ (rat a) (rat b) ,
          (λ x _ → ((sin x) ^ⁿ 2) +ᵣ ((cos x) ^ⁿ 2)) is
        (λ _ _ → rat [ pos 0 / 1+ 0 ])
    h = subst2 (uDerivativeOfℙ intervalℙ (rat a) (rat b) ,_is_)
      (funExt₂ λ _ _ →
        cong₂ _+ᵣ_
          (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
          (cong₂ _·ᵣ_ (sym (·IdL _)) refl))
      (funExt₂ λ _ _ →
        cong₂ _+ᵣ_ (cong₂ _+ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _))
           (cong₂ _+ᵣ_ (-ᵣ· _ _) (-ᵣ· _ _)
             ∙ sym (-ᵣDistr _ _))
          ∙ 𝐑'.+InvR' _ _ refl)
      (+uDerivativeℙ _ _ _ _ _
        h1 h2)

       where
       h1 = (uDerivativeOfℙ· (rat a) (rat b) a<b
          _ _ _ _
          (pre-bounded-sin a b a<b)
          (pre-bounded-sin a b a<b)
          (pre-uContSin a b a<b)
          (pre-bounded-cos a b a<b)
        (sin'=cos-uder a b a<b)
        (sin'=cos-uder a b a<b)
        )
       h2 = (uDerivativeOfℙ· (rat a) (rat b) a<b
          _ _ _ _
          (pre-bounded-cos a b a<b) (pre-bounded-cos a b a<b)
          (pre-uContCos a b a<b)
          (map-snd (λ X x x∈ → isTrans≡≤ᵣ _ _ _
               (sym (-absᵣ _)) (X x x∈)) (pre-bounded-sin a b a<b))
        (cos'=-sin-uder a b a<b) (cos'=-sin-uder a b a<b))

  sin0²+cos0²≡1 : (sin 0 ^ⁿ 2) +ᵣ (cos 0 ^ⁿ 2) ≡ 1
  sin0²+cos0²≡1 = 𝐑'.+IdL' _ _ (cong (_^ⁿ 2) sin0=0 ∙ (0^ⁿ 1))
    ∙ cong (_^ⁿ 2) cos0=1 ∙ 1^ⁿ 2

  h : ℚ.TrichotomyRec 0
       (λ z → (sin (rat z) ^ⁿ 2) +ᵣ (cos (rat z) ^ⁿ 2) ≡
        (sin 0 ^ⁿ 2) +ᵣ (cos 0 ^ⁿ 2))
  h .ℚ.TrichotomyRec.lt-case x x<0 =
    h' x 0 (<ℚ→<ᵣ _ _ x<0)
  h .ℚ.TrichotomyRec.eq-case = refl
  h .ℚ.TrichotomyRec.gt-case x 0<x =
    sym (h' 0 x (<ℚ→<ᵣ _ _ 0<x))


sin·sin+cos·cos=1 : ∀ x → ((sin x) ·ᵣ (sin x)) +ᵣ ((cos x) ·ᵣ (cos x)) ≡ 1
sin·sin+cos·cos=1 x =
 cong₂ _+ᵣ_
   (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
   (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
  ∙ sin²+cos²=1 x

cos·cos=1-sin·sin : ∀ x → ((cos x) ·ᵣ (cos x)) ≡ 1 -ᵣ ((sin x) ·ᵣ (sin x))
cos·cos=1-sin·sin x = sym (𝐑'.plusMinus _ _)
  ∙ cong (_-ᵣ ((sin x) ·ᵣ (sin x))) (+ᵣComm _ _ ∙ sin·sin+cos·cos=1 x)


_₀₊^ⁿ_ : ℝ₀₊ → ℕ → ℝ₀₊
(x , 0≤x) ₀₊^ⁿ n  = (x ^ⁿ n) , 0≤x^ⁿ x n 0≤x


nth-pow-root-iso₀₊ : ℕ₊₁ → Iso ℝ₀₊ ℝ₀₊
nth-pow-root-iso₀₊ n .Iso.fun = _₀₊^ⁿ (ℕ₊₁→ℕ n)
nth-pow-root-iso₀₊ n .Iso.inv = (nth-rootNonNeg n)
nth-pow-root-iso₀₊ n .Iso.rightInv (x , 0≤x) = ww
 where
 opaque
  unfolding maxᵣ minᵣ
  ww : ((nth-rootNonNeg n (x , 0≤x)) ₀₊^ⁿ (ℕ₊₁→ℕ n)) ≡ (x , 0≤x)
  ww =
   ℝ₀₊≡
       (cong ((_^ⁿ (ℕ₊₁→ℕ n)) ∘ fst ∘  (nth-rootNonNeg n))
         (ℝ₀₊≡ (sym (≤→maxᵣ _ _ 0≤x)))
          ∙∙ ≡Continuous
              (λ x →
                ((_^ⁿ (ℕ₊₁→ℕ n)) ∘ fst ∘  (nth-rootNonNeg n))
                 (maxᵣ 0 x , ≤maxᵣ _ _))
              (maxᵣ 0)
             (IsContinuous∘ _ _
               (IsContinuous^ⁿ (ℕ₊₁→ℕ n))
                (IsContinuousWithPred∘IsContinuous
                 (pred≥ 0)
                 (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))

                  (maxᵣ 0)
                   (λ x → ≤maxᵣ 0 x)
                   (IsUContinuousℙ→pointwiseℙ _ _
                     (snd (snd (nth-rootNonNegDef n))))
                   (IsContinuousMaxL 0)))
             (IsContinuousMaxL 0)
            (λ q → byDichotomyMax 0
              {λ r r∈ → (fst (nth-rootNonNeg n (rat r , r∈)) ^ⁿ (ℕ₊₁→ℕ n))
                  ≡ rat r } w q _) x ∙∙
         ≤→maxᵣ _ _ 0≤x)
    where
    w : DichotomyRec 0 λ m ≤m →
         (fst (nth-rootNonNeg n (rat m , ≤m)) ^ⁿ ℕ₊₁→ℕ n) ≡ rat m
    w .DichotomyRec.eq-case =
      cong (_^ⁿ suc (n .ℕ₊₁.n))
       (fst (fst (snd (nth-rootNonNegDef n))))
      ∙ 0^ⁿ (n .ℕ₊₁.n)
    w .DichotomyRec.gt-case m m>0 =
     cong (_^ⁿ suc (n .ℕ₊₁.n))
       ((snd (fst (snd (nth-rootNonNegDef n))) _))
      ∙ cong fst  (nth-pow-root-iso n .Iso.rightInv
        (rat m , m>0))

nth-pow-root-iso₀₊ n .Iso.leftInv (x , 0≤x) = ww
 where
 opaque
  unfolding maxᵣ
  ww : ((nth-rootNonNeg n ((x , 0≤x)  ₀₊^ⁿ (ℕ₊₁→ℕ n)))) ≡ (x , 0≤x)
  ww = (cong ((nth-rootNonNeg n) ∘
      (λ (x , 0≤x) → x ^ⁿ (ℕ₊₁→ℕ n) , 0≤x^ⁿ x (ℕ₊₁→ℕ n) 0≤x ))
        (sym (ℝ₀₊≡ (≤→maxᵣ _ _ 0≤x))) ∙
        ℝ₀₊≡ (≡Continuous
            (λ x →
              (fst (nth-rootNonNeg n
                ((maxᵣ 0 x) ^ⁿ (ℕ₊₁→ℕ n) , 0≤x^ⁿ (maxᵣ 0 x) (ℕ₊₁→ℕ n) (≤maxᵣ _ _))
                 ))
               )
            (maxᵣ 0)
            (IsContinuousWithPred∘IsContinuous (pred≥ 0)
             _ _ _
             (IsUContinuousℙ→pointwiseℙ _ _
                   (snd (snd (nth-rootNonNegDef n))))
             (IsContinuous∘ _ _ (IsContinuous^ⁿ (ℕ₊₁→ℕ n))
              (IsContinuousMaxL 0))
              )
            (IsContinuousMaxL 0)
            (λ q → byDichotomyMax 0
            {λ r r∈ →
               (fst (nth-rootNonNeg n (rat r ^ⁿ (ℕ₊₁→ℕ n) ,
                0≤x^ⁿ (rat r) (ℕ₊₁→ℕ n) r∈)))
                ≡ rat r }
            w q _)
            x
        ∙
        (≤→maxᵣ _ _ 0≤x)))
   where
   w : DichotomyRec {ℓ = ℓ-zero} 0 λ m ≤m →
         fst (nth-rootNonNeg n
           ((rat m ^ⁿ ℕ₊₁→ℕ n) , 0≤x^ⁿ (rat m) (ℕ₊₁→ℕ n) ≤m)) ≡ rat m
   w .DichotomyRec.eq-case =
       cong (fst ∘ nth-rootNonNeg n) (ℝ₀₊≡ (0^ⁿ (n .ℕ₊₁.n)))
     ∙ fst (fst (snd (nth-rootNonNegDef n)))
   w .DichotomyRec.gt-case m m>0 =
      (cong (fst ∘ nth-rootNonNeg n) (ℝ₀₊≡ refl)
    ∙ (snd (fst (snd (nth-rootNonNegDef n))) _))
    ∙ cong fst  (nth-pow-root-iso n .Iso.leftInv
       (rat m , m>0))


nth-pow-root-equiv₀₊ : ℕ₊₁ → ℝ₀₊ ≃ ℝ₀₊
nth-pow-root-equiv₀₊ n = isoToEquiv (nth-pow-root-iso₀₊ n)

1st-rootNonNeg : ∀ x → nth-rootNonNeg 1 x ≡ x
1st-rootNonNeg (x , x≤0) =
  sym (invEq (equivAdjointEquiv (nth-pow-root-equiv₀₊ 1))
     (ℝ₀₊≡ (·IdL _)))
