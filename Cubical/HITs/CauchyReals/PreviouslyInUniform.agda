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
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (seqΣ ; seqΣ' ; _^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using (invℚ ; _⁻¹₊)
open import Cubical.HITs.CauchyReals.RationalsImports
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.NthRoot hiding (invℚ₊ ; _ℚ^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore hiding
  ( IsUContinuousConst
  ; IsUContinuous+ᵣ₂
  ; IsUContinuousC·ᵣ
  ; IsUContinuous-ᵣ₂
  ; clampDistᵣ
  ; IsUContinuousMaxᵣ
  )
open import Cubical.HITs.CauchyReals.Partition using
  ( ℚ<→0<
  ; _ℚ₊·_
  ; riemannSum-
  ; riemannSum-clamp
  ; riemannSum'-absᵣ≤
  ; riemannSum'≤
  ; riemannSum'Const
  ; rtp-1/n
  )
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.FundamentalTheoremOfCalculus
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
  ( expℝ
  ; expSeq'
  ; expSeq'≡expSeq
  ; expSeq'NonNeg
  ; expSeqNonNeg
  ; absᵣ∘expSeq≡expSeq∘absᵣ
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

open IntegrationUC rtp-1/n


-- Basic integral extensionality and uniform-continuity algebra that used to
-- live here have been migrated to Integration, Uniform, and
-- FundamentalTheoremOfCalculus.

{-
Old half-line extension machinery.

This was used here to extend positive-root data to a nonnegative root. It still
contains pre-refactor min/max lifting paths; when reviving it, use `ℚℝ!` or
`minᵣ-rat`/`maxᵣ-rat` directly instead of hand-normalizing rational operations.

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
         refl ∙ Rℝ.minusPlus (fst x) x₀)))) ))
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

  g-hlp-min-max : ∀ δ  δ' x → g-hlp δ δ x ≡ g-hlp δ (min₊ δ' δ) x
  g-hlp-min-max δ δ' x =
   cong (g-hlp δ δ) (sym (Rℝ.minusPlus x x₀))
    ∙∙ ≡Continuous
     (λ x → g-hlp δ δ (x +ᵣ x₀))
     (λ x → g-hlp δ (min₊ δ' δ) (x +ᵣ x₀))
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
   cong (g-hlp δ (min₊ δ' δ)) (Rℝ.minusPlus x x₀)

  g-seq : FSeq (pred≥ x₀)
  g-seq n x _ =
    let δ = fst (x₀lim ([ 1 / 1+ n ]  , tt)) /2₊

    in g-hlp δ δ x

  g-cauchy : IsUCauchyFSequence (pred≥ x₀) g-seq
  g-cauchy ε =
    let (1+ N , 1/N<) = ℚ.lowerBoundℕ⁻¹ (ε /2₊)
    in suc N , λ x x∈ m n <n <m →
        let δ  , Y = x₀lim ([ 1 / 1+ n ]  , tt)
            δ' , Y' = x₀lim ([ 1 / 1+ m ]  , tt)
            zz = _
            zz' = _
            <ε/2 = isTrans<≤ᵣ _ _ _
               (Y _ zz (inl zz)
                ((isTrans≡<ᵣ _ _ _
                 (cong absᵣ ℝ! ∙
                   sym (-absᵣ _) ∙ absᵣPos _ (snd (ℚ₊→ℝ₊ (δ /2₊))))
                 (<ℚ→<ᵣ _ _ (/2₊<id δ))
                 ) )) (≤ℚ→≤ᵣ _ _

                   (ℚ.isTrans≤ [ 1 / 1+ n ] [ 1 / 1+ N ] (fst ε ℚ.· [ 1 / 2 ])
                    ((ℚ.invℚ₊≤invℚ₊ ([ pos (suc n) / 1 ] , _) ([ pos (suc N) / 1 ] , _)
                      (≤ℤ→≤ℚ _ _ (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _) (ℕ.≤-suc (ℕ.<-weaken <n))))))
                       (ℚ.<Weaken≤ [ 1 / 1+ N ] _ 1/N<))
                       )
            <ε/2' = isTrans<≤ᵣ _ _ _
               (Y' _ zz' (inl zz')
                (isTrans≡<ᵣ _ _ _
                 (cong absᵣ ℝ! ∙
                   sym (-absᵣ _) ∙ absᵣPos _ (snd (ℚ₊→ℝ₊ (δ' /2₊))))
                 (<ℚ→<ᵣ _ _ (/2₊<id δ'))
                 )) ((≤ℚ→≤ᵣ _ _

                   (ℚ.isTrans≤ [ 1 / 1+ m ] [ 1 / 1+ N ] (fst ε ℚ.· [ 1 / 2 ])
                    ((ℚ.invℚ₊≤invℚ₊ ([ pos (suc m) / 1 ] , _) ([ pos (suc N) / 1 ] , _)
                      (≤ℤ→≤ℚ _ _ (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _) (ℕ.≤-suc (ℕ.<-weaken <m))))))
                       (ℚ.<Weaken≤ [ 1 / 1+ N ] _ 1/N<))
                       ))
        in isTrans≡<ᵣ _ _ _
          (cong absᵣ (cong₂ _-ᵣ_
            (g-hlp-min-max (δ /2₊) (δ' /2₊) x)
            (g-hlp-min-max (δ' /2₊) (δ /2₊) x ∙
              cong (flip (g-hlp (δ' /2₊)) x) (ℚ₊≡
               {min₊ _ _}
               {min₊ (δ' /2₊) (δ /2₊)}
               (ℚ.minComm (fst (δ /2₊)) (fst (δ' /2₊)))))))
          (isTrans≤<ᵣ _ _ _
            (isTrans≤ᵣ _ _ _ (maxᵣ-dist _ _ _)
              (absᵣ-triangle-midpt _ y₀ _))
            ((isTrans<≡ᵣ _ _ _ (<ᵣMonotone+ᵣ _ _ _ _
                (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) <ε/2)
                (<ε/2'))
             (+ᵣ-rat _ _ ∙ cong rat (ℚε/2+ε/2≡ε (fst ε))))))

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
               let zz = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
                           (<ᵣ-o+ _ _ _
                            (snd (ℚ₊→ℝ₊
                              (fst (x₀lim ([ pos 1 / 1+ n ] , tt)) /2₊))))
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
                      (cong absᵣ ℝ! ∙
                       sym (-absᵣ _) ∙
                        absᵣPos _ (snd
                         (ℚ₊→ℝ₊ (fst (x₀lim ([ pos 1 / 1+ n ] , tt)) /2₊)))))
                      (<ℚ→<ᵣ _ _ (/2₊<id (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))
                  (<ℚ→<ᵣ _ _ (ℚ.isTrans< [ 1 / 1+ n ] [ 1 / 1+ N ] _
                    (fst (ℚ.invℚ₊-<-invℚ₊ (fromNat (suc N)) (fromNat (suc n)))
                     (<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
                      (ℕ.≤-suc SN<n)))) 1/N<))) ∣₁
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
                   (δ , ℚ<→0< _ (<ᵣ→<ℚ _ _ 0<δ ))

             in ∣ suc N , (λ n <n →
              let zzz = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
                           (<ᵣ-o+ _ _ _
                            (snd (ℚ₊→ℝ₊
                              (fst (x₀lim ([ pos 1 / 1+ n ] , tt)) /2₊))))
                  zz :
                      (x₀ +ᵣ rat (fst (fst (x₀lim ([ 1 / 1+ n ] , tt)) /2₊)))
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
                          (cong absᵣ ℝ! ∙
                           sym (-absᵣ _) ∙
                            absᵣPos _ (snd
                             (ℚ₊→ℝ₊ (fst (x₀lim ([ pos 1 / 1+ n ] , tt)) /2₊)))))
                          (<ℚ→<ᵣ _ _ (/2₊<id (fst (x₀lim ([ pos 1 / 1+ n ] , tt)))))))
                      (<ℚ→<ᵣ _ _ (ℚ.isTrans< [ 1 / 1+ n ] [ 1 / 1+ N ] _
                        (fst (ℚ.invℚ₊-<-invℚ₊ (fromNat (suc N)) (fromNat (suc n)))
                         (<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
                          (ℕ.≤-suc <n)))) 1/N<)))))
                          (a<b-c⇒a+c<b _ _ _ δ<fx-y₀)))
              in isTrans≡<ᵣ _ _ _
                  (cong absᵣ (Rℝ.+InvR' _ _
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
     (sym (Rℝ.+IdL' _ x₀ (maxᵣComm 0 (rat m) ∙
          ≤→maxᵣ (rat m) 0 (<ᵣWeaken≤ᵣ (rat m) 0 (<ℚ→<ᵣ m 0 m<0))))))  )

   w .ℚ.TrichotomyRec.eq-case _ = ≡ᵣWeaken≤ᵣ _ _
     (sym g[x₀]=y₀ ∙
      cong (uncurry (fst g)) (Σ≡Prop (isProp≤ᵣ _)
      (sym (Rℝ.+IdL' _ _ refl))))
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
    (λ ε → (ℚ._ℚ₊^ⁿ_ ε (suc n')) ,
      λ r r∈ x＃r x →
        isTrans<≡ᵣ _ _ _
         (isTrans≡<ᵣ _ _ _
           ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ (snd (root (1+ n .ℕ₊₁.n) (r , r∈))))
           (ₙ√-StrictMonotone n (subst2 _<ᵣ_
            ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ r∈)
            (sym (cong fst (^ℤ-rat _ (pos (suc n')))))
            x)))
           (cong fst (Iso.ret (nth-pow-root-iso n)
            (ℚ₊→ℝ₊ ε))) )
    (uContRoot n) λ _ _ → ₙ√-Monotone n


nth-rootNonNeg : ℕ₊₁ → Σ ℝ (_≤ᵣ_ 0) → Σ ℝ (_≤ᵣ_ 0)
nth-rootNonNeg n = fst (nth-rootNonNegDef n)

nth-rootNonNeg0 : ∀ n (p : 0 ≤ᵣ 0) → 0 ≡ fst (nth-rootNonNeg n (0 , p))
nth-rootNonNeg0 n p = sym (fst (fst (snd (nth-rootNonNegDef n))))
  ∙ cong (λ p → fst (nth-rootNonNeg n (0 , p)))
   (isProp≤ᵣ 0 0 _ _)
-}

-- Interval boundedness and boundedness closure lemmas have been migrated to
-- Uniform.

IsUCauchyFSequenceExp : ∀ a b → a <ᵣ b →
               ∥ (IsUCauchyFSequence (intervalℙ a b)
                      λ n x _ → seqΣ (expSeq x) n) ∥₁
IsUCauchyFSequenceExp a b a<b =
 PT.map (Iso.fun (IsoIsUConvSeries'IsCauchy'SequenceSum
         (intervalℙ a b) (λ n x _ → expSeq x n))) (uConvExpSer a b a<b )


{-
Moved to Cubical.HITs.CauchyReals.FundamentalTheoremOfCalculus.

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
        (((ε /2₊) /2₊) ℚ₊· ℚ._⁻¹₊ η₊)
      NF , XF = IsUCauchyFSequence-lim (intervalℙ a b) _
                 iucF uF ((ε /2₊) /2₊)
      Nf⊔NF = ℕ.max Nf NF
  (δ , Xδ) ← fₙ≡∫Fₙ (suc Nf⊔NF) x x∈ (ε /2₊)
  return
    (δ , λ tp msh≤ →
          fst (∼≃abs<ε _ _ ε)
              (subst∼ (ℚ.+Comm _ _ ∙  (ℚ.+Assoc _ _ _)
                ∙ cong₂ ℚ._+_ (ℚε/2+ε/2≡ε (fst (ε /2₊))) refl
                 ∙ ℚε/2+ε/2≡ε (fst ε))
                (triangle∼
                  (triangle∼ {ε = ((ε /2₊) /2₊)}
                     (sym∼ _ _ _ $ invEq (∼≃abs<ε _ _ ((ε /2₊) /2₊))
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
                                 (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ ((ε /2₊) /2₊))
                                  (isTrans≡<ᵣ _ _ _
                                    (cong₂ _·ᵣ_ refl (sym (invℝ₊-rat η₊)))
                                    (invEq (z/y<x₊≃z<y₊·x _ _ _)
                                     (isTrans<≡ᵣ _ _ _
                                       (isTrans≤<ᵣ _ _ _
                                         (≤ᵣ-+o _ _ (-ᵣ a) (snd x∈)) b-a<η₊)
                                       (sym (·IdR _))))))
                                 (·IdR _))))))
                    (invEq (∼≃abs<ε _ _ (ε /2₊)) (Xδ tp msh≤)))
                  (invEq (∼≃abs<ε _ _ ((ε /2₊) /2₊)) (XF x x∈ (suc Nf⊔NF)
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
       let zz = FTOC⇐ x b (<ᵣWeaken≤ᵣ _ _ x<b)
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
                        (FTOC⇐ a b (<ᵣWeaken≤ᵣ _ _ a<b) _ _ ucf fd)
       in subst (on[ a , x ]IntegralOf
              (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is_)
               (sym (Rℝ.plusMinus _ _)
                ∙∙ cong₂ _-ᵣ_ zzz
                   (cong₂ _-ᵣ_
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl)))
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl))))
                ∙∙ [x-y]-[x-z]≡z-y _ _ _)
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
        (FTOC⇐ a x (<ᵣWeaken≤ᵣ _ _ a<x)
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
-}

{-
Old nonnegative-root iso tail, depending on the archived `nth-rootNonNeg`
construction above. This should move to the checked nth-root development when
the nonnegative extension is revived.

_₀₊^ⁿ_ : ℝ₀₊ → ℕ → ℝ₀₊
(x , 0≤x) ₀₊^ⁿ n  = (x ^ⁿ n) , 0≤x^ⁿ x n 0≤x


nth-pow-root-iso₀₊ : ℕ₊₁ → Iso ℝ₀₊ ℝ₀₊
nth-pow-root-iso₀₊ n .Iso.fun = _₀₊^ⁿ (ℕ₊₁→ℕ n)
nth-pow-root-iso₀₊ n .Iso.inv = (nth-rootNonNeg n)
nth-pow-root-iso₀₊ n .Iso.sec (x , 0≤x) = ww
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
      ∙ cong fst  (nth-pow-root-iso n .Iso.sec
        (rat m , m>0))

nth-pow-root-iso₀₊ n .Iso.ret (x , 0≤x) = ww
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
    ∙ cong fst  (nth-pow-root-iso n .Iso.ret
       (rat m , m>0))


nth-pow-root-equiv₀₊ : ℕ₊₁ → ℝ₀₊ ≃ ℝ₀₊
nth-pow-root-equiv₀₊ n = isoToEquiv (nth-pow-root-iso₀₊ n)

1st-rootNonNeg : ∀ x → nth-rootNonNeg 1 x ≡ x
1st-rootNonNeg (x , x≤0) =
  sym (invEq (equivAdjointEquiv (nth-pow-root-equiv₀₊ 1))
     (ℝ₀₊≡ (·IdL _)))
-}
