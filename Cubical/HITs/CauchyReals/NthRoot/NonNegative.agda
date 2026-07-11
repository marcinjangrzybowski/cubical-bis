module Cubical.HITs.CauchyReals.NthRoot.NonNegative where


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
open import Cubical.Data.Int.Fast as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
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
open import Cubical.HITs.CauchyReals.Partition using (ℚ<→0<)
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.Uniform using
  ( IsUContinuousℙ-ᵣ∘
  ; IsUContinuousℙ→pointwise
  ; IsUContinuousℙ→pointwiseℙ
  ; IsUContinuousMaxᵣ
  ; IsUCauchyFSequence
  ; IsUContFSequence
  ; FSeq
  ; fromUCauchyFSequence
  ; isCauchyFSequenceAt
  ; fromCauchySequence'₁≡fromUCauchyFSequence
  ; fromCauchySequence'-at≡fromUCauchyFSequence
  ; maxᵣ-dist
  ; DichotomyRec
  ; byDichotomyMax
  )

opaque
 unfolding maxᵣ minᵣ
 extendℝFnLeft : ∀ (x₀ y₀ : ℝ) →
         (f : (Σ ℝ (x₀ <ᵣ_)) → (Σ ℝ (y₀ <ᵣ_)))
       → at x₀ limitOfℙ pred> x₀ , (λ x x₀<x _ → fst (f (x , x₀<x )) ) is' y₀

       → IsUContinuousℙ (pred> x₀) (curry (fst ∘ f))
       → (∀ x y → fst x ≤ᵣ fst y → fst (f x) ≤ᵣ fst (f y))
      → Σ[ f' ∈ ((Σ ℝ (x₀ ≤ᵣ_)) → (Σ ℝ (y₀ ≤ᵣ_))) ]
          (((fst (f' (x₀ , ≤ᵣ-refl x₀)) ≡ y₀) ×
            (∀ x → fst (f' (x .fst , (<ᵣWeaken≤ᵣ x₀ (x .fst) (snd x)))) ≡ fst (f x)  ))
              × IsUContinuousℙ (pred≥ x₀) (curry (fst ∘ f')))
 extendℝFnLeft x₀ y₀ f x₀lim ucf f-mon  =
   (λ x →
     let pr : y₀ ≤ᵣ fst g (fst x) (snd x)
         pr =
           isTrans≤≡ᵣ _ _ _
             (≤Cont
               {f₁ = λ x → (fst g) ((maxᵣ 0 x) +ᵣ x₀)
                 (isTrans≡≤ᵣ _ _ _ (sym (+IdL _))
                  (≤ᵣ-+o _ _ _ (≤maxᵣ 0 x))) }
               (IsContinuousConst y₀)
               (IsContinuousWithPred∘IsContinuous
                 (pred≥ x₀)
                 (fst g)
                 (λ u → maxᵣ 0 u +ᵣ x₀)
                 (λ u → isTrans≡≤ᵣ x₀ (0 +ᵣ x₀) (maxᵣ 0 u +ᵣ x₀)
                   (sym (+IdL x₀))
                   (≤ᵣ-+o 0 (maxᵣ 0 u) x₀ (≤maxᵣ 0 u)))
                 (IsUContinuousℙ→pointwise (pred≥ x₀) (fst g) (snd g))
                 (IsContinuous∘ (_+ᵣ x₀) (maxᵣ 0)
                   (IsContinuous+ᵣR x₀) (IsContinuousMaxL 0)))
               (λ u → y₀≤g u
                 (isTrans≡≤ᵣ x₀ (0 +ᵣ x₀) (maxᵣ 0 (rat u) +ᵣ x₀)
                   (λ i → +IdL x₀ (~ i))
                   (≤ᵣ-+o 0 (maxᵣ 0 (rat u)) x₀ (≤maxᵣ 0 (rat u)))))
               (fst x -ᵣ x₀))
             (cong (uncurry (fst g))
              (Σ≡Prop (λ z → isProp≤ᵣ x₀ z)
               (cong₂ _+ᵣ_
                 (≤→maxᵣ 0 (fst x -ᵣ x₀) (x≤y→0≤y-x x₀ (fst x) (snd x)))
                 refl
                ∙ Rℝ.minusPlus (fst x) x₀)))
     in fst g (fst x) (snd x) , pr)
    , (g[x₀]=y₀ , λ x → g[x₀<x]=f x (<ᵣWeaken≤ᵣ x₀ (x .fst) (snd x))) ,
     snd g
  where

  f-mon-inv : ∀ x y → fst (f x) <ᵣ fst (f y) → fst x ≤ᵣ fst y
  f-mon-inv x y fx<fy = ≯ᵣ→≤ᵣ _ _
   λ y<x → ≤ᵣ→≯ᵣ _ _ (f-mon y x (<ᵣWeaken≤ᵣ _ _ y<x)) fx<fy

  g-hlp : ℚ₊ → ℚ₊ → ℝ → ℝ
  g-hlp δ δ' x =
    let z : x₀ <ᵣ x₀ +ᵣ rat (fst δ)
        z = isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ)))
        z' : x₀ <ᵣ x₀ +ᵣ rat (fst δ')
        z' = isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ')))
    in maxᵣ (fst (f (x₀ +ᵣ rat (fst δ) , z)))
         (fst (f ((maxᵣ (x₀ +ᵣ rat (fst δ'))
           x) , isTrans<≤ᵣ x₀ (x₀ +ᵣ rat (fst δ')) (maxᵣ (x₀ +ᵣ rat (fst δ')) x)
             z' (≤maxᵣ (x₀ +ᵣ rat (fst δ')) x) )))

  g-hlpCont : ∀ δ δ' → IsContinuous (g-hlp δ δ')
  g-hlpCont δ δ' =
    let z : x₀ <ᵣ x₀ +ᵣ rat (fst δ)
        z = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
          (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ)))
        z' : x₀ <ᵣ x₀ +ᵣ rat (fst δ')
        z' = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
          (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ')))
    in IsContinuous∘
      (maxᵣ (fst (f (x₀ +ᵣ rat (fst δ) , z))))
      (λ x → fst (f (maxᵣ (x₀ +ᵣ rat (fst δ')) x ,
        isTrans<≤ᵣ _ _ _ z' (≤maxᵣ (x₀ +ᵣ rat (fst δ')) x))))
      (IsContinuousMaxL (fst (f (x₀ +ᵣ rat (fst δ) , z))))
      (IsContinuousWithPred∘IsContinuous
        (pred> x₀)
        (curry (fst ∘ f))
        (maxᵣ (x₀ +ᵣ rat (fst δ')))
        (λ x → isTrans<≤ᵣ x₀ (x₀ +ᵣ rat (fst δ'))
          (maxᵣ (x₀ +ᵣ rat (fst δ')) x) z'
          (≤maxᵣ (x₀ +ᵣ rat (fst δ')) x))
        (IsUContinuousℙ→pointwise (pred> x₀) (curry (fst ∘ f)) ucf)
        (IsContinuousMaxL (x₀ +ᵣ rat (fst δ'))))

  g-hlp-min-max : ∀ δ  δ' x → g-hlp δ δ x ≡ g-hlp δ (min₊ δ' δ) x
  g-hlp-min-max δ δ' x =
   cong (g-hlp δ δ) (sym (Rℝ.minusPlus x x₀))
    ∙∙ ≡Continuous
     (λ x → g-hlp δ δ (x +ᵣ x₀))
     (λ x → g-hlp δ (min₊ δ' δ) (x +ᵣ x₀))
    (IsContinuous∘ (g-hlp δ δ) (_+ᵣ x₀) (g-hlpCont δ δ)
      (IsContinuous+ᵣR x₀))
    ((IsContinuous∘ (g-hlp δ (min₊ δ' δ)) (_+ᵣ x₀)
      (g-hlpCont δ (min₊ δ' δ))
      (IsContinuous+ᵣR x₀)))
    (λ q → ⊎.rec
        (λ q≤δ →
         let ineq = (Σ≡Prop (λ z → isProp<ᵣ x₀ z)
              (maxᵣComm _ _ ∙ ≤→maxᵣ _ _ (isTrans≡≤ᵣ _ _ _ (+ᵣComm _ _)
               (≤ᵣ-o+ _ _ _ (≤ℚ→≤ᵣ _ _ q≤δ)))))
         in (maxᵣComm _ _ ∙ ≤→maxᵣ _ _
          (≡ᵣWeaken≤ᵣ _ _ (cong (fst ∘ f) ineq)))
          ∙
           sym (maxᵣComm _ _ ∙ ≤→maxᵣ _ _
            (f-mon _ _
              (max≤-lem _ _ _
               (≤ᵣ-o+ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ') (fst δ))))
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
                   (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ') (fst δ))) (≤ℚ→≤ᵣ _ _ δ≤q)))))))
          in ≤→maxᵣ _ _ (f-mon _ _ (isTrans≤≡ᵣ _ _ _ ineq
                (sym zz))) ∙∙ cong (fst ∘ f)
                  (Σ≡Prop (λ z → isProp<ᵣ x₀ z)
                  zz) ∙∙
             sym (≤→maxᵣ _  _
                (f-mon _ _ ineq)))
     (ℚ.≤cases q (fst δ)))
       (x -ᵣ x₀)
   ∙∙
   cong (g-hlp δ (min₊ δ' δ)) (Rℝ.minusPlus x x₀)

  invSuc₊ : ℕ → ℚ₊
  invSuc₊ n = [ pos 1 / 1+ n ] , ℚ.0<pos 0 (1+ n)

  invSuc≤inv₊ : ∀ N₊ n → ℕ₊₁→ℕ N₊ ℕ.< n → [ 1 / 1+ n ] ℚ.≤ [ 1 , N₊ ]
  invSuc≤inv₊ (1+ N) n N<n =
    ℚ.invℚ₊≤invℚ₊
      ([ pos (suc n) / 1 ] , ℚ.0<pos n 1)
      ([ pos (suc N) / 1 ] , ℚ.0<pos N 1)
      (≤ℤ→≤ℚ (pos (suc N)) (pos (suc n))
        (ℤ.ℕ≤→pos-≤-pos (suc N) (suc n) (ℕ.≤-suc (ℕ.<-weaken N<n))))

  g-seq : FSeq (pred≥ x₀)
  g-seq n x _ =
    let δ : ℚ₊
        δ = fst (x₀lim (invSuc₊ n)) /2₊

    in g-hlp δ δ x

  g-cauchy : IsUCauchyFSequence (pred≥ x₀) g-seq
  g-cauchy ε =
    let N₊ , 1/N< = ℚ.lowerBoundℕ⁻¹ (ε /2₊)
        N = ℕ₊₁→ℕ N₊
    in N , λ x x∈ m n <n <m →
        let δ  , Y = x₀lim (invSuc₊ n)
            δ' , Y' = x₀lim (invSuc₊ m)
            zz : x₀ <ᵣ x₀ +ᵣ rat (fst (δ /2₊))
            zz = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
              (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ (δ /2₊))))
            zz' : x₀ <ᵣ x₀ +ᵣ rat (fst (δ' /2₊))
            zz' = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
              (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ (δ' /2₊))))
            <ε/2 = isTrans<≤ᵣ _ _ _
               (Y _ zz (inl zz)
                ((isTrans≡<ᵣ _ _ _
                 (cong absᵣ ℝ! ∙
                   sym (-absᵣ _) ∙ absᵣPos _ (snd (ℚ₊→ℝ₊ (δ /2₊))))
                 (<ℚ→<ᵣ _ _ (/2₊<id δ))
                 ) )) (≤ℚ→≤ᵣ _ _

                   (ℚ.isTrans≤ [ 1 / 1+ n ] [ 1 , N₊ ] (fst ε ℚ.· [ 1 / 2 ])
                    (invSuc≤inv₊ N₊ n <n)
                    (ℚ.<Weaken≤ [ 1 , N₊ ] _ 1/N<))
                       )
            <ε/2' = isTrans<≤ᵣ _ _ _
               (Y' _ zz' (inl zz')
                (isTrans≡<ᵣ _ _ _
                 (cong absᵣ ℝ! ∙
                   sym (-absᵣ _) ∙ absᵣPos _ (snd (ℚ₊→ℝ₊ (δ' /2₊))))
                 (<ℚ→<ᵣ _ _ (/2₊<id δ'))
                 )) ((≤ℚ→≤ᵣ _ _

                   (ℚ.isTrans≤ [ 1 / 1+ m ] [ 1 , N₊ ] (fst ε ℚ.· [ 1 / 2 ])
                    (invSuc≤inv₊ N₊ m <m)
                    (ℚ.<Weaken≤ [ 1 , N₊ ] _ 1/N<))
                       ))
        in isTrans≡<ᵣ _ _ _
          (cong absᵣ (cong₂ _-ᵣ_
            (g-hlp-min-max (δ /2₊) (δ' /2₊) x)
            (g-hlp-min-max (δ' /2₊) (δ /2₊) x ∙
              cong (flip (g-hlp (δ' /2₊)) x) (ℚ₊≡
                {min₊ (δ /2₊) (δ' /2₊)}
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
  g-cs n =
    let δ : ℚ₊
        δ = fst (x₀lim (invSuc₊ n)) /2₊
        z : x₀ <ᵣ x₀ +ᵣ rat (fst δ)
        z = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
          (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ)))
    in IsUContinuous∘ℙ
      (pred≥ x₀)
      (IsUContinuousMaxᵣ (fst (f (x₀ +ᵣ rat (fst δ) , z))))
      (IsUContinuousℙ∘ℙ
        (pred≥ x₀)
        (pred> x₀)
        (λ x x∈ → isTrans<≤ᵣ x₀ (x₀ +ᵣ rat (fst δ))
          (maxᵣ (x₀ +ᵣ rat (fst δ)) x) z
          (≤maxᵣ (x₀ +ᵣ rat (fst δ)) x))
        ucf
        (restrIsUContinuousℙ
          (pred≥ x₀)
          (maxᵣ (x₀ +ᵣ rat (fst δ)))
          (IsUContinuousMaxᵣ (x₀ +ᵣ rat (fst δ)))))

  g : Σ-syntax ((x : ℝ) → x ∈ pred≥ x₀ → ℝ) (IsUContinuousℙ (pred≥ x₀))
  g = fromUCauchyFSequence (pred≥ x₀) g-seq g-cauchy g-cs

  g[x₀]=y₀ : fst g x₀ (≤ᵣ-refl x₀) ≡ y₀
  g[x₀]=y₀ = sym
   (fromCauchySequence'₁≡fromUCauchyFSequence
     (pred≥ x₀) g-seq x₀ (≤ᵣ-refl x₀) g-cauchy g-cs ∣ w ∣₁)
     ∙ fromCauchySequence'≡ (λ n → g-seq n x₀ (≤ᵣ-refl x₀))
       w y₀
       g[x₀]=y₀-limit
   where
    w : IsCauchySequence' (flip (flip g-seq x₀) (≤ᵣ-refl x₀))
    w = isCauchyFSequenceAt (pred≥ x₀) g-seq g-cauchy x₀ (≤ᵣ-refl x₀)

    g[x₀]=y₀-limit : (ε : ℚ₊) →
      ∃[ N ∈ ℕ ] (∀ n → N ℕ.< n →
        absᵣ (g-seq n x₀ (≤ᵣ-refl x₀) -ᵣ y₀) <ᵣ rat (fst ε))
    g[x₀]=y₀-limit ε =
      let N₊ , 1/N< = ℚ.lowerBoundℕ⁻¹ ε
          N = ℕ₊₁→ℕ N₊
      in ∣ N ,
        (λ n SN<n →
          let δ = fst (x₀lim (invSuc₊ n))
              δ/2 : ℚ₊
              δ/2 = δ /2₊
              zz = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
                    (<ᵣ-o+ _ _ _
                     (snd (ℚ₊→ℝ₊ δ/2)))
              n<Nε : [ 1 / 1+ n ] ℚ.< fst ε
              n<Nε =
                ℚ.isTrans≤< [ 1 / 1+ n ] [ 1 , N₊ ] (fst ε)
                  (invSuc≤inv₊ N₊ n SN<n) 1/N<
              ∣x₀-[x₀+δ/2]∣<δ :
                absᵣ (x₀ -ᵣ (x₀ +ᵣ rat (fst δ/2))) <ᵣ rat (fst δ)
              ∣x₀-[x₀+δ/2]∣<δ =
                isTrans≡<ᵣ _ _ _
                  (cong absᵣ ℝ! ∙
                   sym (-absᵣ _) ∙
                   absᵣPos _ (snd (ℚ₊→ℝ₊ δ/2)))
                  (<ℚ→<ᵣ _ _ (/2₊<id δ))
              ∣y₀-f[x₀+δ/2]∣<1/n :
                absᵣ (y₀ -ᵣ fst (f (x₀ +ᵣ rat (fst δ/2) , zz)))
                <ᵣ rat (fst (invSuc₊ n))
              ∣y₀-f[x₀+δ/2]∣<1/n =
                snd (x₀lim (invSuc₊ n))
                  _ _ (inl zz) ∣x₀-[x₀+δ/2]∣<δ
          in isTrans≡<ᵣ _ _ _
             (minusComm-absᵣ _ _ ∙
               cong (absᵣ ∘ (_-ᵣ_ y₀))
                (cong (maxᵣ (fst (f (x₀ +ᵣ rat (fst δ/2) , zz)))) (cong (fst ∘ f)
                 (Σ≡Prop (λ z → isProp<ᵣ x₀ z)
                  (maxᵣComm _ _ ∙ ≤→maxᵣ _ _
                    (<ᵣWeaken≤ᵣ _ _ zz)))) ∙
                  maxᵣIdem (fst (f (x₀ +ᵣ rat (fst δ/2) , zz)))))
             (isTrans<ᵣ _ _ _
             ∣y₀-f[x₀+δ/2]∣<1/n
             (<ℚ→<ᵣ _ _ n<Nε))) ∣₁


  g[x₀<x]=f : ∀ (x : Σ ℝ (x₀ <ᵣ_)) (p : x .fst ∈ pred≥ x₀)  →
                fst g (x .fst) p ≡ fst (f x)
  g[x₀<x]=f (x , x₀<x) p = (sym
   (fromCauchySequence'-at≡fromUCauchyFSequence
     (pred≥ x₀) g-seq x p g-cauchy g-cs)
     ∙ fromCauchySequence'≡ (λ n → g-seq n x p)
       (isCauchyFSequenceAt (pred≥ x₀) g-seq g-cauchy x p)
       (fst (f (x , x₀<x)))
       (λ ε → PT.rec
          squash₁
          (λ (δ , 0<δ , δ<fx-y₀) →
            g[x₀<x]=f-limit ε δ 0<δ δ<fx-y₀)
          (denseℚinℝ _ _ (x<y→0<y-x _ _ (snd (f (x , x₀<x)))))))
   where
    g[x₀<x]=f-limit :
      (ε : ℚ₊) (δ : ℚ) → 0 <ᵣ rat δ → rat δ <ᵣ fst (f (x , x₀<x)) -ᵣ y₀ →
      ∃[ N ∈ ℕ ] (∀ n → N ℕ.< n →
        absᵣ (g-seq n x (<ᵣWeaken≤ᵣ x₀ x x₀<x) -ᵣ fst (f (x , x₀<x))) <ᵣ rat (fst ε))
    g[x₀<x]=f-limit ε δ 0<δ δ<fx-y₀ =
      let N₊ , 1/N< = ℚ.lowerBoundℕ⁻¹ (δ , ℚ<→0< δ (<ᵣ→<ℚ 0 δ 0<δ))
          N = ℕ₊₁→ℕ N₊
      in ∣ N , (λ n <n →
        let δ₀ = fst (x₀lim (invSuc₊ n))
            δ₀/2 : ℚ₊
            δ₀/2 = δ₀ /2₊
            zzz = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
                    (<ᵣ-o+ _ _ _
                     (snd (ℚ₊→ℝ₊ δ₀/2)))
            n<Nδ : [ 1 / 1+ n ] ℚ.< δ
            n<Nδ =
              ℚ.isTrans≤< [ 1 / 1+ n ] [ 1 , N₊ ] δ
                (invSuc≤inv₊ N₊ n <n) 1/N<
            ∣x₀-[x₀+δ₀/2]∣<δ₀ :
              absᵣ (x₀ -ᵣ (x₀ +ᵣ rat (fst δ₀/2))) <ᵣ rat (fst δ₀)
            ∣x₀-[x₀+δ₀/2]∣<δ₀ =
              isTrans≡<ᵣ _ _ _
                (cong absᵣ ℝ! ∙
                 sym (-absᵣ _) ∙
                 absᵣPos _ (snd (ℚ₊→ℝ₊ δ₀/2)))
                (<ℚ→<ᵣ _ _ (/2₊<id δ₀))
            ∣y₀-f[x₀+δ₀/2]∣<1/n :
              absᵣ (y₀ -ᵣ fst (f (x₀ +ᵣ rat (fst δ₀/2) , zzz)))
              <ᵣ rat (fst (invSuc₊ n))
            ∣y₀-f[x₀+δ₀/2]∣<1/n =
              snd (x₀lim (invSuc₊ n))
                _ _ (inl zzz) ∣x₀-[x₀+δ₀/2]∣<δ₀
            f[x₀+δ₀/2]-y₀<δ :
              fst (f (x₀ +ᵣ rat (fst δ₀/2) , zzz)) -ᵣ y₀
              <ᵣ rat δ
            f[x₀+δ₀/2]-y₀<δ =
              isTrans≤<ᵣ _ _ _
                (isTrans≤≡ᵣ _ _ _ (≤absᵣ _) (minusComm-absᵣ _ _))
                (isTrans<ᵣ _ _ _
                  ∣y₀-f[x₀+δ₀/2]∣<1/n
                  (<ℚ→<ᵣ _ _ n<Nδ))
            f[x₀+δ₀/2]<f[x] :
              fst (f (x₀ +ᵣ rat (fst δ₀/2) , zzz))
              <ᵣ fst (f (x , x₀<x))
            f[x₀+δ₀/2]<f[x] =
              isTrans<ᵣ _ _ _
                (a-b<c⇒a<c+b _ _ _ f[x₀+δ₀/2]-y₀<δ)
                (a<b-c⇒a+c<b _ _ _ δ<fx-y₀)
            zz :
                (x₀ +ᵣ rat (fst δ₀/2))
                  ≤ᵣ x
            zz = f-mon-inv (x₀ +ᵣ rat (fst δ₀/2) , zzz) (x , x₀<x) f[x₀+δ₀/2]<f[x]
            xδ : ℝ
            xδ = x₀ +ᵣ rat (fst δ₀/2)
            max-xδ-x∈ : x₀ <ᵣ maxᵣ xδ x
            max-xδ-x∈ = isTrans<≤ᵣ x₀ xδ (maxᵣ xδ x) zzz (≤maxᵣ xδ x)
            f[xδ]≤f[max-xδ-x] :
              fst (f (xδ , zzz)) ≤ᵣ fst (f (maxᵣ xδ x , max-xδ-x∈))
            f[xδ]≤f[max-xδ-x] =
              f-mon (xδ , zzz) (maxᵣ xδ x , max-xδ-x∈) (≤maxᵣ xδ x)
        in isTrans≡<ᵣ _ _ _
            (cong absᵣ (Rℝ.+InvR' _ _
              (≤→maxᵣ (fst (f (xδ , zzz))) (fst (f (maxᵣ xδ x , max-xδ-x∈)))
                f[xδ]≤f[max-xδ-x]
               ∙ cong (fst ∘ f)
                (Σ≡Prop (λ z → isProp<ᵣ x₀ z)
                 (≤→maxᵣ xδ x zz))))
           ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))) ∣₁



  y₀≤g : (u : ℚ) → (p : x₀ ≤ᵣ maxᵣ 0 (rat u) +ᵣ x₀) → y₀ ≤ᵣ fst g (maxᵣ 0 (rat u) +ᵣ x₀) p
  y₀≤g = ℚ.byTrichotomy 0 {A = Y} w
   where
   Y : ℚ → Type
   Y z = (p : x₀ ≤ᵣ maxᵣ 0 (rat z) +ᵣ x₀) →
         y₀ ≤ᵣ fst g (maxᵣ 0 (rat z) +ᵣ x₀) p

   w : ℚ.TrichotomyRec {ℓ = ℓ-zero} 0 Y
   w .ℚ.TrichotomyRec.lt-case m m<0 p =

     ≡ᵣWeaken≤ᵣ y₀ (fst g (maxᵣ 0 (rat m) +ᵣ x₀ ) p) (sym g[x₀]=y₀ ∙
       cong (uncurry (fst g)) (Σ≡Prop (λ z → isProp≤ᵣ x₀ z)
     (sym (Rℝ.+IdL' _ x₀ (maxᵣComm 0 (rat m) ∙
          ≤→maxᵣ (rat m) 0 (<ᵣWeaken≤ᵣ (rat m) 0 (<ℚ→<ᵣ m 0 m<0))))))  )

   w .ℚ.TrichotomyRec.eq-case p = ≡ᵣWeaken≤ᵣ _ _
     (sym g[x₀]=y₀ ∙
      cong (uncurry (fst g)) (Σ≡Prop (λ z → isProp≤ᵣ x₀ z)
      (sym (Rℝ.+IdL' _ _ (maxᵣIdem 0)))))
   w .ℚ.TrichotomyRec.gt-case m 0<m p =
     let 0<max0m : 0 <ᵣ maxᵣ 0 (rat m)
         0<max0m = isTrans<≤ᵣ _ _ _
           (<ℚ→<ᵣ _ _ 0<m)
           (isTrans≤≡ᵣ _ _ _ (≤maxᵣ (rat m) 0) (maxᵣComm (rat m) 0))
         x₀<max0m+x₀ : x₀ <ᵣ maxᵣ 0 (rat m) +ᵣ x₀
         x₀<max0m+x₀ = isTrans≡<ᵣ _ _ _
           (sym (+IdL _))
           (<ᵣ-+o _ _ x₀ 0<max0m)
     in isTrans≤≡ᵣ _ _ _
      (<ᵣWeaken≤ᵣ _ _
       (snd (f (maxᵣ 0 (rat m) +ᵣ x₀ , x₀<max0m+x₀))))
      (sym (g[x₀<x]=f
       (maxᵣ 0 (rat m) +ᵣ x₀ , x₀<max0m+x₀) p))

 nth-rootNonNegDef : ∀ (n : ℕ₊₁) → Σ (Σ ℝ (0 ≤ᵣ_) → Σ ℝ (0 ≤ᵣ_))
                                 (λ f' →
                                    ((fst (f' (0 , ≤ᵣ-refl 0)) ≡ 0) ×
                                     ((x : Σ ℝ (0 <ᵣ_)) →
                                      fst (f' (x .fst , <ᵣWeaken≤ᵣ 0 (x .fst) (snd x))) ≡
                                      root (1+ n .ℕ₊₁.n) (x .fst , x .snd) .fst))
                                    × IsUContinuousℙ (pred≥ 0) (curry ((λ r → fst r) ∘ f')))
 nth-rootNonNegDef n@(1+ n') = extendℝFnLeft 0 0
   (λ x → root n x)
    (λ ε → (ℚ._ℚ₊^ⁿ_ ε (suc n')) ,
      λ r r∈ x＃r x →
        isTrans<≡ᵣ _ _ _
         (isTrans≡<ᵣ _ _ _
           ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ (snd (root (1+ n .ℕ₊₁.n) (r , r∈))))
           (ₙ√-StrictMonotone n (subst2 _<ᵣ_
            ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ r∈)
            (sym (cong fst (^ℤ-rat ε (pos (suc n')))))
            x)))
           (cong fst (Iso.ret (nth-pow-root-iso n)
            (ℚ₊→ℝ₊ ε))) )
    (uContRoot n) λ x y x≤y → ₙ√-Monotone {x = x} {y = y} n x≤y


nth-rootNonNeg : ℕ₊₁ → Σ ℝ (0 ≤ᵣ_) → Σ ℝ (0 ≤ᵣ_)
nth-rootNonNeg n = fst (nth-rootNonNegDef n)

nth-rootNonNeg0 : (n : ℕ₊₁) (p : 0 ≤ᵣ 0) → 0 ≡ fst (nth-rootNonNeg n (0 , p))
nth-rootNonNeg0 n p = sym (fst (fst (snd (nth-rootNonNegDef n))))
  ∙ cong (λ p → fst (nth-rootNonNeg n (0 , p)))
   (isProp≤ᵣ 0 0 (≤ᵣ-refl 0) p)

_₀₊^ⁿ_ : ℝ₀₊ → ℕ → ℝ₀₊
(x , 0≤x) ₀₊^ⁿ n  = (x ^ⁿ n) , 0≤x^ⁿ x n 0≤x

max-rat₀₊ : (q : ℚ) →
  (maxᵣ 0 (rat q) , ≤maxᵣ 0 (rat q)) ≡
  (rat (ℚ.max 0 q) , ≤ℚ→≤ᵣ 0 (ℚ.max 0 q) (ℚ.≤max 0 q))
max-rat₀₊ q = ℝ₀₊≡ (maxᵣ-rat 0 q)


nth-pow-root-iso₀₊ : ℕ₊₁ → Iso ℝ₀₊ ℝ₀₊
nth-pow-root-iso₀₊ n .Iso.fun = λ x → x ₀₊^ⁿ (ℕ₊₁→ℕ n)
nth-pow-root-iso₀₊ n .Iso.inv = (nth-rootNonNeg n)
nth-pow-root-iso₀₊ n .Iso.sec (x , 0≤x) = ww
 where
 opaque
  unfolding maxᵣ minᵣ
  ww : ((nth-rootNonNeg n (x , 0≤x)) ₀₊^ⁿ (ℕ₊₁→ℕ n)) ≡ (x , 0≤x)
  ww =
   ℝ₀₊≡
       (cong ((_^ⁿ (ℕ₊₁→ℕ n)) ∘ fst ∘  (nth-rootNonNeg n))
         (ℝ₀₊≡ (sym (≤→maxᵣ 0 x 0≤x)))
          ∙∙ ≡Continuous
              (λ x →
                ((_^ⁿ (ℕ₊₁→ℕ n)) ∘ fst ∘  (nth-rootNonNeg n))
                 (maxᵣ 0 x , ≤maxᵣ 0 x))
              (maxᵣ 0)
             (IsContinuous∘
               (_^ⁿ (ℕ₊₁→ℕ n))
               (λ x → fst (nth-rootNonNeg n (maxᵣ 0 x , ≤maxᵣ 0 x)))
               (IsContinuous^ⁿ (ℕ₊₁→ℕ n))
                (IsContinuousWithPred∘IsContinuous
                 (pred≥ 0)
                 (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))

                  (maxᵣ 0)
                   (λ x → ≤maxᵣ 0 x)
                   (IsUContinuousℙ→pointwiseℙ (pred≥ 0)
                     (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))
                     (snd (snd (nth-rootNonNegDef n))))
                   (IsContinuousMaxL 0)))
             (IsContinuousMaxL 0)
            (λ q → subst
              (λ z → (fst (nth-rootNonNeg n z) ^ⁿ (ℕ₊₁→ℕ n)) ≡ fst z)
              (sym (max-rat₀₊ q))
              (byDichotomyMax 0
                {λ r r∈ → (fst (nth-rootNonNeg n (rat r , r∈)) ^ⁿ (ℕ₊₁→ℕ n))
                    ≡ rat r } w q (≤ℚ→≤ᵣ 0 (ℚ.max 0 q) (ℚ.≤max 0 q)))) x ∙∙
         ≤→maxᵣ 0 x 0≤x)
    where
    w : DichotomyRec {ℓ = ℓ-zero} 0 λ m ≤m →
         (fst (nth-rootNonNeg n (rat m , ≤m)) ^ⁿ ℕ₊₁→ℕ n) ≡ rat m
    w .DichotomyRec.eq-case =
      cong (_^ⁿ suc (n .ℕ₊₁.n))
       (fst (fst (snd (nth-rootNonNegDef n))))
      ∙ 0^ⁿ (n .ℕ₊₁.n)
    w .DichotomyRec.gt-case m m>0 =
     cong (_^ⁿ suc (n .ℕ₊₁.n))
       (snd (fst (snd (nth-rootNonNegDef n))) (rat m , m>0))
      ∙ cong fst  (nth-pow-root-iso n .Iso.sec
        (rat m , m>0))

nth-pow-root-iso₀₊ n .Iso.ret (x , 0≤x) = ww
 where
 opaque
  unfolding maxᵣ
  ww : ((nth-rootNonNeg n ((x , 0≤x)  ₀₊^ⁿ (ℕ₊₁→ℕ n)))) ≡ (x , 0≤x)
  ww = (cong ((nth-rootNonNeg n) ∘
      (λ (x , 0≤x) → x ^ⁿ (ℕ₊₁→ℕ n) , 0≤x^ⁿ x (ℕ₊₁→ℕ n) 0≤x ))
        (sym (ℝ₀₊≡ (≤→maxᵣ 0 x 0≤x))) ∙
        ℝ₀₊≡ (≡Continuous
            (λ x →
              (fst (nth-rootNonNeg n
                ((maxᵣ 0 x) ^ⁿ (ℕ₊₁→ℕ n) , 0≤x^ⁿ (maxᵣ 0 x) (ℕ₊₁→ℕ n) (≤maxᵣ 0 x))
                 ))
               )
            (maxᵣ 0)
            (IsContinuousWithPred∘IsContinuous (pred≥ 0)
             (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))
             (λ x → (maxᵣ 0 x) ^ⁿ (ℕ₊₁→ℕ n))
             (λ x → 0≤x^ⁿ (maxᵣ 0 x) (ℕ₊₁→ℕ n) (≤maxᵣ 0 x))
             (IsUContinuousℙ→pointwiseℙ (pred≥ 0)
               (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))
                   (snd (snd (nth-rootNonNegDef n))))
             (IsContinuous∘
              (_^ⁿ (ℕ₊₁→ℕ n))
              (maxᵣ 0)
              (IsContinuous^ⁿ (ℕ₊₁→ℕ n))
              (IsContinuousMaxL 0))
              )
            (IsContinuousMaxL 0)
            (λ q → subst
              (λ z → fst (nth-rootNonNeg n
                ((fst z ^ⁿ (ℕ₊₁→ℕ n)) , 0≤x^ⁿ (fst z) (ℕ₊₁→ℕ n) (snd z)))
                ≡ fst z)
              (sym (max-rat₀₊ q))
              (byDichotomyMax 0
              {λ r r∈ →
                 (fst (nth-rootNonNeg n (rat r ^ⁿ (ℕ₊₁→ℕ n) ,
                  0≤x^ⁿ (rat r) (ℕ₊₁→ℕ n) r∈)))
                  ≡ rat r }
              w q (≤ℚ→≤ᵣ 0 (ℚ.max 0 q) (ℚ.≤max 0 q))))
            x
        ∙
        (≤→maxᵣ 0 x 0≤x)))
   where
   w : DichotomyRec {ℓ = ℓ-zero} 0 λ m ≤m →
         fst (nth-rootNonNeg n
           ((rat m ^ⁿ ℕ₊₁→ℕ n) , 0≤x^ⁿ (rat m) (ℕ₊₁→ℕ n) ≤m)) ≡ rat m
   w .DichotomyRec.eq-case =
       cong (fst ∘ nth-rootNonNeg n)
         (ℝ₀₊≡
          {x = (0 ^ⁿ (ℕ₊₁→ℕ n) , 0≤x^ⁿ 0 (ℕ₊₁→ℕ n) (≤ᵣ-refl 0))}
          {y = (0 , ≤ᵣ-refl 0)}
          (0^ⁿ (n .ℕ₊₁.n)))
     ∙ fst (fst (snd (nth-rootNonNegDef n)))
   w .DichotomyRec.gt-case m m>0 =
     let mⁿ = rat m ^ⁿ (ℕ₊₁→ℕ n)
         0<mⁿ : 0 <ᵣ mⁿ
         0<mⁿ = 0<x^ⁿ (rat m) (ℕ₊₁→ℕ n) m>0
         0≤mⁿ : 0 ≤ᵣ mⁿ
         0≤mⁿ = 0≤x^ⁿ (rat m) (ℕ₊₁→ℕ n) (<ᵣWeaken≤ᵣ 0 (rat m) m>0)
     in (cong (fst ∘ nth-rootNonNeg n)
       (ℝ₀₊≡
        {x = (mⁿ , 0≤mⁿ)}
        {y = (mⁿ , <ᵣWeaken≤ᵣ 0 mⁿ 0<mⁿ)}
        refl)
    ∙ (snd (fst (snd (nth-rootNonNegDef n))) (mⁿ , 0<mⁿ)))
    ∙ cong fst  (nth-pow-root-iso n .Iso.ret
       (rat m , m>0))


nth-pow-root-equiv₀₊ : ℕ₊₁ → ℝ₀₊ ≃ ℝ₀₊
nth-pow-root-equiv₀₊ n = isoToEquiv (nth-pow-root-iso₀₊ n)

1st-rootNonNeg : (x : ℝ₀₊) → nth-rootNonNeg 1 x ≡ x
1st-rootNonNeg x@(r , 0≤r) =
  cong (nth-rootNonNeg 1) (sym (ℝ₀₊≡ (·IdR r)))
    ∙ Iso.ret (nth-pow-root-iso₀₊ 1) x
