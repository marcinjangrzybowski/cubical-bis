module Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding


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
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.RationalsImports using (ℚ₊ ; _+₊_ ; _·₊_ ; _/2₊ ; min₊)
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.TrigBase
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot hiding (invℚ₊ ; _ℚ₊^ⁿ_)
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.ArcSin.Base

open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base public
 arcSin⟨⟩∘sin-ℚ : ∀ (Q : ℚ₊) → (Q<π/2 : rat (fst Q) <ᵣ π-number/2)
  → ∀ q → (0 ℚ.≤ q) ⊎ (q ℚ.≤ 0)
  →  (q∈ : rat q ∈ intervalℙ (-ᵣ (rat (fst Q))) (rat (fst Q)))
  → ∀ sinq∈
   → arcSin⟨⟩ (sin (rat q)) sinq∈

   ≡ (rat q)
 arcSin⟨⟩∘sin-ℚ Q Q<π/2 q (inl 0≤q') (_ , q<Q) sinq∈@(_ , sinq<1) =
  let 0≤q : 0 ≤ᵣ (rat q)
      0≤q = ≤ℚ→≤ᵣ _ _ 0≤q'
      q<π/2 : (rat q) <ᵣ π-number/2
      q<π/2 = isTrans≤<ᵣ _ _ _ q<Q Q<π/2
      0≤sinq : 0 ≤ᵣ sin (rat q)
      0≤sinq = fst $ x∈[0,π/2⟩→sin[x]∈[0,1⟩ (rat q)
          (0≤q , q<π/2)

  in 𝐑'.+IdL' _ _ (
       cong -ᵣ_
         (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (-ᵣ (sin (rat q)))
              decℚ≤ᵣ?
              (isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _  0≤sinq)
               (-ᵣ-rat 0)  )))
           ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
       ∙ -ᵣ-rat 0)
     ∙ cong (uncurry arcSin)
         ((Σ≡Prop (∈-isProp (pred≤< 0 1))
          (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ ( 0≤sinq , sin≤1 _)))))
          ∙ secArcSin _ (0≤sinq , sinq<1) (0≤q , q<π/2)
 arcSin⟨⟩∘sin-ℚ Q Q<π/2 q (inr q'≤0) (-Q<-q , _) sinq∈@(-1<sinq , _) =
  let 0≤-q : 0 ≤ᵣ -ᵣ rat q
      0≤-q = isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0))
              (-ᵣ≤ᵣ _ _ (≤ℚ→≤ᵣ _ _ q'≤0))

      sin-q<1 : sin (-ᵣ rat q) <ᵣ 1
      sin-q<1 = subst2 _<ᵣ_ (sin-odd (rat q)) (-ᵣ-rat -1)
          (-ᵣ<ᵣ _ _ -1<sinq)

      -q<π/2 : -ᵣ rat q <ᵣ π-number/2
      -q<π/2 = isTrans≤<ᵣ _ _ _ (-ᵣ≤ᵣ _ _ -Q<-q)
                (isTrans≡<ᵣ _ _ _ (-ᵣInvol _) Q<π/2)

      sinq≤0 : sin (rat q) ≤ᵣ 0
      sinq≤0 = ≤ᵣ-ᵣ _ _
        (subst2 _≤ᵣ_ (sym (-ᵣ-rat 0)) (sym (sin-odd (rat q)))
         (fst (x∈[0,π/2⟩→sin[x]∈[0,1⟩ (-ᵣ (rat q))
          (0≤-q , -q<π/2))))

  in 𝐑'.+IdR' _ _
      (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (sin (rat q))
              decℚ≤ᵣ? sinq≤0))
           ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
     ∙ cong -ᵣ_
       (cong (uncurry arcSin)
         (Σ≡Prop (∈-isProp (pred≤< 0 1)) {clampᵣ 0 1 (-ᵣ sin (rat q)) , _}
           (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _
             (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _ sinq≤0) ,
              (isTrans≤ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _
               (≤absᵣ _) (sym (-absᵣ _))) (∣sin∣≤1 (rat q))))) ∙ sin-odd _))
         ∙ secArcSin _ (subst2 _≤ᵣ_
           (-ᵣ-rat 0) (sin-odd _) (-ᵣ≤ᵣ _ _ sinq≤0) , sin-q<1)
           (0≤-q , -q<π/2))
     ∙ -ᵣInvol (rat q)



 ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ : ∀ x → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
       → sin x ∈ ointervalℙ -1 1
 ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ x x∈@(<x , x<) =
  isTrans≡<ᵣ _ _ _ ((sym (-ᵣ-rat 1) ∙ cong -ᵣ_ (sym (sin[π/2]≡1)))
   ∙ sin-odd π-number/2)
   (sin-strictMonotone (-ᵣ π-number/2) x
     (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ π-number/2₊ π-number/2₊)) (ointervalℙ⊆intervalℙ _ _ x x∈) <x) ,
   isTrans<≡ᵣ _ _ _
     (sin-strictMonotone x (π-number/2)
      (ointervalℙ⊆intervalℙ _ _ x x∈)
       (<ᵣWeaken≤ᵣ _ _ ((-ℝ₊<ℝ₊ π-number/2₊ π-number/2₊)) , ≤ᵣ-refl _) x<)
     sin[π/2]≡1

 sin∘arcSin⟨⟩ℚ :
      ∀ q q∈ → (0 ℚ.≤ q) ⊎ (q ℚ.≤ 0)
    → sin (arcSin⟨⟩ (rat q) q∈) ≡ (rat q)
 sin∘arcSin⟨⟩ℚ q (-1<q , q<1) (inl 0≤q') =
   let 0≤q = ≤ℚ→≤ᵣ 0 q 0≤q'

   in cong sin (𝐑'.+IdL' _ _
        (cong -ᵣ_
          (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (-ᵣ rat q)
              decℚ≤ᵣ?
              (isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _  0≤q)
               (-ᵣ-rat 0)  )))
           ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))  ∙
          -ᵣ-rat 0)
          ∙ cong (uncurry arcSin)
              (Σ≡Prop (∈-isProp (pred≤< 0 1))
                (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _
                 (0≤q , <ᵣWeaken≤ᵣ _ _ q<1)))))
         ∙ retArcSin _ (0≤q , q<1)
 sin∘arcSin⟨⟩ℚ q (-1<q , _) (inr q≤0') =
   let q≤0 = ≤ℚ→≤ᵣ q 0 q≤0'
       0≤-q : 0 ≤ᵣ -ᵣ rat q
       0≤-q = isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _ q≤0)
       -q<1 : -ᵣ rat q <ᵣ 1
       -q<1 = isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ -1<q)
                (-ᵣ-rat -1)
   in cong sin (𝐑'.+IdR' _ _ (cong (uncurry arcSin)
            (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (x≤→clampᵣ≡ 0 1 (rat q)
              decℚ≤ᵣ? q≤0))
              ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
      ∙ cong -ᵣ_ (cong (uncurry arcSin)
         (Σ≡Prop (∈-isProp (pred≤< 0 1))
           (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _ (0≤-q , (<ᵣWeaken≤ᵣ _ _ -q<1)))))))
     ∙ sym (sin-odd _)
     ∙ cong -ᵣ_ (retArcSin _ (0≤-q , -q<1))
     ∙ -ᵣInvol _




 opaque
  unfolding _+ᵣ_
  IsContinuousWPArcSin⟨⟩ : IsContinuousWithPred (ointervalℙ -1 1) arcSin⟨⟩
  IsContinuousWPArcSin⟨⟩ =
    contDiagNE₂WP sumR (ointervalℙ -1 1)
             (λ x x∈ → -ᵣ (arcSin (clampᵣ 0 1 (-ᵣ x))
             ((≤clampᵣ 0 1 (-ᵣ x) decℚ≤ᵣ?) ,
              isTrans≤<ᵣ _ (maxᵣ 0 (-ᵣ x)) _
                  (min≤ᵣ (maxᵣ 0 (-ᵣ x)) 1 )
                  (max<-lem 0 (-ᵣ x) 1 (decℚ<ᵣ? {0} {1})
                    ((isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (fst x∈))
                     (-ᵣ-rat -1)))))))
           (λ x x∈ →
             arcSin (clampᵣ 0 1 x)
              ((≤clampᵣ 0 1 x decℚ≤ᵣ?)
               , isTrans≤<ᵣ _ (maxᵣ 0 x) _
                  (min≤ᵣ (maxᵣ 0 x) 1 )
                  (max<-lem 0 x 1 (decℚ<ᵣ? {0} {1}) (snd x∈))))
            (IsContinuousWithPred-ᵣ (ointervalℙ -1 1)
              _
              (IsContinuousWP∘ (pred≤< 0 1) (ointervalℙ -1 1)
             _
             _ _
             IsContinuousWithPredArcSin
             (IsContinuousWP∘ (ointervalℙ -1 1) (ointervalℙ -1 1)
              _
              _
              (λ x (<x , x<) → (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 1))
                (-ᵣ<ᵣ _ _ x<)) ,
               (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ <x) (-ᵣ-rat -1)))
              (AsContinuousWithPred (ointervalℙ -1 1)
                _ (IsContinuousClamp 0 1))
              ((AsContinuousWithPred (ointervalℙ -1 1)
                _ IsContinuous-ᵣ)))))
            (IsContinuousWP∘ (pred≤< 0 1) (ointervalℙ -1 1)
             arcSin
             _ _
             IsContinuousWithPredArcSin
             (((AsContinuousWithPred (ointervalℙ -1 1)
              (clampᵣ 0 1 ) (IsContinuousClamp 0 1)))))


arcSin⟨⟩∘sin : ∀ x sinx∈
 → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
 → arcSin⟨⟩ (sin x) sinx∈ ≡ x
arcSin⟨⟩∘sin x sinx∈@(<negx , x<) x∈ =
  PT.rec (isSetℝ _ _)
    (λ (Q , ∣x∣<Q , Q<π/2) →
      let Q₊ = (Q , (ℚ<→0< Q (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) ∣x∣<Q))))
          x∈Q : x ∈ intervalℙ (rat (ℚ.- Q)) (rat Q)
          x∈Q = isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat Q))
                 (-ᵣ≤ᵣ _ _
                  (isTrans≤ᵣ _ _ _ (≤absᵣ _)
                    (isTrans≡≤ᵣ _ _ _ (sym (-absᵣ _)) (<ᵣWeaken≤ᵣ _ _ ∣x∣<Q) ))))
                    (-ᵣInvol _ ) ,
                 isTrans≤ᵣ _ _ _ (≤absᵣ _)
                 (<ᵣWeaken≤ᵣ _ _ ∣x∣<Q )

          zzz = cong (uncurry arcSin⟨⟩)
                (Σ≡Prop (∈-isProp (ointervalℙ (-1) 1))
                  {u = _ , (<negx , x<)}
                  {v = _ , _}
                      (cong sin
                       ((∈ℚintervalℙ→clampᵣ≡ (rat ((ℚ.- Q))) (rat Q)
                 x x∈Q))))

      in zzz ∙∙
         ≡Continuous
           (λ x → arcSin⟨⟩ (sin (clampᵣ (rat (ℚ.- Q)) (rat Q) x))
                     (⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ _ (sym-intervalℙ⊆ointervalℙ _ _ Q<π/2
                      _ (
                        subst (λ -Q → clampᵣ (rat (ℚ.- Q)) (rat Q) x ∈
                          intervalℙ -Q (rat Q))
                          (sym (-ᵣ-rat Q))
                           ((clampᵣ∈ℚintervalℙ (rat (ℚ.- Q)) (rat Q)
                             (isTrans≡≤ᵣ _ _ _
                               (sym (-ᵣ-rat Q))
                               (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ Q₊) (ℚ₊→ℝ₊ Q₊)))) x))))))
           (λ x → clampᵣ (rat ((ℚ.- Q))) (rat Q) x)
           (IsContinuousWithPred∘IsContinuous
              (ointervalℙ -1 1)
               arcSin⟨⟩ _ _
               IsContinuousWPArcSin⟨⟩
                (IsContinuous∘ _ _
                  (isContinuousSin)
                  (IsContinuousClamp (rat ((ℚ.- Q))) (rat Q))))
           (IsContinuousClamp (rat ((ℚ.- Q))) (rat Q))

           (λ q →
            let z = sym (clampᵣ-rat (ℚ.- Q) Q q)
                q∈ = (subst-∈ (intervalℙ (-ᵣ rat Q) (rat Q))
                     ((cong clampᵣ (-ᵣ-rat Q) ≡$ rat Q ≡$ rat q) ∙ sym z)
                     (clampᵣ∈ℚintervalℙ _ (rat Q)
                       (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ Q₊) (ℚ₊→ℝ₊ Q₊))) (rat q)))
                sinq∈ : sin (rat (ℚ.clamp (ℚ.- Q) Q q)) ∈ ointervalℙ -1 1
                sinq∈ = ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ _
                  (sym-intervalℙ⊆ointervalℙ (rat Q) π-number/2
                    Q<π/2 (rat (ℚ.clamp (ℚ.- Q) Q q)) q∈)
            in cong (uncurry arcSin⟨⟩)
                (Σ≡Prop (∈-isProp (ointervalℙ (-1) 1))
                      (cong sin (sym z)))
                  ∙∙ arcSin⟨⟩∘sin-ℚ Q₊ Q<π/2
                   (ℚ.clamp (ℚ.- Q) Q q)
                    (ℚ.≤cases 0 (ℚ.clamp (ℚ.- Q) Q q)) q∈ sinq∈ ∙∙ z)
               x
         ∙∙ (sym (∈ℚintervalℙ→clampᵣ≡ (rat ((ℚ.- Q))) (rat Q)
                 x x∈Q)))
    (denseℚinℝ (absᵣ x) π-number/2  (
     ointerval→abs< x π-number/2 x∈))

sym-clamp-rat : ∀ q (Q : ℚ₊) →
                     clampᵣ (-ᵣ rat (fst Q)) (rat (fst Q)) (rat q) ≡
                    rat (ℚ.clamp (ℚ.- (fst Q)) (fst Q) q)
sym-clamp-rat q Q = (cong clampᵣ (-ᵣ-rat (fst Q))
  ≡$ (rat (fst Q)) ≡$ rat q) ∙ clampᵣ-rat (ℚ.- (fst Q)) (fst Q) q



sin∘arcSin⟨⟩ : ∀ x x∈ → sin (arcSin⟨⟩ x x∈) ≡ x
sin∘arcSin⟨⟩ x x∈ = fst (propTruncIdempotent≃ (isSetℝ _ _)) $ do
  let h = λ (x : ℝ) → substEquiv (λ X → x ∈
          ointervalℙ X (rat [ pos 1 / 1+ 0 ]))
         (sym (-ᵣ-rat 1))
  (q , ∣x∣<q , q<1) ← denseℚinℝ (absᵣ x) 1 (ointerval→abs< x 1
        (fst (h x) x∈))
  let q₊ : ℚ₊
      q₊ = q , ℚ<→0< q (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) ∣x∣<q))
      p = ∈ℚintervalℙ→clampᵣ≡ (-ᵣ (rat q)) (rat q) x
            (abs≤→interval x (rat q) (<ᵣWeaken≤ᵣ _ _ ∣x∣<q))
      hh = clampᵣ∈ℚintervalℙ _ _
                (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ q₊) (ℚ₊→ℝ₊ q₊)))
  ∣ cong sin (cong (uncurry arcSin⟨⟩)
       (Σ≡Prop (∈-isProp (ointervalℙ _ _))
         p))
    ∙∙ ≡Continuous
        (λ x → sin (arcSin⟨⟩
          (clampᵣ (-ᵣ (rat q)) (rat q) x)
            (invEq (h _) (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _
               (hh x)))))
        (clampᵣ (-ᵣ (rat q)) (rat q))
        (IsContinuous∘ _ _ isContinuousSin
           (IsContinuousWithPred∘IsContinuous
             (ointervalℙ -1 1)
             _
             _
             (λ x → invEq (h _)
                (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _ _))
             IsContinuousWPArcSin⟨⟩
             (IsContinuousClamp (-ᵣ (rat q)) (rat q))))
        (IsContinuousClamp (-ᵣ (rat q)) (rat q))
         (λ y →
         let p' = sym (sym-clamp-rat y q₊)
         in cong sin (cong (uncurry arcSin⟨⟩)
              (Σ≡Prop (∈-isProp (ointervalℙ -1 1))
                (sym p'))) ∙
             sin∘arcSin⟨⟩ℚ
             (ℚ.clamp (ℚ.- q) q y)
             (invEq (h _) (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _
                  ((subst-∈ (intervalℙ (-ᵣ rat q) (rat q))
                     (sym-clamp-rat y q₊)
                    (hh (rat y)) ))))
              (ℚ.≤cases 0 (ℚ.clamp (ℚ.- q) q y))
                 ∙ p')
         x
    ∙∙ sym p ∣₁


sinIso⟨-π/2,π2⟩ : Iso (Σ _ (_∈ ointervalℙ (-ᵣ π-number/2) π-number/2))
                      (Σ _ (_∈ ointervalℙ -1 1))
sinIso⟨-π/2,π2⟩ .Iso.fun (x , x∈) = sin x , ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ x x∈
sinIso⟨-π/2,π2⟩ .Iso.inv (x , x∈) = arcSin⟨⟩ x x∈ , arcSin⟨⟩∈ x x∈
sinIso⟨-π/2,π2⟩ .Iso.sec (x , x∈) =
 Σ≡Prop (∈-isProp (ointervalℙ -1 1))
  (sin∘arcSin⟨⟩ _ _)
sinIso⟨-π/2,π2⟩ .Iso.ret (x , x∈) =
 Σ≡Prop (∈-isProp (ointervalℙ (-ᵣ π-number/2) π-number/2))
  (arcSin⟨⟩∘sin _ _ x∈)


equivSin⟨⟩ : (Σ _ (_∈ ointervalℙ (-ᵣ π-number/2) π-number/2))
             ≃ (Σ _ (_∈ ointervalℙ -1 1))
equivSin⟨⟩ = isoToEquiv sinIso⟨-π/2,π2⟩
