module Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Injection where

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
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Partition using (ℚ<→0< ; rtp-1/n ; riemannSum-empty)
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open IntegrationUC rtp-1/n
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.FundamentalTheoremOfCalculus using
  ( Integral-additive
  ; FTOC⇒*
  ; FTOC⇐''
  )
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
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


open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Core

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Definition public
arcSinInj : ∀ x y x∈ y∈ → arcSin x x∈ ≡ arcSin y y∈ → x ≡ y
arcSinInj x y x∈@(0≤x , x<1) y∈@(0≤y , y<1) p =
  ≡-byContracdition _ _ w


  where
  w : (ε : ℚ₊) → rat (fst ε) <ᵣ absᵣ (x -ᵣ y) → ⊥
  w ε ε< =
    ⊎.rec
           (w' y x y∈ x∈ (sym p))
           (w' x y x∈ y∈ p)
      cases<
   where
     cases< :  (y +ᵣ rat (fst ε) <ᵣ x) ⊎ (x +ᵣ rat (fst ε) <ᵣ y)
     cases< = ⊎.map
         (λ 0<x-y →
            let z = isTrans<≡ᵣ _ _ _ ε< (absᵣPos _ 0<x-y)
            in isTrans≡<ᵣ _ _ _ (+ᵣComm _ _) (a<b-c⇒a+c<b _ _ _ z))
         (λ 0<y-x →
            let z = isTrans<≡ᵣ _ _ _ ε< (absᵣNeg _ 0<y-x ∙ -[x-y]≡y-x _ _)
            in isTrans≡<ᵣ _ _ _ (+ᵣComm _ _) (a<b-c⇒a+c<b _ _ _ z))
       (decCut _ (isTrans<ᵣ _ _ _ (snd (ℚ₊→ℝ₊ ε)) ε<))

     w' : ∀ x y x∈ y∈ → arcSin x x∈ ≡ arcSin y y∈ →
          x +ᵣ rat (fst ε) <ᵣ y → ⊥
     w' x y x∈@(0≤x , x<1) y∈@(0≤y , y<1) p x+ε<y =
       ≤ᵣ→≯ᵣ (fst Δ) 0
         (≤-o+-cancel _ _ _ (≡ᵣWeaken≤ᵣ _ _ (cc ∙ sym p ∙ sym (+IdR _))))
         0<Δ

      where
       x<y : x <ᵣ y
       x<y = isTrans<ᵣ _ _ _
         (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
          (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ ε)))) x+ε<y

       x≤y : x ≤ᵣ y
       x≤y = <ᵣWeaken≤ᵣ _ _ x<y

       Δ : Σ ℝ (on[_,_]IntegralOf_is_ x y (curry ∘ (λ x' x'∈ → arcSin' x' _)))
       Δ = PT.rec
           (IntegratedℙPropℙ _ _ x≤y
             (curry ∘ (λ x' x'∈ → arcSin' x' _)))
               (Integrate-UContinuousℙ
                x
                y
                x≤y
                (λ x' x'∈ → arcSin' x' _) ∘
                IsUContinuousℙ-restr (intervalℙ 0 y) (intervalℙ x y) _
                  λ _ → map-fst λ x∈ → isTrans≤ᵣ _ _ _ 0≤x x∈)
                (arcSin'-UC y y∈)

       0<Δ : 0 <ᵣ fst Δ
       0<Δ = isTrans<≤ᵣ 0 _ _
         (isTrans<≡ᵣ _ _ _ (x<y→0<y-x _ _ x<y) (sym (Rℝ.·IdL _)))
          (Integral-≤ x y x≤y (λ _ _ _ → 1)
            _
            _
            _
            (λ x' ≤x' x'≤ → (isTrans≡≤ᵣ _ _ _ 1≡arcSin'0
              (arcSin'-Monotone _ _ _ _ (isTrans≤ᵣ _ _ _ 0≤x ≤x'))))
            (IntegralConstℙ x y x≤y 1)
            (snd Δ))

       arcSin-x : _
       arcSin-x = subst (λ f → on[ 0 , x ]IntegralOf
            f is
            arcSinDef x (0≤x , x<1) .fst)
              (funExt₃ λ x' _ _ →
                cong (arcSin' x') (∈-isProp (pred≤< 0 1) _ _ _))
              (snd (arcSinDef x x∈))

       cc : arcSin x (0≤x , x<1) +ᵣ Δ .fst ≡ arcSin y (0≤y , y<1)
       cc = Integral-additive 0 x y
              0≤x x≤y
                (λ r z z₁ → arcSin' r (z , isTrans≤<ᵣ r y 1 z₁ y<1))
                ((arcSin x x∈))
               (Δ .fst)
               (arcSin y y∈)
               arcSin-x (snd Δ) (snd (arcSinDef y y∈))
