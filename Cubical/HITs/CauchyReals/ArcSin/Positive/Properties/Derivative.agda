module Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Derivative where

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
arcSinDer : ∀ x → (x∈ : x ∈ ointervalℙ 0 1) →
 uDerivativeOfℙ intervalℙ 0 x ,
  (λ x' (≤x , x≤) → arcSin x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈))) is
    (λ x' (≤x , x≤) → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈)))
arcSinDer x x∈ =
   PT.rec (isProp-uDerivativeOfℙ (intervalℙ 0 x) _ _)
        (FTOC⇒* 0 x (<ᵣWeaken≤ᵣ _ _ (fst x∈))
          _
          _
            (λ x₁ x∈₁ y y∈ →
              (fst y∈ , isTrans≤ᵣ _ _ _ (snd y∈) (snd x∈₁)))
            λ y y∈ →
              subst (λ f → on[ 0 , y ]IntegralOf
                f
                is (arcSinDef y (y∈ .fst ,
                 isTrans≤<ᵣ y x 1 (y∈ .snd) (snd x∈)) .fst))
                (funExt₃ λ x' _ _ →
                 cong (arcSin' x') (∈-isProp (pred≤< 0 1) _ _ _) )
                  ((snd (arcSinDef y
                         (y∈ .fst , isTrans≤<ᵣ y x 1 (y∈ .snd) (snd x∈))))))
        (arcSin'-UC x (<ᵣWeaken≤ᵣ _ _ (fst x∈) , snd x∈))



x∈[0,π/2⟩→sin[x]∈[0,1⟩ : ∀ x → x ∈ pred≤< 0 π-number/2 → sin x ∈ pred≤< 0 1
x∈[0,π/2⟩→sin[x]∈[0,1⟩ x x∈ =
 isTrans≡≤ᵣ _ _ _ (sym sin0=0)
  (sin-firstQuarter-Monotone 0 x
   (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ 0<π-number/2)
    (map-snd (<ᵣWeaken≤ᵣ _ _) x∈)
    (fst x∈))
  ,
  (isTrans<≡ᵣ _ _ _
   (sin-firstQuarter-strictMonotone _ _
    (fst x∈ , <ᵣWeaken≤ᵣ _ _ (snd x∈))
     (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) (snd x∈))
   sin[π/2]≡1)

x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ : ∀ x → x ∈ ointervalℙ 0 π-number/2 → sin x ∈ ointervalℙ 0 1
x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈ =
  isTrans≡<ᵣ _ _ _ (sym sin0=0)
  (sin-firstQuarter-strictMonotone 0 x
   ((≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ 0<π-number/2))
    (ointervalℙ⊆intervalℙ _ _ _ x∈)
    (fst x∈))
  ,
  (isTrans<≡ᵣ _ _ _
   (sin-firstQuarter-strictMonotone _ _
    (ointervalℙ⊆intervalℙ _ _ _ x∈ )
     (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) (snd x∈))
   sin[π/2]≡1)


bounded-arcSin' : ∀ x → (x∈ : x ∈ ointervalℙ 0 1) →
  ∥ Bounded (intervalℙ 0 x)
    (λ x' (≤x , x≤) → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈)))
    ∥₁
bounded-arcSin' x x∈ =
  PT.map
   (map-snd (λ {q} X x' x'∈ →
     isTrans≡≤ᵣ _ _ _ (absᵣPos _ (snd (arcSin'₊ x'
        (map-snd (flip (isTrans≤<ᵣ _ _ _) (snd x∈)) x'∈ ))))
      (isTrans≤ᵣ _ _ _
       (arcSin'-Monotone x' x _ _ (snd x'∈))
       (<ᵣWeaken≤ᵣ _ _ X))))
   (∃ℚ₊LargerThanℝ₊
    (arcSin'₊ x (map-fst (<ᵣWeaken≤ᵣ _ _) x∈)))


sin＃-firstQuarter : (x y : ℝ) (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2) →
      x ＃ y → sin x ＃ sin y
sin＃-firstQuarter x y x∈ y∈ =
 ⊎.map (sin-firstQuarter-strictMonotone x y x∈ y∈)
       (sin-firstQuarter-strictMonotone y x y∈ x∈)

[arcSin∘Sin]'=1 : ∀ x → (x∈ : x ∈ ointervalℙ 0 π-number/2) →
  uDerivativeOfℙ (intervalℙ 0 x) ,
     (λ x' x'∈ → arcSin (sin x')
      ((x∈[0,π/2⟩→sin[x]∈[0,1⟩ x'
       (map-snd (flip (isTrans≤<ᵣ _ _ _) (snd x∈)) x'∈)))) is λ _ _ → 1
[arcSin∘Sin]'=1 x x∈ =
  subst2 (uDerivativeOfℙ (intervalℙ 0 x) ,_is_)
      (funExt₂ λ _ _ → cong (uncurry arcSin)
       (Σ≡Prop (∈-isProp (pred≤< 0 1)) refl))
      (funExt₂ w=)
      w
 where
 w : uDerivativeOfℙ intervalℙ 0 x , _ is _

 w = chainRule-uDerivativeℙ (intervalℙ 0 x) (intervalℙ 0 (sin x))
        (λ x _ → sin x) (λ x _ → cos x) _ _
        (bounded-cos (intervalℙ 0 x))
        (bounded-arcSin' (sin x) (x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈)) --bounded-arcSin'
        (λ y y∈ → fst (x∈[0,π/2⟩→sin[x]∈[0,1⟩ y
          ((map-snd (flip (isTrans≤<ᵣ y x π-number/2) (snd x∈)) y∈))) ,
         sin-firstQuarter-Monotone y x
           (map-snd (flip (isTrans≤ᵣ _ _ _) (<ᵣWeaken≤ᵣ _ _ (snd x∈))) y∈)
           (ointervalℙ⊆intervalℙ _ _ _ x∈) (snd y∈))
        (uContSin (intervalℙ 0 x))
        (arcSinDer (sin x) (x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈))
        (sin'=cos-uder' 0 x (fst x∈))



 w= : ∀ (x' : ℝ) x'∈ →
      _ ≡ 1
 w= x' x'∈ =
   cong (_·ᵣ fst cosx₊)
    (cong (fst ∘ invℝ₊)
      (ℝ₊≡ (cong fst (sym
       (invEq (equivAdjointEquiv
         (_ , isEquiv-₊^ⁿ 2) {_ , snd cosx₊})
        (ℝ₊≡
         (sym (𝐑'.plusMinus _ _)
         ∙ cong (_-ᵣ (sin x' ^ⁿ 2))
         (+ᵣComm _ _ ∙ sin²+cos²=1 x'))))))))
    ∙ ·ᵣComm _ _ ∙ x·invℝ₊[x] cosx₊
  where
   cosx₊ : ℝ₊
   cosx₊ = (cos x' , 0≤x<π/2→0<cos[x] x' (fst x'∈)
     (isTrans≤<ᵣ _ _ _ (snd x'∈) (snd x∈)))
