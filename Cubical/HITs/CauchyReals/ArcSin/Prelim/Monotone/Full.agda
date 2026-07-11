module Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone.Full where

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


open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone.Quarter

sin⟨⟩-strictMonotone :
      (x y : ℝ)
      (x∈ : x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2)
      (y∈ : y ∈ ointervalℙ (-ᵣ π-number/2) π-number/2)
      → x <ᵣ y → sin x <ᵣ sin y
sin⟨⟩-strictMonotone x y x∈ y∈ x<y =
   0<y-x→x<y _ _ (isTrans<≤ᵣ _ _ _
    (snd ((_ , ∣x∣<π/2→0<cos[x] _
      (isTrans<≤ᵣ _ _ _
        (-ᵣ<ᵣ _ _ 0<π-number/2) (isTrans≡≤ᵣ _ _ _ (-ᵣ-rat 0)
         (isTrans≤ᵣ _ _ _ (0≤absᵣ y) (≤maxᵣ _ _) )) ,
          <π/2 )) ₊·ᵣ
      (_ , x<y→0<y-x _ _ x<y)))
    ((Integral-≤ x y x≤y _ _ _ _
      (λ x' ≤x' x'≤ →
        isTrans≤≡ᵣ _ _ _ ((cos-firstQuarter-Monotone
         _ _ (0≤absᵣ _ , <ᵣWeaken≤ᵣ _ _ (isTrans≡<ᵣ _ _ _
              (abs-max x')
              ((max<-lem x' (-ᵣ x') π-number/2
               ( isTrans≤<ᵣ _ _ _ x'≤  (snd y∈) )
               (isTrans<≡ᵣ _ _ _
                (-ᵣ<ᵣ _ _ (isTrans<≤ᵣ _ _ _ (fst x∈) ≤x'))
                 (-ᵣInvol _))))))
          ((isTrans≤ᵣ _ _ _ (0≤absᵣ _) (≤maxᵣ _ _)) ,
           <ᵣWeaken≤ᵣ _ _ <π/2)
          (isTrans≡≤ᵣ _ _ _
           (abs-max x')
            (maxMonotoneᵣ x' (absᵣ y) (-ᵣ x') (absᵣ x)
               (isTrans≤ᵣ _ _ _ x'≤ (≤absᵣ y))
                 (isTrans≤ᵣ _ _ _ (-ᵣ≤ᵣ _ _ ≤x')
                  (isTrans≤≡ᵣ _ _ _
                   (≤absᵣ _)
                   (sym (-absᵣ _))))

              ))))
         (sym (cos∘absᵣ x')))
      (IntegralConstℙ _ _ x≤y (cos (maxᵣ (absᵣ y) (absᵣ x))))
      (∫cos x y x≤y))))
  where
  x≤y = <ᵣWeaken≤ᵣ _ _ x<y

  <π/2 : maxᵣ (absᵣ y) (absᵣ x) <ᵣ π-number/2
  <π/2 = max<-lem (absᵣ y) (absᵣ x) _
             (isTrans≡<ᵣ _ _ _
              (abs-max y) (max<-lem y (-ᵣ y) π-number/2
               ((snd y∈))
               (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ ( (fst y∈)))
                 (-ᵣInvol _))))
             ((isTrans≡<ᵣ _ _ _
              (abs-max x)
              ((max<-lem x (-ᵣ x) π-number/2
               ( (snd x∈))
               (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ ((fst x∈)))
                 (-ᵣInvol _))))))

sin-strictMonotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      (y∈ : y ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      → x <ᵣ y → sin x <ᵣ sin y
sin-strictMonotone x y x∈ y∈ x<y =

 let (m , x<m , m<y)  = denseℝ _ _ x<y
     (m' , x<m' , m'<m)  = denseℝ _ _ x<m
     m∈ : m ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
     m∈ = (isTrans≤<ᵣ _ _ _ (fst x∈) x<m) , (isTrans<≤ᵣ _ _ _ m<y (snd y∈) )
     m'∈ : m' ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
     m'∈ = (isTrans≤<ᵣ _ _ _ (fst x∈) x<m') , isTrans<≤ᵣ _ _ _
         (isTrans<ᵣ _ _ _ m'<m m<y) (snd y∈)
 in isTrans<≤ᵣ _ _ _ (isTrans≤<ᵣ _ _ _
      (sin-Monotone _ _ x∈ (ointervalℙ⊆intervalℙ _ _ m' m'∈)
       (<ᵣWeaken≤ᵣ _ _ x<m'))
     (sin⟨⟩-strictMonotone m' m
       m'∈
       m∈ m'<m))
      (sin-Monotone _ _ (ointervalℙ⊆intervalℙ _ _ m m∈) y∈
      (<ᵣWeaken≤ᵣ _ _ m<y))





