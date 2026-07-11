module Cubical.HITs.CauchyReals.ArcSin.Positive.Continuity where

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
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Core
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties

IntegralNonNeg : ∀ a b → a ≤ᵣ b → ∀ f s →  on[ a , b ]IntegralOf f is s →
               (∀ x ≤x x≤ → 0 ≤ᵣ f x ≤x x≤ ) → 0 ≤ᵣ s
IntegralNonNeg a b a≤b f _ s∫ 0≤f =
 isTrans≡≤ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
  (Integral-≤ a b a≤b (λ _ _ _ → 0) _ _ _
  0≤f (IntegralConstℙ a b a≤b  0) s∫)


arcSinDiff-Help : ∀ U → 0 ≤ᵣ U → U <ᵣ 1 → Σ[ L ∈ ℝ₊ ]
 (∀ u u' u∈ u'∈ →  u ≤ᵣ U → u' ≤ᵣ U
               →  absᵣ (arcSin u u∈ -ᵣ arcSin u' u'∈) ≤ᵣ

                  absᵣ (u -ᵣ u') ·ᵣ fst L )
arcSinDiff-Help U 0≤U U<1 =
   2 ₊·ᵣ L , w

 where

  U∈ = (0≤U , U<1)

  L : ℝ₊
  L = arcSin'₊ U U∈


  w : _
  w u u' u∈@(0≤u , u<1) u'∈@(0≤u' , u'<1) u≤U u'≤U =
   isTrans≤ᵣ _ _ _
   (isTrans≡≤ᵣ _ _ _
    (cong absᵣ (cong₂ _-ᵣ_ h h' ∙ ℝ!))
      (isTrans≤≡ᵣ _ _ _
        (absᵣ-triangle _ _)
        (cong₂ _+ᵣ_ (absᵣNonNeg _
           (IntegralNonNeg _ _ (min≤ᵣ u u') _ _ (snd u∫ )
            λ x ≤x x< →
              <ᵣWeaken≤ᵣ _ _ (snd (arcSin'₊ _ (_ , isTrans≤<ᵣ _ _ _ x< _)))))
         (sym (-absᵣ _)  ∙ absᵣNonNeg _
           ((IntegralNonNeg _ _ (min≤ᵣ' u u') _ _ (snd u'∫)
             λ x ≤x x< →
              <ᵣWeaken≤ᵣ _ _ (snd (arcSin'₊ _ (_ , isTrans≤<ᵣ _ _ _ x< _)))))))))
    (isTrans≤ᵣ _ _ _
      (≤ᵣMonotone+ᵣ _ _ _ _
        (Integral-≤ _ _ (min≤ᵣ u u') _ _ _ _
          (λ x ≤x x≤ →
            arcSin'-Monotone _ _ _ U∈
              (isTrans≤ᵣ _ _ _ x≤ (u≤U)) )
          (snd u∫) (IntegralConstℙ _ _ (min≤ᵣ u u') (fst L)))
        (Integral-≤ _ _ (min≤ᵣ' u u') _ _ _ _
          (λ x ≤x x≤ →
            arcSin'-Monotone _ _ _ U∈
               (isTrans≤ᵣ _ _ _ x≤ u'≤U))
          (snd u'∫) (IntegralConstℙ _ _ (min≤ᵣ' u u') (fst L))))
      (isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _
        (sym (·DistL+ _ _ _) ∙ ·ᵣComm _ _ )

        (≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd L))
         (isTrans≤≡ᵣ _ _ _
           (≤ᵣMonotone+ᵣ _ _ _ _
             (≤ᵣ-+o _ _ _ (≤maxᵣ u u'))
             (≤ᵣ-+o _ _ _ (isTrans≤≡ᵣ _ _ _ (≤maxᵣ u' u) (maxᵣComm u' u))))
           (x+x≡2x _ ∙ (·ᵣComm _ _ ))))
         ) (sym (·ᵣAssoc _ 2 (fst L)) ∙ cong₂ _·ᵣ_ (sym (absᵣNonNeg _
         (fst (x≤y≃0≤y-x _ _)
         (isTrans≤ᵣ _ _ _ (min≤ᵣ u u' ) (≤maxᵣ u u'))))
         ∙ absᵣ-min-max u u') refl) ) )
    where


       u⊓u' : ℝ₀₊
       u⊓u' = minᵣ₀₊ (_ ,  0≤u) (_ , 0≤u')

       u⊓u'∈ : fst u⊓u' ∈ pred≤< 0 1
       u⊓u'∈ = snd u⊓u' , isTrans≤<ᵣ _ _ _ (min≤ᵣ _ _) u<1

       u∫ = (PT.rec
                  (IntegratedℙPropℙ _ _ (min≤ᵣ u u') _)
                   ((Integrate-UContinuousℙ
                   (fst u⊓u')
                   u
                   (min≤ᵣ u u')
                   (λ x' x'∈ → arcSin' _ _))
                   ∘ IsUContinuousℙ-restr (intervalℙ 0 u)
                      (intervalℙ _ _) _
                      λ x → map-fst (isTrans≤ᵣ _ _ _ (snd u⊓u') ))
                   ((arcSin'-UC u u∈)))

       u'∫ = (PT.rec
                  (IntegratedℙPropℙ _ _ (min≤ᵣ' u u') _)
                   ((Integrate-UContinuousℙ
                   (fst u⊓u')
                   u'
                   (min≤ᵣ' u u')
                   (λ x' x'∈ → arcSin' _ _))
                   ∘ IsUContinuousℙ-restr (intervalℙ 0 u')
                      (intervalℙ _ _) _
                      λ x → map-fst (isTrans≤ᵣ _ _ _ (snd u⊓u') ))
                   ((arcSin'-UC u' u'∈)))

       h : _
       h = sym (Integral-additive* (pred≤< 0 1)
               0 (fst u⊓u') u (snd u⊓u') (min≤ᵣ u u') arcSin'
               (snd (arcSinDef _ u⊓u'∈))
                (snd u∫)
                (snd (arcSinDef _ _)))


       h' : _
       h' = sym (Integral-additive* (pred≤< 0 1)
               0 (fst u⊓u') u' (snd u⊓u') (min≤ᵣ' u u') arcSin'
               (snd (arcSinDef _ u⊓u'∈))
                (snd u'∫)
                (snd (arcSinDef _ _)))

IsContinuousWithPredArcSin : IsContinuousWithPred (pred≤< 0 1) arcSin
IsContinuousWithPredArcSin u ε u∈@(0≤u , u<1) = do
  let (b , u<b , b<1) = denseℝ _ _ u<1
  (η , 0<η , η<b-u) ← denseℚinℝ _ _ (x<y→0<y-x _ _ u<b)
  let L , ≤L = arcSinDiff-Help b
            (isTrans≤ᵣ _ _ _ 0≤u (<ᵣWeaken≤ᵣ _ _ u<b)) b<1
  (υ , L<υ) ← ∃ℚ₊LargerThanℝ₊ L
  let η₊ = η , ℚ<→0< η (<ᵣ→<ℚ 0 η 0<η)
      δ = min₊ η₊ (invℚ₊ υ ·₊ ε)
  ∣ δ , (λ v v∈ u∼v →
      invEq (∼≃abs<ε _ _ _)
       let z = fst (∼≃abs<ε _ _ _) u∼v
           zz = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) (isTrans<≤ᵣ _ _ _ z
                 (≤ℚ→≤ᵣ _ _ (ℚ.min≤ η _))))
       in isTrans≤<ᵣ _ _ _  (≤L u v u∈ v∈ (<ᵣWeaken≤ᵣ _ _ u<b)
                       (<ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ _ _ _
                         (a-b<c⇒a<c+b _ _ _ zz)
                         (a<b-c⇒a+c<b _ _ _ η<b-u))))
           (isTrans<≡ᵣ _ _ _
             (<ᵣ₊Monotone·ᵣ _ _ _ _
               (0≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (snd L))
               (isTrans<≤ᵣ _ _ _
                 z
                 (≤ℚ→≤ᵣ _ _ (ℚ.min≤' η _))) L<υ)

                  ((·ᵣComm _ _ ∙ sym (rat·ᵣrat _ _) ∙
                 cong rat (ℚ.y·[x/y] υ _))))) ∣₁
