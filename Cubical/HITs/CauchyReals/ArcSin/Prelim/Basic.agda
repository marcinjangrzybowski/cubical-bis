module Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic where

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
open import Cubical.Data.Rationals.Order as ℚ using ()
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using ()


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; _+₊_ ; _·₊_ ; _/2₊ ; min₊)
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0< ; rtp-1/n ; riemannSum-empty)
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Properties
open import Cubical.HITs.CauchyReals.Calculus.Integration.Uniform
open IntegrationUC rtp-1/n
open import Cubical.HITs.CauchyReals.Calculus.Derivative.MeanValue
open import Cubical.HITs.CauchyReals.Calculus.Integration.FundamentalTheorem using
  ( Integral-additive
  ; FTOC⇒*
  ; FTOC⇐''
  )
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Analysis.Uniform
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base hiding (invℚ₊ ; _ℚ₊^ⁿ_)
open import Cubical.HITs.CauchyReals.Calculus.Integration.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.Trigonometry.Identities
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.Tactics.CommRingSolver.Specialised.Reals


Integral-≤ : ∀ a b → a ≤ᵣ b → ∀ f f' s s'
            → (∀ x ≤x x≤ → f x ≤x x≤ ≤ᵣ f' x ≤x x≤)
            → on[ a , b ]IntegralOf f is s
            → on[ a , b ]IntegralOf f' is s'
            → s ≤ᵣ s'
Integral-≤ a b a≤b f f' s s' f≤f' s=∫ s'=∫ =
  Integral'-≤ a b a≤b
   _ _
   s s'
      (λ x x∈ → f≤f' _ _ _)
       (invEq (clampᵣ-IntegralOf' a b a≤b _ _) s=∫)
       (invEq (clampᵣ-IntegralOf' a b a≤b _ _) s'=∫)



Integral0ℙ : (a b : ℝ) →
             a ≤ᵣ b →
             on[ a , b ]IntegralOf (λ _ _ _ → 0) is 0
Integral0ℙ a b a≤b =
  subst (on[ a , b ]IntegralOf (λ _ _ _ → rat [ pos 0 / 1+ 0 ]) is_)
    (𝐑'.0LeftAnnihilates _) (IntegralConstℙ a b a≤b 0)

cos∘absᵣ : ∀ x → cos x ≡ cos (absᵣ x)
cos∘absᵣ = ≡Continuous _ _
  isContinuousCos
  (IsContinuous∘ _ _ isContinuousCos IsContinuousAbsᵣ)
   λ q → ⊎.rec
     (λ 0≤q → cong cos $ sym (absᵣNonNeg _ (≤ℚ→≤ᵣ _ _ 0≤q)))
     (λ q≤0 → cong cos (sym (-ᵣInvol _)) ∙
              ((cong cos $ sym (cong -ᵣ_
               ((absᵣNonNeg _ (isTrans≡≤ᵣ _ _ _
                 (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _
                  (((≤ℚ→≤ᵣ q 0 q≤0)))) )) ∙
                  refl))))
              ∙ sym (cos-even _) ∙ cong cos
               (sym (-absᵣ _)))
     (ℚ.≤cases 0 q)

∣x∣≤π/2→0≤cos[x] : ∀ x → x ∈ intervalℙ (-ᵣ π-number/2) π-number/2 → 0 ≤ᵣ cos x
∣x∣≤π/2→0≤cos[x] x x∈ =
  isTrans≤≡ᵣ _ _ _
   (x≤π/2→0≤cos[x] (absᵣ x)
     (0≤absᵣ _ , (isTrans≡≤ᵣ _ _ _  (abs-max _)
     (max≤-lem x (-ᵣ x) _ (snd x∈)
      (isTrans≤≡ᵣ _  _ _  (-ᵣ≤ᵣ _ _ (fst x∈)) (-ᵣInvol _ ))))))
   (sym (cos∘absᵣ x))

∣x∣<π/2→0<cos[x] : ∀ x → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2 → 0 <ᵣ cos x
∣x∣<π/2→0<cos[x] x x∈ =
  isTrans<≡ᵣ _ _ _
   (0≤x<π/2→0<cos[x] (absᵣ x)
     (0≤absᵣ _)
     ((isTrans≡<ᵣ _ _ _  (abs-max _)
     (max<-lem x (-ᵣ x) _ (snd x∈)
      (isTrans<≡ᵣ _  _ _  (-ᵣ<ᵣ _ _ (fst x∈)) (-ᵣInvol _ ))))))
   (sym (cos∘absᵣ x))


sin-firstQuarter-Monotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2)
      → x ≤ᵣ y → sin x ≤ᵣ sin y
sin-firstQuarter-Monotone x y x∈ y∈ x≤y =
 invEq (x≤y≃0≤y-x _ _)
   (Integral-≤ x y x≤y _ _ _ _
      (λ x' ≤x' x'≤ →
        x≤π/2→0≤cos[x] x'
          (isTrans≤ᵣ _ _ _ (fst x∈) ≤x' ,
           isTrans≤ᵣ _ _ _ x'≤ (snd y∈ ) ))
      (Integral0ℙ _ _ x≤y)
      (∫cos x y x≤y))

sin-Monotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      (y∈ : y ∈ intervalℙ (-ᵣ π-number/2) π-number/2)
      → x ≤ᵣ y → sin x ≤ᵣ sin y
sin-Monotone x y x∈ y∈ x≤y =
 invEq (x≤y≃0≤y-x _ _)
   (Integral-≤ x y x≤y _ _ _ _
      (λ x' ≤x' x'≤ →
        ∣x∣≤π/2→0≤cos[x] x'
         (isTrans≤ᵣ _ _ _ (fst x∈ ) ≤x' ,
          isTrans≤ᵣ _ _ _ x'≤ (snd y∈ )))
      (Integral0ℙ _ _ x≤y)
      (∫cos x y x≤y))



cos-firstQuarter-Monotone :
      (x y : ℝ)
      (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2)
      → x ≤ᵣ y → cos y ≤ᵣ cos x
cos-firstQuarter-Monotone x y x∈ y∈ x≤y =
  invEq (x≤y≃0≤y-x _ _)
           (Integral-≤ x y x≤y _ _ _ _
              (λ x' ≤x' x'≤ →
                isTrans≡≤ᵣ _ _ _
                  (sym sin0=0) (sin-firstQuarter-Monotone 0 x'
                   (≤ᵣ-refl 0 , <ᵣWeaken≤ᵣ _ _ 0<π-number/2)
                   (isTrans≤ᵣ _ _ _ (fst x∈) ≤x'
                   , isTrans≤ᵣ _ _ _ x'≤ (snd y∈))
                   (isTrans≤ᵣ _ _ _ (fst x∈) ≤x')))
              (Integral0ℙ _ _ x≤y)
              (∫sin x y x≤y))
