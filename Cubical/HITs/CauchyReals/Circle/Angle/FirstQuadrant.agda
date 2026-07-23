module Cubical.HITs.CauchyReals.Circle.Angle.FirstQuadrant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset


open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base using
  ( absᵣPos
  ; <ᵣ-o+
  ; -ᵣ<ᵣ
  )
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Predicate using
  (sym-intervalℙ⊆ointervalℙ)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Power.Order using (^<1)
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using (absᵣNeg)
open import Cubical.HITs.CauchyReals.Algebra.Order.Apartness using (decCut)
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base

open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  ( sin
  ; cos
  ; sin²+cos²=1
  ; sin-odd
  ; cos-even
  )
open import Cubical.HITs.CauchyReals.Trigonometry.Identities
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic using
  ( ∣x∣<π/2→0<cos[x] )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Circle.Base public
pre-distCircle→angle : ∀ x y → x ^ⁿ 2 +ᵣ y ^ⁿ 2 ≡ 1
  → absᵣ x ≤ᵣ (rat [ 3 / 4 ])
  → Σ[ φ ∈ ℝ ] ((φ ∈ ointervalℙ (-ᵣ π-number/2) π-number/2)
              ⊎ (φ ∈ ointervalℙ π-number/2 (π-number/2 +ᵣ π-number)))
      × ((sin φ ≡ x) × (cos φ ≡ y))
pre-distCircle→angle x y x²+y²=1 ∣x∣≤3/4 =
 let x∈ : x ∈ intervalℙ (-ᵣ rat [ 3 / 4 ]) (rat [ 3 / 4 ])
     x∈ = abs≤→interval x (rat [ 3 / 4 ]) ∣x∣≤3/4

     x²<1 : (x ^ⁿ 2) <ᵣ 1
     x²<1 = (isTrans≡<ᵣ _ _ _
                  (abs[x^²ⁿ] 1 x
                    ∙ absᵣ^ⁿ x 2)
                  (^<1 (absᵣ x) (0≤absᵣ x) 1
                   (isTrans≤<ᵣ _ _ _ ∣x∣≤3/4 decℚ<ᵣ?)))
     0<y² : 0 <ᵣ y ^ⁿ 2
     0<y² = <-o+-cancel _ _ _
              (isTrans<≡ᵣ _ _ _
                (isTrans≡<ᵣ _ _ _ (Rℝ.+IdR _) x²<1)
                (sym x²+y²=1))
     0<∣y∣ : 0 <ᵣ absᵣ y
     0<∣y∣ = 0<x²→0<abs[x] y 0<y²
     x∈ = (subst (λ X → x ∈
            ointervalℙ X 1)
           (-ᵣ-rat 1) (sym-intervalℙ⊆ointervalℙ _ 1 decℚ<ᵣ? x x∈))
     φ = arcSin⟨⟩ x x∈
     φ∈ = arcSin⟨⟩∈ x x∈
     sin= = sin∘arcSin⟨⟩ x _
     zz :  (cos φ ^ⁿ 2) ≡ (y ^ⁿ 2)
     zz = sym (𝐑'.plusMinus _ _) ∙
      cong (_-ᵣ (x ^ⁿ 2))
       (+ᵣComm _ _ ∙ cong (_+ᵣ (cos φ ^ⁿ 2))
        (sym (cong (_^ⁿ 2) sin=)) ∙ sin²+cos²=1 φ ∙ sym x²+y²=1
         ∙ +ᵣComm _ _)
         ∙ 𝐑'.plusMinus _ _

     cos= : cos φ ≡ absᵣ y
     cos= =
         cong fst (invEq (congEquiv
           {x = _ , ∣x∣<π/2→0<cos[x] φ (arcSin⟨⟩∈ _ x∈)}
           {_ , 0<∣y∣}
           (_ , isEquiv-₊^ⁿ 2))
              (ℝ₊≡ (zz
                  ∙ abs[x^²ⁿ] 1 y
                    ∙ absᵣ^ⁿ y 2)))
     f-inl : 0 <ᵣ y → Σ[ φ ∈ ℝ ] (φ ∈ ointervalℙ (-ᵣ π-number/2) π-number/2)
                 × ((sin φ ≡ x) × (cos φ ≡ y))
     f-inl 0<y = φ , φ∈ , sin= , cos= ∙ absᵣPos y 0<y

     f-inr : y <ᵣ 0 → Σ[ φ ∈ ℝ ]
      (φ ∈ ointervalℙ π-number/2 (π-number/2 +ᵣ π-number))
      × ((sin φ ≡ x) × (cos φ ≡ y))
     f-inr y<0 =
        π-number -ᵣ φ ,
          (isTrans≡<ᵣ _ _ _
            (sym (𝐑'.plusMinus _ _) ∙ cong₂ _+ᵣ_ (x+x≡2x _) refl)
            (<ᵣ-o+ _ _ π-number (-ᵣ<ᵣ _ _ (snd φ∈)))
          , (isTrans<≡ᵣ _ _ _
            (<ᵣ-o+ _ _ π-number (-ᵣ<ᵣ _ _ (fst φ∈)))
             (cong₂ _+ᵣ_ refl (-ᵣInvol _) ∙ +ᵣComm _ _))) ,
          cong sin (+ᵣComm _ _)
           ∙ sin[x]=-sin[x+π] (-ᵣ φ)
           ∙ sin-odd _ ∙
            cong sin (-ᵣInvol _) ∙ sin=
          , cong cos (+ᵣComm _ _)
            ∙ cos[x]=-cos[x+π] (-ᵣ φ)
            ∙ cong -ᵣ_ (
              (sym (cos-even φ) ∙ cos=)
              ∙ absᵣNeg _ y<0)
             ∙ -ᵣInvol _

 in ⊎.rec (map-snd (map-fst inl) ∘ f-inl)
          (map-snd (map-fst inr) ∘ f-inr)
     (decCut y 0<∣y∣)
