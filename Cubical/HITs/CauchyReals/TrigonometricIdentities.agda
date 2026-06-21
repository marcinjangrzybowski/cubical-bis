{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.TrigonometricIdentities where

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
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot





0<sin[π/2] : 0 <ᵣ sin π-number/2
0<sin[π/2] = isTrans<≤ᵣ _ _ _ 0<sin1
  (invEq (x≤y≃0≤y-x _ _)
  (Integral'-≤ 1 π-number/2 (<ᵣWeaken≤ᵣ _ _ 1<π-number/2) _ _ _ _
      (λ x → x≤π/2→0≤cos[x] x ∘ map-fst (isTrans≤ᵣ _ _ _ (decℚ≤ᵣ? {0} {1})))
      (Integral'Const0  1 π-number/2 (<ᵣWeaken≤ᵣ _ _ 1<π-number/2))
      (∫cos 1 π-number/2 (<ᵣWeaken≤ᵣ _ _ 1<π-number/2))))


sin[π/2]≡1 : sin π-number/2 ≡ 1
sin[π/2]≡1 =
 let z = sym (𝐑'.+IdR' _ _ (𝐑'.0RightAnnihilates' _ _ cos[π/2]≡0))
        ∙ sin²+cos²=1 π-number/2
 in cong fst (invEq (congEquiv {x = _ , 0<sin[π/2]}
            {1} (_ , (isEquiv-₊^ⁿ 2)))
      (ℝ₊≡ (z ∙ sym (·IdL _) ∙ sym (·IdR _)) ))

sin[x+π/2]=cos[x] : ∀ x → sin (x +ᵣ π-number/2) ≡ cos x
sin[x+π/2]=cos[x] x = (sinOfSum x π-number/2)
   ∙∙ (𝐑'.+IdL' _ _ (𝐑'.0RightAnnihilates' _ _ cos[π/2]≡0 ))
   ∙∙ (𝐑'.·IdR' _ _ sin[π/2]≡1)

cos[x+π/2]=-sin[x] : ∀ x → cos (x +ᵣ π-number/2) ≡ -ᵣ sin x
cos[x+π/2]=-sin[x] x = cosOfSum x π-number/2 ∙
  𝐑'.+IdL' _ _ (𝐑'.0RightAnnihilates' _ _ cos[π/2]≡0)
   ∙ cong -ᵣ_ (𝐑'.·IdR' _ _ sin[π/2]≡1)

cos[x]=-sin[x-π/2] : ∀ x → cos x ≡ -ᵣ sin (x -ᵣ π-number/2)
cos[x]=-sin[x-π/2] x =
     cong cos (sym (𝐑'.minusPlus _ _))
   ∙ cos[x+π/2]=-sin[x] (x -ᵣ π-number/2)



cos[x]=-cos[x+π] : ∀ x → cos (x +ᵣ π-number) ≡ -ᵣ cos x
cos[x]=-cos[x+π] x = cong cos
   (cong (x +ᵣ_) (sym (x+x≡2x π-number/2)) ∙ +ᵣAssoc _ _ _ )
    ∙ cos[x+π/2]=-sin[x] _ ∙
     cong -ᵣ_ (sin[x+π/2]=cos[x] x)

sin[x]=-sin[x+π] : ∀ x → sin (x +ᵣ π-number) ≡ -ᵣ sin x
sin[x]=-sin[x+π] x =
  (sym (-ᵣInvol _) ∙ sym (cong  -ᵣ_ (cong cos
    (  sym (+ᵣAssoc _ _ _)
    ∙∙ cong (x +ᵣ_) (+ᵣComm _ _)
    ∙∙ +ᵣAssoc _ _ _)
   ∙ cos[x+π/2]=-sin[x] (x +ᵣ π-number))))
    ∙ cong -ᵣ_ (cos[x]=-cos[x+π] (x +ᵣ π-number/2))
    ∙ -ᵣInvol _ ∙ cos[x+π/2]=-sin[x] x


sin-period : ∀ x → sin (x +ᵣ 2 ·ᵣ π-number) ≡ sin x
sin-period x =
  cong sin (cong (x +ᵣ_) (sym (x+x≡2x _))
     ∙ +ᵣAssoc _ _ _) ∙∙  (sin[x]=-sin[x+π] (x +ᵣ π-number)) ∙∙
    (cong -ᵣ_ (sin[x]=-sin[x+π] x) ∙ -ᵣInvol _)

cos-period : ∀ x → cos (x +ᵣ 2 ·ᵣ π-number) ≡ cos x
cos-period x =
  cong cos (cong (x +ᵣ_) (sym (x+x≡2x _))
     ∙ +ᵣAssoc _ _ _) ∙∙  (cos[x]=-cos[x+π] (x +ᵣ π-number)) ∙∙
    (cong -ᵣ_ (cos[x]=-cos[x+π] x) ∙ -ᵣInvol _)


injFromNatℚ : ∀ k k' → [ k / 1 ] ≡ [ k' / 1 ] → k ≡ k'
injFromNatℚ k k' p = sym (ℤ.·IdR _) ∙∙ ℚ.eq/⁻¹ _ _ p ∙∙ ℤ.·IdR _

cos[2φ]=cos²[φ]-sin²[φ] : ∀ φ → cos (2 ·ᵣ φ) ≡  (cos φ) ^ⁿ 2 -ᵣ  (sin φ) ^ⁿ 2
cos[2φ]=cos²[φ]-sin²[φ] φ = cong cos (sym (x+x≡2x φ)) ∙
  cosOfSum _ _ ∙ cong₂ _-ᵣ_ (cong₂ _·ᵣ_ (sym (·IdL _)) refl)
    (cong₂ _·ᵣ_ (sym (·IdL _)) refl)

cos[2φ]=1-2sin²[φ] : ∀ φ → cos (2 ·ᵣ φ) ≡ 1 -ᵣ 2 ·ᵣ (sin φ) ^ⁿ 2
cos[2φ]=1-2sin²[φ] φ = cos[2φ]=cos²[φ]-sin²[φ] φ ∙
 (sym L𝐑.lem--081) ∙ cong₂ _-ᵣ_ (sin²+cos²=1 φ) (x+x≡2x _)

cos[2φ]=2cos²[φ]-1 : ∀ φ → cos (2 ·ᵣ φ) ≡ 2 ·ᵣ (cos φ) ^ⁿ 2 -ᵣ 1
cos[2φ]=2cos²[φ]-1 φ = cos[2φ]=cos²[φ]-sin²[φ] φ ∙
  sym L𝐑.lem--081 ∙ cong₂ _-ᵣ_  (x+x≡2x _) (+ᵣComm _ _ ∙ sin²+cos²=1 φ)

