module Cubical.HITs.CauchyReals.Analysis.Metric.Premetric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport using (substEquiv; subst2Equiv)

open import Cubical.Data.Nat as ℕ using (zero; suc)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Unit using (tt)

open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Algebra.ArchimedeanRing.Base using (ArchimedeanRingStr)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Data.Rationals.Inverse using (invℚ₊-fromNat)
open import Cubical.Relation.Premetric.Base using (PremetricSpace; PremetricStr)
open import Cubical.Relation.Premetric.Mappings using (UC[_,_])
open import Cubical.Relation.Premetric.Instances.ArchimedeanRing
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base using
  (intervalℙ; ℚ₊→ℝ₊; _<ᵣ_; _-ᵣ_; absᵣ; ∼≃abs<ε)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base using (abs-max)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication using (_·ᵣ_; rat·ᵣrat)
open import Cubical.HITs.CauchyReals.Algebra.Inverse using
  (invℝ₊; invℝ₊-rat; z<x/y₊≃y₊·z<x)
open import Cubical.HITs.CauchyReals.Algebra.Order.Archimedean

open ℚ using (_⁻¹₊)


private
  module ℝA = ArchimedeanRingStr (snd ℝArchimedeanRing)


ℝPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
fst ℝPremetricSpace = ℝ
snd ℝPremetricSpace =
  snd (ArchimedeanRing→PremetricSpace ℝArchimedeanRing)


infix 4 _≈ℝ[_]_

_≈ℝ[_]_ : ℝ → ℚ₊ → ℝ → Type
_≈ℝ[_]_ = PremetricStr._≈[_]_ (snd ℝPremetricSpace)


private
  positiveFraction : ℕ.ℕ → ℕ.ℕ → ℚ₊
  positiveFraction a b =
    [ pos (suc a) / 1+ b ] , ℚ.pos<pos tt

  positiveNat : ℕ.ℕ → ℚ₊
  positiveNat n =
    [ pos (suc n) / 1+ zero ] , ℚ.pos<pos tt

  positiveFractionPath : ∀ a b →
    fst (ℚ₊→ℝ₊ (positiveNat a)) ·ᵣ
      fst (invℝ₊ (ℚ₊→ℝ₊ (positiveNat b)))
      ≡ rat (fst (positiveFraction a b))
  positiveFractionPath a b =
    cong (fst (ℚ₊→ℝ₊ (positiveNat a)) ·ᵣ_)
      (invℝ₊-rat (positiveNat b))
    ∙ sym (rat·ᵣrat (fst (positiveNat a))
        (fst ((positiveNat b) ⁻¹₊)))
    ∙ cong rat
        (cong (fst (positiveNat a) ℚ.·_) (invℚ₊-fromNat b) ∙ ℚ!)


onPositiveFraction≈ℝ≃∼ : ∀ x y a b →
  (x ≈ℝ[ positiveFraction a b ] y) ≃
    (x ∼[ positiveFraction a b ] y)
onPositiveFraction≈ℝ≃∼ x y a b =
  onPositiveFraction≈₊R ℝArchimedeanRing x y a b
  ∙ₑ subst2Equiv _<ᵣ_
      (cong₂ _·ᵣ_
        (ι-pos≡fromNatℝ (suc b))
        (sym (abs-max (x -ᵣ y))))
      (ι-pos≡fromNatℝ (suc a))
  ∙ₑ invEquiv
      (z<x/y₊≃y₊·z<x
        (fst (ℚ₊→ℝ₊ (positiveNat a)))
        (absᵣ (x -ᵣ y))
        (ℚ₊→ℝ₊ (positiveNat b)))
  ∙ₑ substEquiv (absᵣ (x -ᵣ y) <ᵣ_)
      (positiveFractionPath a b)
  ∙ₑ invEquiv (∼≃abs<ε x y (positiveFraction a b))


opaque
  ≈ℝ→∼ : ∀ x y ε → x ≈ℝ[ ε ] y → x ∼[ ε ] y
  ≈ℝ→∼ x y = uncurry $
    SQ.elimProp
      (λ q → isPropΠ2 λ 0<q _ → isProp∼ x (q , 0<q) y)
      λ { (pos (suc a) , 1+ b) (ℚ.pos<pos _) →
        fst (onPositiveFraction≈ℝ≃∼ x y a b) }


  ∼→≈ℝ : ∀ x y ε → x ∼[ ε ] y → x ≈ℝ[ ε ] y
  ∼→≈ℝ x y = uncurry $
    SQ.elimProp
      (λ q → isPropΠ2 λ 0<q _ →
        isProp≈₊R ℝArchimedeanRing x y (q , 0<q))
      λ { (pos (suc a) , 1+ b) (ℚ.pos<pos _) →
        invEq (onPositiveFraction≈ℝ≃∼ x y a b) }


≈ℝ≃∼ : ∀ x y ε → (x ≈ℝ[ ε ] y) ≃ (x ∼[ ε ] y)
≈ℝ≃∼ x y ε =
  propBiimpl→Equiv
    (isProp≈₊R ℝArchimedeanRing x y ε)
    (isProp∼ x ε y)
    (≈ℝ→∼ x y ε)
    (∼→≈ℝ x y ε)


ClosedIntervalPremetricSpace : ℝ → ℝ → PremetricSpace ℓ-zero ℓ-zero
fst (ClosedIntervalPremetricSpace a b) = Σ ℝ (_∈ intervalℙ a b)
snd (ClosedIntervalPremetricSpace a b) =
  PremetricSubspaceStr (intervalℙ a b) (snd ℝPremetricSpace)


UnitIntervalPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
UnitIntervalPremetricSpace = ClosedIntervalPremetricSpace ℝA.0r ℝA.1r


closedIntervalInclusionUC : ∀ a b →
  UC[ ClosedIntervalPremetricSpace a b , ℝPremetricSpace ]
closedIntervalInclusionUC a b =
  subspaceInclusionUC ℝPremetricSpace (intervalℙ a b)
