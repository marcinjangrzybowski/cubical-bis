module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative


HasComplexDerivativeWithinAt :
  ComplexPredicate → (ℂ → ℂ) → ℂ → ℂ → Type₀
HasComplexDerivativeWithinAt P f derivative z =
  (ε : ℚ₊) →
  Σ[ δ ∈ ℚ₊ ]
    ((h : ℂ) → (0#h : 0ℂ #ℂ h) →
      z +ℂ h ∈ P →
      modulus h <ᵣ rat (fst δ) →
      modulus (DifferenceQuotient f z h 0#h -ℂ derivative)
        <ᵣ rat (fst ε))


ComplexDifferentiableWithinAt :
  ComplexPredicate → (ℂ → ℂ) → ℂ → Type₀
ComplexDifferentiableWithinAt P f z =
  Σ[ derivative ∈ ℂ ]
    HasComplexDerivativeWithinAt P f derivative z


HolomorphicOn : ComplexPredicate → (ℂ → ℂ) → Type₀
HolomorphicOn P f =
  (z : ℂ) → z ∈ P → ComplexDifferentiableWithinAt P f z


hasComplexDerivativeAt→Within :
  ∀ P {f derivative z} →
  HasComplexDerivativeAt f derivative z →
  HasComplexDerivativeWithinAt P f derivative z
hasComplexDerivativeAt→Within P derivativeAt ε =
  map-snd
    (λ estimate h 0#h _ h<δ →
      estimate h 0#h h<δ)
    (derivativeAt ε)


hasComplexDerivativeWithinWholeAt→At :
  ∀ {f derivative z} →
  HasComplexDerivativeWithinAt wholeℂ f derivative z →
  HasComplexDerivativeAt f derivative z
hasComplexDerivativeWithinWholeAt→At derivativeWithin ε =
  map-snd
    (λ estimate h 0#h h<δ →
      estimate h 0#h tt h<δ)
    (derivativeWithin ε)


complexDifferentiableAt→Within :
  ∀ P {f z} →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableWithinAt P f z
complexDifferentiableAt→Within P {f} {z} differentiable =
  fst differentiable ,
  hasComplexDerivativeAt→Within P
    {f = f} {derivative = fst differentiable} {z = z}
    (snd differentiable)


complexDifferentiableWithinWholeAt→At :
  ∀ {f z} →
  ComplexDifferentiableWithinAt wholeℂ f z →
  ComplexDifferentiableAt f z
complexDifferentiableWithinWholeAt→At {f} {z} differentiableWithin =
  fst differentiableWithin ,
  hasComplexDerivativeWithinWholeAt→At
    {f = f} {derivative = fst differentiableWithin} {z = z}
    (snd differentiableWithin)


holomorphic→HolomorphicOn :
  ∀ P {f} → Holomorphic f → HolomorphicOn P f
holomorphic→HolomorphicOn P {f} holomorphic z _ =
  complexDifferentiableAt→Within P {f = f} {z = z}
    (holomorphic z)


holomorphicOnWhole→Holomorphic :
  ∀ {f} → HolomorphicOn wholeℂ f → Holomorphic f
holomorphicOnWhole→Holomorphic {f} holomorphicOn z =
  complexDifferentiableWithinWholeAt→At {f = f} {z = z}
    (holomorphicOn z tt)


hasComplexDerivativeWithinAt-restrict :
  ∀ {P Q f derivative z} →
  Q ⊆ P →
  HasComplexDerivativeWithinAt P f derivative z →
  HasComplexDerivativeWithinAt Q f derivative z
hasComplexDerivativeWithinAt-restrict {P} {Q} {z = z}
  Q⊆P derivativeWithin ε =
  map-snd
    (λ estimate h 0#h z+h∈Q h<δ →
      estimate h 0#h (Q⊆P (z +ℂ h) z+h∈Q) h<δ)
    (derivativeWithin ε)


complexDifferentiableWithinAt-restrict :
  ∀ {P Q f z} →
  Q ⊆ P →
  ComplexDifferentiableWithinAt P f z →
  ComplexDifferentiableWithinAt Q f z
complexDifferentiableWithinAt-restrict
  {P} {Q} {f} {z} Q⊆P differentiableWithin =
  fst differentiableWithin ,
  hasComplexDerivativeWithinAt-restrict
    {P = P} {Q = Q} {f = f}
    {derivative = fst differentiableWithin} {z = z}
    Q⊆P (snd differentiableWithin)


holomorphicOn-restrict :
  ∀ {P Q f} → Q ⊆ P → HolomorphicOn P f → HolomorphicOn Q f
holomorphicOn-restrict {P} {Q} {f} Q⊆P holomorphicOn z z∈Q =
  complexDifferentiableWithinAt-restrict
    {P = P} {Q = Q} {f = f} {z = z} Q⊆P
    (holomorphicOn z (Q⊆P z z∈Q))


exactDifferenceQuotient→HasComplexDerivativeWithinAt :
  ∀ P f derivative z →
  ((h : ℂ) → (0#h : 0ℂ #ℂ h) →
    DifferenceQuotient f z h 0#h ≡ derivative) →
  HasComplexDerivativeWithinAt P f derivative z
exactDifferenceQuotient→HasComplexDerivativeWithinAt
  P f derivative z exact =
  hasComplexDerivativeAt→Within P
    {f = f} {derivative = derivative} {z = z}
    (exactDifferenceQuotient→HasComplexDerivativeAt
      f derivative z exact)


affineHasDerivativeWithin : ∀ P a b z →
  HasComplexDerivativeWithinAt P (affineℂ a b) a z
affineHasDerivativeWithin P a b z =
  hasComplexDerivativeAt→Within P
    {f = affineℂ a b} {derivative = a} {z = z}
    (affineHasDerivative a b z)


affineHolomorphicOn : ∀ P a b →
  HolomorphicOn P (affineℂ a b)
affineHolomorphicOn P a b =
  holomorphic→HolomorphicOn P
    {f = affineℂ a b} (affineHolomorphic a b)


identityHasDerivativeWithin : ∀ P z →
  HasComplexDerivativeWithinAt P (λ w → w) 1ℂ z
identityHasDerivativeWithin P z =
  hasComplexDerivativeAt→Within P
    {f = λ w → w} {derivative = 1ℂ} {z = z}
    (identityHasDerivative z)


identityHolomorphicOn : ∀ P →
  HolomorphicOn P (λ w → w)
identityHolomorphicOn P z _ =
  1ℂ , identityHasDerivativeWithin P z


constantHasDerivativeWithin : ∀ P c z →
  HasComplexDerivativeWithinAt P (λ _ → c) 0ℂ z
constantHasDerivativeWithin P c z =
  hasComplexDerivativeAt→Within P
    {f = λ _ → c} {derivative = 0ℂ} {z = z}
    (constantHasDerivative c z)


constantHolomorphicOn : ∀ P c →
  HolomorphicOn P (λ _ → c)
constantHolomorphicOn P c z _ =
  0ℂ , constantHasDerivativeWithin P c z


squareHasDerivativeWithin : ∀ P z →
  HasComplexDerivativeWithinAt P squareℂ (z +ℂ z) z
squareHasDerivativeWithin P z =
  hasComplexDerivativeAt→Within P
    {f = squareℂ} {derivative = z +ℂ z} {z = z}
    (squareHasDerivative z)


squareHolomorphicOn : ∀ P → HolomorphicOn P squareℂ
squareHolomorphicOn P =
  holomorphic→HolomorphicOn P
    {f = squareℂ} squareHolomorphic
