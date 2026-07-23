module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition
open import Cubical.HITs.CauchyReals.Complex.Inverse.Cancellation
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Zero

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


DifferenceQuotient : (ℂ → ℂ) → ℂ → (h : ℂ) → 0ℂ #ℂ h → ℂ
DifferenceQuotient f z h 0#h =
  (f (z +ℂ h) -ℂ f z) ／ℂ[ h , 0#h ]


HasComplexDerivativeAt : (ℂ → ℂ) → ℂ → ℂ → Type₀
HasComplexDerivativeAt f derivative z =
  (ε : ℚ₊) →
  Σ[ δ ∈ ℚ₊ ]
    ((h : ℂ) → (0#h : 0ℂ #ℂ h) →
      modulus h <ᵣ rat (fst δ) →
      modulus (DifferenceQuotient f z h 0#h -ℂ derivative)
        <ᵣ rat (fst ε))


ComplexDifferentiableAt : (ℂ → ℂ) → ℂ → Type₀
ComplexDifferentiableAt f z =
  Σ[ derivative ∈ ℂ ] HasComplexDerivativeAt f derivative z


Holomorphic : (ℂ → ℂ) → Type₀
Holomorphic f = (z : ℂ) → ComplexDifferentiableAt f z


modulus0<rat : ∀ ε → modulus 0ℂ <ᵣ rat (fst ε)
modulus0<rat ε = subst (_<ᵣ rat (fst ε)) (sym modulus0)
  (<ℚ→<ᵣ 0 (fst ε) (snd ε))


exactDifferenceQuotient→HasComplexDerivativeAt :
  ∀ f derivative z →
  ((h : ℂ) → (0#h : 0ℂ #ℂ h) →
    DifferenceQuotient f z h 0#h ≡ derivative) →
  HasComplexDerivativeAt f derivative z
exactDifferenceQuotient→HasComplexDerivativeAt f derivative z exact ε =
  ε , λ h 0#h _ →
    subst (_<ᵣ rat (fst ε))
      (sym (cong modulus
        (cong (_-ℂ derivative) (exact h 0#h) ∙ +ℂInvR derivative)))
      (modulus0<rat ε)


affineℂ : ℂ → ℂ → ℂ → ℂ
affineℂ a b z = a ·ℂ z +ℂ b


affineDifferenceQuotient : ∀ a b z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (affineℂ a b) z h 0#h ≡ a
affineDifferenceQuotient a b z h 0#h =
  cong (_／ℂ[ h , 0#h ]) (ℂ≡ ℝ! ℝ!)
  ∙ [x·y]/yℂ a h 0#h


affineHasDerivative : ∀ a b z →
  HasComplexDerivativeAt (affineℂ a b) a z
affineHasDerivative a b z =
  exactDifferenceQuotient→HasComplexDerivativeAt
    (affineℂ a b) a z (affineDifferenceQuotient a b z)


affineHolomorphic : ∀ a b → Holomorphic (affineℂ a b)
affineHolomorphic a b z = a , affineHasDerivative a b z


opaque
  affineIdentity : affineℂ 1ℂ 0ℂ ≡ (λ w → w)
  affineIdentity = funExt λ _ → ℂ≡ ℝ! ℝ!


identityHasDerivative : ∀ z →
  HasComplexDerivativeAt (λ w → w) 1ℂ z
identityHasDerivative z = subst
  (λ f → HasComplexDerivativeAt f 1ℂ z)
  affineIdentity (affineHasDerivative 1ℂ 0ℂ z)


opaque
  affineConstant : ∀ c → affineℂ 0ℂ c ≡ (λ _ → c)
  affineConstant c = funExt λ _ → ℂ≡ ℝ! ℝ!


constantHasDerivative : ∀ c z →
  HasComplexDerivativeAt (λ _ → c) 0ℂ z
constantHasDerivative c z = subst
  (λ f → HasComplexDerivativeAt f 0ℂ z)
  (affineConstant c) (affineHasDerivative 0ℂ c z)


squareℂ : ℂ → ℂ
squareℂ z = z ·ℂ z


squareDifference : ∀ z h →
  squareℂ (z +ℂ h) -ℂ squareℂ z ≡
  ((z +ℂ z) +ℂ h) ·ℂ h
squareDifference _ _ = ℂ≡ ℝ! ℝ!


squareDifferenceQuotient : ∀ z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient squareℂ z h 0#h ≡ (z +ℂ z) +ℂ h
squareDifferenceQuotient z h 0#h =
  cong (_／ℂ[ h , 0#h ]) (squareDifference z h)
  ∙ [x·y]/yℂ ((z +ℂ z) +ℂ h) h 0#h


squareRemainder : ∀ z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient squareℂ z h 0#h -ℂ (z +ℂ z) ≡ h
squareRemainder z h 0#h =
  cong (_-ℂ (z +ℂ z)) (squareDifferenceQuotient z h 0#h)
  ∙ ℂ≡ ℝ! ℝ!


squareHasDerivative : ∀ z →
  HasComplexDerivativeAt squareℂ (z +ℂ z) z
squareHasDerivative z ε =
  ε , λ h 0#h |h|<ε →
    subst (_<ᵣ rat (fst ε))
      (sym (cong modulus (squareRemainder z h 0#h))) |h|<ε


squareHolomorphic : Holomorphic squareℂ
squareHolomorphic z = (z +ℂ z) , squareHasDerivative z
