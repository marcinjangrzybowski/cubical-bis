module Cubical.Analysis.Complex.Polynomial.Cancellation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polar.Cis using (fromℝ-naturalPower)
open import Cubical.Analysis.Complex.Roots.Cancellation
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Expansion
open import Cubical.Analysis.Complex.Polynomial.Expansion.Bounds

private
  module Powers = Exponentiation ℂCommRing

  opaque
    scalePower : ∀ a r u n → a ·ℂ ((fromℝ r ·ℂ u) ^ℂ n) ≡
      (a ·ℂ fromℝ (powℝ r n)) ·ℂ (u ^ℂ n)
    scalePower a r u n = cong (a ·ℂ_)
      (Powers.^-ldist-· (fromℝ r) u n ∙ cong (_·ℂ (u ^ℂ n)) (fromℝ-naturalPower r n))
      ∙ ·ℂAssoc a (fromℝ (powℝ r n)) (u ^ℂ n)

    scaledCoefficientModulus : ∀ a r n → 0ℝ ≤ℝ r →
      modulusℂ (a ·ℂ fromℝ (powℝ r n)) ≡ modulusℂ a · powℝ r n
    scaledCoefficientModulus a r n nonnegative = modulusℂ-mul a (fromℝ (powℝ r n))
      ∙ cong (modulusℂ a ·_)
        (modulusℂ-fromℝ (powℝ r n) ∙ absOfNonnegative (powℝ r n) (powNonnegative r n nonnegative))

    scaledUnitModulus : ∀ r u → 0ℝ ≤ℝ r → modulusℂ u ≡ 1ℝ → modulusℂ (fromℝ r ·ℂ u) ≡ r
    scaledUnitModulus r u nonnegative unit = modulusℂ-mul (fromℝ r) u
      ∙ cong₂ _·_ (modulusℂ-fromℝ r ∙ absOfNonnegative r nonnegative) unit ∙ mulIdR r

scaledMonicCoefficient : ∀ {n} → MonicPolynomial (suc n) → ℝ → Fin (suc n) → ℂ
scaledMonicCoefficient p r k = monicCoefficient p (suc k) ·ℂ fromℝ (powℝ r (suc (Fin.toℕ k)))

opaque
  scaledMonicCoefficient-modulus : ∀ {n} (p : MonicPolynomial (suc n)) r k → 0ℝ ≤ℝ r →
    modulusℂ (scaledMonicCoefficient p r k) ≡ nonconstantWeight p r k
  scaledMonicCoefficient-modulus p r k nonnegative =
    scaledCoefficientModulus (monicCoefficient p (suc k)) r (suc (Fin.toℕ k)) nonnegative

  nonconstantTerm-scaledDirection : ∀ {n} (p : MonicPolynomial (suc n)) r u k →
    nonconstantTerm p (fromℝ r ·ℂ u) k ≡ scaledMonicCoefficient p r k ·ℂ (u ^ℂ suc (Fin.toℕ k))
  nonconstantTerm-scaledDirection p r u k = nonconstantTerm-formula p (fromℝ r ·ℂ u) k
    ∙ scalePower (monicCoefficient p (suc k)) r u (suc (Fin.toℕ k))

SelectedTermCancellation : ∀ {n} → MonicPolynomial (suc n) → ℝ → Fin (suc n) → Type₀
SelectedTermCancellation p r k = Σ[ z ∈ ℂ ] (modulusℂ z ≡ r) ×
  (modulusℂ (monicCoefficient p zero +ℂ nonconstantTerm p z k) ≡
    absℝ (modulusℂ (monicCoefficient p zero) - nonconstantWeight p r k))

-- The radius is preserved exactly. Only the angular direction is selected,
-- and its witness remains under propositional truncation.
cancelSelectedTerm : ∀ {n} (p : MonicPolynomial (suc n)) r k → 0ℝ ≤ℝ r →
  0ℝ <ℝ modulusℂ (monicCoefficient p zero) → 0ℝ <ℝ nonconstantWeight p r k →
  ∥ SelectedTermCancellation p r k ∥₁
cancelSelectedTerm p r k nonnegative constant-positive term-positive = PT.map fromUnit
  (oppositeCoefficientPower (Fin.toℕ k) a b constant-positive
    (subst (0ℝ <ℝ_) (sym b-modulus) term-positive))
  where
  a = monicCoefficient p zero
  b = scaledMonicCoefficient p r k
  b-modulus = scaledMonicCoefficient-modulus p r k nonnegative

  fromUnit : (Σ[ u ∈ ℂ ] (modulusℂ u ≡ 1ℝ) ×
      (modulusℂ (a +ℂ (b ·ℂ (u ^ℂ suc (Fin.toℕ k)))) ≡ absℝ (modulusℂ a - modulusℂ b))) →
    SelectedTermCancellation p r k
  fromUnit (u , unit , cancellation) = fromℝ r ·ℂ u , scaledUnitModulus r u nonnegative unit ,
    cong modulusℂ (cong (a +ℂ_) (nonconstantTerm-scaledDirection p r u k))
      ∙ cancellation ∙ cong (λ value → absℝ (modulusℂ a - value)) b-modulus
