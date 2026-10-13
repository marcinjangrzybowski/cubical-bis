module Cubical.Analysis.Complex.Roots.FromPolar where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Functions.Roots.Positive
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polar.Cis

private
  degree-positive : ∀ n → 0ℝ <ℝ realNatural (suc n)
  degree-positive n = subst2 _<ℝ_ (addIdL 0ℝ) (sym (realNatural-suc n))
    (≤<ℝ-add 0ℝ (realNatural n) 0ℝ 1ℝ (realNatural-nonnegative n)
      (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt)))

  reciprocalDegree : ℕ → ℝ
  reciprocalDegree n = positiveReciprocal (realNatural (suc n)) (degree-positive n)

  rootAngle : ℕ → ℝ → ℝ
  rootAngle n θ = reciprocalDegree n · θ

  multiply-rootAngle : ∀ n θ → realNatural (suc n) · rootAngle n θ ≡ θ
  multiply-rootAngle n θ = mulAssoc (realNatural (suc n)) (reciprocalDegree n) θ
    ∙ cong (_· θ) (positiveReciprocalLaw (realNatural (suc n)) (degree-positive n)) ∙ mulIdL θ

opaque
  unitRootℂ : ℕ → ℝ → ℂ
  unitRootℂ n θ = cisℝ (rootAngle n θ)

  unitRootℂ-power : ∀ n θ → unitRootℂ n θ ^ℂ suc n ≡ cisℝ θ
  unitRootℂ-power n θ = cisℝ-naturalPower (rootAngle n θ) (suc n)
    ∙ cong cisℝ (multiply-rootAngle n θ)

  unitRootℂ-modulus : ∀ n θ → modulusℂ (unitRootℂ n θ) ≡ 1ℝ
  unitRootℂ-modulus n θ = modulusℂ-cisℝ (rootAngle n θ)

opaque
  polarRootℂ : (n : ℕ) (radius : ℝ) → 0ℝ <ℝ radius → ℝ → ℂ
  polarRootℂ n radius positive θ = polarℂ (positiveRootℝ n radius positive) (rootAngle n θ)

  polarRootℂ-power : ∀ n radius positive θ →
    polarRootℂ n radius positive θ ^ℂ suc n ≡ polarℂ radius θ
  polarRootℂ-power n radius positive θ =
    polarℂ-naturalPower (positiveRootℝ n radius positive) (rootAngle n θ) (suc n)
      ∙ cong₂ polarℂ (positiveRootℝ-power n radius positive) (multiply-rootAngle n θ)
