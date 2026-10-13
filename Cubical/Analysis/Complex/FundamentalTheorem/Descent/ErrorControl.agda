module Cubical.Analysis.Complex.FundamentalTheorem.Descent.ErrorControl where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.DegreeShrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.ErrorAllowance
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Dominance
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Constants
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Factor
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.SmallError

private
  degree-positive : ∀ n → 0ℝ <ℝ realNatural (suc n)
  degree-positive n = subst2 _<ℝ_ (addIdL 0ℝ) (sym (realNatural-suc n))
    (≤<ℝ-add 0ℝ (realNatural n) 0ℝ 1ℝ (realNatural-nonnegative n) (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt)))

  reciprocalFactor : ℕ → ℝ
  reciprocalFactor n = positiveReciprocal (powℝ (degreeShrink n) (suc n))
    (powPositive (degreeShrink n) (suc n) (degreeShrink-positive n))

opaque
  degreeErrorCoefficient : ℕ → ℝ
  degreeErrorCoefficient n = realNatural (suc n) · reciprocalFactor n

  degreeErrorCoefficient-positive : ∀ n → 0ℝ <ℝ degreeErrorCoefficient n
  degreeErrorCoefficient-positive n = mulPositive (realNatural (suc n)) (reciprocalFactor n) (degree-positive n)
    (positiveReciprocalPositive (powℝ (degreeShrink n) (suc n))
      (powPositive (degreeShrink n) (suc n) (degreeShrink-positive n)))

  degreeErrorAllowance-linear : ∀ n ε →
    realNatural (suc n) · degreeErrorAllowance n ε ≡ degreeErrorCoefficient n · rat (fst ε)
  degreeErrorAllowance-linear n ε = cong (realNatural (suc n) ·_)
    (PowerErrorAllowance.allowance-formula n (degreeShrink n) (degreeShrink-positive n) (rat (fst ε)))
    ∙ mulAssoc (realNatural (suc n)) (reciprocalFactor n) (rat (fst ε))

DescentError : ℕ → ℝ → ℚ₊ → Type₀
DescentError n A ε = (rat (fst ε) ≤ℝ target) × (rat (fst ε) ≤ℝ descentHalf · bound) ×
  (realNatural (suc n) · degreeErrorAllowance n ε ≤ℝ descentEighth · bound)
  where
  target = descentHalf · A
  bound = descentSelectedFactor n · target

chooseDescentError : ∀ n A → 0ℝ <ℝ A → ∥ Σ[ ε ∈ ℚ₊ ] DescentError n A ε ∥₁
chooseDescentError n A positive = PT.map
  (λ (ε , first , second , third) → ε , first , second ,
    subst (_≤ℝ descentEighth · bound) (sym (degreeErrorAllowance-linear n ε)) third)
  (smallPositiveRationalWithMultiple target (descentHalf · bound) (degreeErrorCoefficient n) (descentEighth · bound)
    target-positive (mulPositive descentHalf bound descentHalf-positive bound-positive)
    (degreeErrorCoefficient-positive n) (mulPositive descentEighth bound descentEighth-positive bound-positive))
  where
  target = descentHalf · A
  bound = descentSelectedFactor n · target
  target-positive = mulPositive descentHalf A descentHalf-positive positive
  bound-positive = mulPositive (descentSelectedFactor n) target (descentSelectedFactor-positive n) target-positive
