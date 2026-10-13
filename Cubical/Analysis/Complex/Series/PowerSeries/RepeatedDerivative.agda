module Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat as Nat
open import Cubical.Analysis.Real.Base using (ℝ)
import Cubical.Analysis.Real.Algebra.Negation as Real
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (mulComm)
open import Cubical.Analysis.Real.Algebra.Natural
import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference

-- Reuse the native real iteration and its natural coefficient multipliers.
-- The successor equation below identifies this coordinate definition with
-- iteration of the established complex formal derivative.
repeatedFormalDerivativeℂ : ℕ → ComplexSequence → ComplexSequence
repeatedFormalDerivativeℂ order coefficients n =
  Real.repeatedFormalDerivative order (re ∘ coefficients) n ,
  Real.repeatedFormalDerivative order (im ∘ coefficients) n

opaque
  repeatedFormalDerivativeℂ-zero : ∀ coefficients → repeatedFormalDerivativeℂ zero coefficients ≡ coefficients
  repeatedFormalDerivativeℂ-zero coefficients = refl

  repeatedFormalDerivativeℂ-successor : ∀ order coefficients →
    repeatedFormalDerivativeℂ (suc order) coefficients ≡ formalDerivativeℂ (repeatedFormalDerivativeℂ order coefficients)
  repeatedFormalDerivativeℂ-successor order coefficients = funExt λ n → sym
    (·ℂComm (fromℝ (realNatural (suc n))) (repeatedFormalDerivativeℂ order coefficients (suc n))
    ∙ complexMultiplyReal (repeatedFormalDerivativeℂ order coefficients (suc n)) (realNatural (suc n))
    ∙ ℂ≡ (mulComm (re (repeatedFormalDerivativeℂ order coefficients (suc n))) (realNatural (suc n)))
          (mulComm (im (repeatedFormalDerivativeℂ order coefficients (suc n))) (realNatural (suc n))))

  repeatedFormalDerivativeℂ-addIterations : ∀ left right coefficients →
    repeatedFormalDerivativeℂ (left Nat.+ right) coefficients ≡
      repeatedFormalDerivativeℂ left (repeatedFormalDerivativeℂ right coefficients)
  repeatedFormalDerivativeℂ-addIterations left right coefficients = funExt λ n → ℂ≡
    (funExt⁻ (Real.repeatedFormalDerivative-addIterations left right (re ∘ coefficients)) n)
    (funExt⁻ (Real.repeatedFormalDerivative-addIterations left right (im ∘ coefficients)) n)

  repeatedFormalDerivativeℂ-coefficient : ∀ order coefficients index →
    repeatedFormalDerivativeℂ order coefficients index ≡
      fromℝ (realNatural (Real.derivativeNaturalProduct index order)) ·ℂ coefficients (index Nat.+ order)
  repeatedFormalDerivativeℂ-coefficient order coefficients index = ℂ≡
    (Real.repeatedFormalDerivative-coefficient order (re ∘ coefficients) index)
    (Real.repeatedFormalDerivative-coefficient order (im ∘ coefficients) index)
    ∙ sym (·ℂComm (fromℝ multiplier) (coefficients (index Nat.+ order))
      ∙ complexMultiplyReal (coefficients (index Nat.+ order)) multiplier
      ∙ ℂ≡ (mulComm (re (coefficients (index Nat.+ order))) multiplier)
            (mulComm (im (coefficients (index Nat.+ order))) multiplier))
    where
    multiplier : ℝ
    multiplier = realNatural (Real.derivativeNaturalProduct index order)

opaque
  repeatedFormalDerivativeℂ-neg : ∀ order coefficients →
    repeatedFormalDerivativeℂ order (λ n → -ℂ coefficients n) ≡ (λ n → -ℂ repeatedFormalDerivativeℂ order coefficients n)
  repeatedFormalDerivativeℂ-neg order coefficients = funExt λ n → ℂ≡
    (funExt⁻ (Real.repeatedFormalDerivative-neg order (re ∘ coefficients)) n)
    (funExt⁻ (Real.repeatedFormalDerivative-neg order (im ∘ coefficients)) n)

  repeatedFormalDerivativeℂ-commute : ∀ order coefficients →
    repeatedFormalDerivativeℂ (suc order) coefficients ≡ repeatedFormalDerivativeℂ order (formalDerivativeℂ coefficients)
  repeatedFormalDerivativeℂ-commute order coefficients =
    cong (λ k → repeatedFormalDerivativeℂ k coefficients) (Nat.+-comm (suc zero) order)
    ∙ repeatedFormalDerivativeℂ-addIterations order (suc zero) coefficients
    ∙ cong (repeatedFormalDerivativeℂ order) (repeatedFormalDerivativeℂ-successor zero coefficients)
