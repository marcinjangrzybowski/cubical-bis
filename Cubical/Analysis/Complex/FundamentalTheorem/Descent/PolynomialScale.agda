module Cubical.Analysis.Complex.FundamentalTheorem.Descent.PolynomialScale where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData as Fin using (Fin; suc)
open import Cubical.Data.Vec using (Vec; lookup; FinVec→Vec; FinVec→Vec→FinVec)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Expansion
open import Cubical.Analysis.Complex.Polynomial.Expansion.Bounds
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.SelectedTerm
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.DegreeShrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Dominance
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteSum
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Remainder

PolynomialRemainderScale : ∀ {n} → MonicPolynomial (suc n) → ℝ → ℚ₊ → Type₀
PolynomialRemainderScale {n} p target ε = Σ[ r ∈ ℝ ] (0ℝ <ℝ r) ×
  (Σ[ k ∈ Fin (suc n) ]
    (selectedTermFactor n (degreeShrink n) · target <ℝ nonconstantWeight p r k + rat (fst ε)) ×
    (nonconstantWeight p r k <ℝ target + rat (fst ε)) ×
    (sumOtherRealTerms (nonconstantWeight p r) k ≤ℝ descentShrink · nonconstantWeight p r k +
      realNatural (suc n) · degreeErrorAllowance n ε))

-- The implicit leading coefficient is exactly one, so its modulus
-- supplies the positive final entry required by finite scale selection.
polynomialRemainderScale : ∀ {n} (p : MonicPolynomial (suc n)) (target : ℝ) →
  0ℝ <ℝ target → (ε : ℚ₊) → ∥ PolynomialRemainderScale p target ε ∥₁
polynomialRemainderScale {n} p target positive ε = PT.map fromScale
  (finitePowerRemainderScale coefficients nonnegative leading-positive target positive ε)
  where
  coefficients : Vec ℝ (suc n)
  coefficients = FinVec→Vec (λ i → modulusℂ (monicCoefficient p (suc i)))

  lookup-coefficient : ∀ i → lookup i coefficients ≡ modulusℂ (monicCoefficient p (suc i))
  lookup-coefficient i = funExt⁻ (FinVec→Vec→FinVec (λ j → modulusℂ (monicCoefficient p (suc j)))) i

  nonnegative : ∀ i → 0ℝ ≤ℝ lookup i coefficients
  nonnegative i = subst (0ℝ ≤ℝ_) (sym (lookup-coefficient i)) (modulusℂ-nonnegative (monicCoefficient p (suc i)))

  leading-positive : 0ℝ <ℝ lookup (Fin.fromℕ n) coefficients
  leading-positive = subst (0ℝ <ℝ_)
    (sym (lookup-coefficient (Fin.fromℕ n) ∙ cong modulusℂ (monicCoefficient-leading p) ∙ modulusℂ-one))
    (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt))

  weight-path : ∀ r i → weightedPower (lookup i coefficients) (Fin.toℕ i) r ≡ nonconstantWeight p r i
  weight-path r i = cong (λ a → weightedPower a (Fin.toℕ i) r) (lookup-coefficient i)

  fromScale : PowerRemainderScale coefficients target ε → PolynomialRemainderScale p target ε
  fromScale (r , r-positive , k , selected-lower , selected-upper , remainder) = r , r-positive , k ,
    subst (selectedTermFactor n (degreeShrink n) · target <ℝ_) (cong (_+ rat (fst ε)) (weight-path r k)) selected-lower ,
    subst (_<ℝ target + rat (fst ε)) (weight-path r k) selected-upper ,
    subst2 _≤ℝ_ (cong (λ values → sumOtherRealTerms values k) (funExt (weight-path r)))
      (cong (λ value → descentShrink · value + realNatural (suc n) · degreeErrorAllowance n ε) (weight-path r k)) remainder
