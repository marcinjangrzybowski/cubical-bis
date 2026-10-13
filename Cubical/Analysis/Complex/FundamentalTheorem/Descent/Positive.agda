module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.FinData using (zero)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Expansion
open import Cubical.Analysis.Complex.Polynomial.Expansion.Bounds
open import Cubical.Analysis.Complex.Polynomial.Cancellation
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteSum
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Dominance
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Constants
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Factor
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.ErrorControl
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.PolynomialScale
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Absorption

-- All choices here are finite and remain inside propositional truncation.
positiveConstantDescent : ∀ {n} (p : MonicPolynomial (suc n)) →
  0ℝ <ℝ modulusℂ (monicCoefficient p zero) →
  ∥ Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ
      descentContraction n · modulusℂ (monicCoefficient p zero) ∥₁
positiveConstantDescent {n} p constant-positive = PT.rec squash₁
  (λ (ε , error-control) → PT.rec squash₁ (atScale ε error-control)
    (polynomialRemainderScale p target target-positive ε))
  (chooseDescentError n A constant-positive)
  where
  A = modulusℂ (monicCoefficient p zero)
  target = descentHalf · A
  bound = descentSelectedFactor n · target
  target-positive = mulPositive descentHalf A descentHalf-positive constant-positive
  bound-positive = mulPositive (descentSelectedFactor n) target (descentSelectedFactor-positive n) target-positive

  atScale : ∀ ε → DescentError n A ε → PolynomialRemainderScale p target ε →
    ∥ Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ descentContraction n · A ∥₁
  atScale ε (error-target , error-bound , error-remainder)
      (r , radius-positive , k , selected-lower , selected-upper , remainder-bound) =
    PT.map finish (cancelSelectedTerm p r k (<ℝ-weaken 0ℝ r radius-positive) constant-positive selected-positive)
    where
    selected = nonconstantWeight p r k
    remainder = sumOtherRealTerms (nonconstantWeight p r) k
    error = realNatural (suc n) · degreeErrorAllowance n ε

    selected-above : descentHalf · bound <ℝ selected
    selected-above = halfBoundFromSlack bound selected (rat (fst ε)) error-bound selected-lower

    selected-positive : 0ℝ <ℝ selected
    selected-positive = <ℝ-trans 0ℝ (descentHalf · bound) selected
      (mulPositive descentHalf bound descentHalf-positive bound-positive) selected-above

    selected-below : selected <ℝ A
    selected-below = selectedBelowConstant A selected (rat (fst ε)) error-target selected-upper

    remainder-small : remainder <ℝ descentHalf · selected
    remainder-small = remainderBelowHalf bound selected remainder error selected-above error-remainder remainder-bound

    finish : SelectedTermCancellation p r k →
      Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ descentContraction n · A
    finish (z , radius , cancellation) = z ,
      subst (modulusℂ (evaluateMonic p z) <ℝ_) (descentContraction-scale n A)
        (absorbedCancellationBound A bound selected remainder (modulusℂ (evaluateMonic p z))
          selected-below selected-above remainder-small value-bound)
      where
      value-bound : modulusℂ (evaluateMonic p z) ≤ℝ absℝ (A - selected) + remainder
      value-bound = subst (modulusℂ (evaluateMonic p z) ≤ℝ_)
        (cong₂ _+_ cancellation (cong (λ radius → sumOtherRealTerms (nonconstantWeight p radius) k) radius))
        (evaluateMonic-selectedBound p z k)
