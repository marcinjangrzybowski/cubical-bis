module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Rationals.Base using (ℚ)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


private
  module ℚStr = CommRingStr (snd ℚCommRing)

  zeroℝ : Real.ℝ
  zeroℝ = CommRingStr.0r (snd ℝCommRing)


-- Coefficients are stored in increasing degree order.  Horner evaluation
-- avoids constructing a list of powers or choosing any auxiliary data.

evaluatePolynomial : List Real.ℝ → Real.ℝ → Real.ℝ
evaluatePolynomial [] x = zeroℝ
evaluatePolynomial (a ∷ coefficients) x =
  a Add.+ (x Mul.· evaluatePolynomial coefficients x)


evaluatePolynomialℚ : List ℚ → ℚ → ℚ
evaluatePolynomialℚ [] x = ℚStr.0r
evaluatePolynomialℚ (a ∷ coefficients) x =
  ℚStr._+_ a
    (ℚStr._·_ x (evaluatePolynomialℚ coefficients x))


evaluatePolynomial-ι : ∀ coefficients x →
  evaluatePolynomial (map Real.ιℚ coefficients) (Real.ιℚ x) ≡
  Real.ιℚ (evaluatePolynomialℚ coefficients x)
evaluatePolynomial-ι [] x = refl
evaluatePolynomial-ι (a ∷ coefficients) x =
  cong
    (λ tail → Real.ιℚ a Add.+ (Real.ιℚ x Mul.· tail))
    (evaluatePolynomial-ι coefficients x)
  ∙ cong (Real.ιℚ a Add.+_)
      (Mul.mul-ι-ι x (evaluatePolynomialℚ coefficients x))
  ∙ Add.add-ι-ι
      a (ℚStr._·_ x (evaluatePolynomialℚ coefficients x))
