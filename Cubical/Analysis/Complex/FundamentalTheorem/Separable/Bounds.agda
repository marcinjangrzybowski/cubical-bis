module Cubical.Analysis.Complex.FundamentalTheorem.Separable.Bounds where

-- The positive algebraic certificate rules out simultaneous smallness of
-- p and p'. These estimates apply before a root is known, which is the
-- essential distinction from the inverse-at-an-exact-root bridge.

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order using (positiveReciprocalPositive)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Inverse.Bounds
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic using (BezoutSeparability)
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Certificate

opaque
  bezoutSeparability-modulusBound : ∀ {n} (p : MonicPolynomial n)
    (certificate : BezoutSeparability p) z sBound tBound →
    normℂ (evaluatePolynomialℂ (BezoutSeparability.bezoutS certificate) z) ≤ℝ sBound →
    normℂ (evaluatePolynomialℂ (BezoutSeparability.bezoutT certificate) z) ≤ℝ tBound →
    1ℝ ≤ℝ sBound · modulusℂ (evaluateMonic p z) + tBound · modulusℂ (derivativeMonic p z)
  bezoutSeparability-modulusBound p certificate z sBound tBound sb tb =
    subst (_≤ℝ sBound · modulusℂ value + tBound · modulusℂ derivative)
      (cong modulusℂ (bezoutSeparability-evaluation p certificate z) ∙ modulusℂ-one)
      (≤ℝ-trans (modulusℂ (s ·ℂ value +ℂ t ·ℂ derivative))
        (modulusℂ (s ·ℂ value) + modulusℂ (t ·ℂ derivative))
        (sBound · modulusℂ value + tBound · modulusℂ derivative)
        (modulusℂ-triangle (s ·ℂ value) (t ·ℂ derivative))
        (addPres≤ (modulusℂ (s ·ℂ value)) (sBound · modulusℂ value)
          (modulusℂ (t ·ℂ derivative)) (tBound · modulusℂ derivative)
          (subst (_≤ℝ sBound · modulusℂ value) (sym (modulusℂ-mul s value))
            (mulPres≤R-0≤ (modulusℂ s) sBound (modulusℂ value) (modulusℂ-nonnegative value)
              (≤ℝ-trans (modulusℂ s) (normℂ s) sBound (modulusℂ≤normℂ s) sb)))
          (subst (_≤ℝ tBound · modulusℂ derivative) (sym (modulusℂ-mul t derivative))
            (mulPres≤R-0≤ (modulusℂ t) tBound (modulusℂ derivative) (modulusℂ-nonnegative derivative)
              (≤ℝ-trans (modulusℂ t) (normℂ t) tBound (modulusℂ≤normℂ t) tb)))))
    where
    s t value derivative : ℂ
    s = evaluatePolynomialℂ (BezoutSeparability.bezoutS certificate) z
    t = evaluatePolynomialℂ (BezoutSeparability.bezoutT certificate) z
    value = evaluateMonic p z
    derivative = derivativeMonic p z

  -- A residual budget plus a positive gap sums to 1. In applications both
  -- are 1/2; the bound on t is enlarged by 1 to make it positive.
  bezoutSeparability-derivativeLowerBound : ∀ {n} (p : MonicPolynomial n)
    (certificate : BezoutSeparability p) z sBound tBound budget gap
    (tPositive : 0ℝ <ℝ tBound) →
    normℂ (evaluatePolynomialℂ (BezoutSeparability.bezoutS certificate) z) ≤ℝ sBound →
    normℂ (evaluatePolynomialℂ (BezoutSeparability.bezoutT certificate) z) ≤ℝ tBound →
    sBound · modulusℂ (evaluateMonic p z) ≤ℝ budget → budget + gap ≡ 1ℝ →
    gap · positiveReciprocal tBound tPositive ≤ℝ modulusℂ (derivativeMonic p z)
  bezoutSeparability-derivativeLowerBound p certificate z sBound tBound budget gap tPositive sb tb small split =
    subst (gap · reciprocal ≤ℝ_) cancel
      (mulPres≤R-0≤ gap (tBound · derivative) reciprocal
        (<ℝ-weaken 0ℝ reciprocal (positiveReciprocalPositive tBound tPositive))
        (addReflects≤L gap (tBound · derivative) budget
          (subst (_≤ℝ budget + tBound · derivative) (sym split)
            (≤ℝ-trans 1ℝ (sBound · modulusℂ (evaluateMonic p z) + tBound · derivative)
              (budget + tBound · derivative)
              (bezoutSeparability-modulusBound p certificate z sBound tBound sb tb)
              (addPres≤R (sBound · modulusℂ (evaluateMonic p z)) budget (tBound · derivative) small)))))
    where
    derivative reciprocal : ℝ
    derivative = modulusℂ (derivativeMonic p z)
    reciprocal = positiveReciprocal tBound tPositive
    cancel : (tBound · derivative) · reciprocal ≡ derivative
    cancel = cong (_· reciprocal) (mulComm tBound derivative)
      ∙ sym (mulAssoc derivative tBound reciprocal)
      ∙ cong (derivative ·_) (positiveReciprocalLaw tBound tPositive) ∙ mulIdR derivative
