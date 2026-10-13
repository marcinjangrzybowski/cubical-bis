module Cubical.Analysis.Complex.Polynomial.Differential.Estimates where

-- Uniform estimates for the divided difference and its deviation from a
-- fixed derivative. The constants are computed from finitely many
-- coefficients and a common norm bound, independently of the center.

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Bounds
open import Cubical.Analysis.Complex.Polynomial.Differential
import Cubical.Analysis.Complex.Polynomial.Differential.DividedDifferenceAlgebra as Identities

private
  module C = Identities.DividedDifferenceIdentities ℂCommRing
  module R = Identities.DividedDifferenceIdentities ℝCommRing
  module RR = RingTheory (CommRing→Ring ℝCommRing)

  opaque
    unfolding evaluatePolynomialℂ polynomialDerivativeℂ

    quotient-cons : ∀ a p w z → evaluatePolynomialℂ (quotientPolynomialℂ (a ∷ p) w) z ≡
      evaluatePolynomialℂ p w +ℂ z ·ℂ evaluatePolynomialℂ (quotientPolynomialℂ p w) z
    quotient-cons a p w z = refl

    error-step : ∀ a p r w z →
      evaluatePolynomialℂ (quotientPolynomialℂ (a ∷ p) w) z -ℂ polynomialDerivativeℂ (a ∷ p) r ≡
      (evaluatePolynomialℂ p w -ℂ evaluatePolynomialℂ p r) +ℂ
        ((z -ℂ r) ·ℂ evaluatePolynomialℂ (quotientPolynomialℂ p w) z +ℂ
          r ·ℂ (evaluatePolynomialℂ (quotientPolynomialℂ p w) z -ℂ polynomialDerivativeℂ p r))
    error-step = C.errorStep

    error-empty : ∀ r w z →
      evaluatePolynomialℂ (quotientPolynomialℂ [] w) z -ℂ polynomialDerivativeℂ [] r ≡ 0ℂ
    error-empty r w z = +ℂInvR 0ℂ

    remainder-factor : ∀ p r z w →
      (evaluatePolynomialℂ p z -ℂ evaluatePolynomialℂ p w) -ℂ
        polynomialDerivativeℂ p r ·ℂ (z -ℂ w) ≡
      (z -ℂ w) ·ℂ (evaluatePolynomialℂ (quotientPolynomialℂ p w) z -ℂ polynomialDerivativeℂ p r)
    remainder-factor = C.remainderFactor

-- H(a + Xp, B) = 2 Lip(p,B) + B H(p,B). The two Lipschitz
-- contributions come from moving the first and second arguments.
polynomialDerivativeVariationℂ : List ℂ → ℝ → ℝ
polynomialDerivativeVariationℂ [] bound = 0ℝ
polynomialDerivativeVariationℂ (a ∷ p) bound =
  polynomialLipschitzBoundℂ p bound +
    (polynomialLipschitzBoundℂ p bound + bound · polynomialDerivativeVariationℂ p bound)

opaque
  polynomialDividedDifference-boundℂ : ∀ p bound w z →
    normℂ w ≤ℝ bound → normℂ z ≤ℝ bound →
    normℂ (evaluatePolynomialℂ (quotientPolynomialℂ p w) z) ≤ℝ polynomialLipschitzBoundℂ p bound
  polynomialDividedDifference-boundℂ [] bound w z wb zb =
    subst (_≤ℝ 0ℝ) (sym (cong normℂ (evaluatePolynomialℂ-empty z) ∙ normℂ-zero)) (≤ℝ-refl 0ℝ)
  polynomialDividedDifference-boundℂ (a ∷ p) bound w z wb zb =
    subst (_≤ℝ polynomialLipschitzBoundℂ (a ∷ p) bound)
      (sym (cong normℂ (quotient-cons a p w z)))
      (normℂ-addBound (evaluatePolynomialℂ p w) (z ·ℂ evaluatePolynomialℂ (quotientPolynomialℂ p w) z)
        (polynomialBoundℂ p bound) (bound · polynomialLipschitzBoundℂ p bound)
        (evaluatePolynomialℂ-bound p bound w wb)
        (normℂ-mulBound z (evaluatePolynomialℂ (quotientPolynomialℂ p w) z)
          bound (polynomialLipschitzBoundℂ p bound) zb
          (polynomialDividedDifference-boundℂ p bound w z wb zb)))

  polynomialDerivative-boundℂ : ∀ p bound r → normℂ r ≤ℝ bound →
    normℂ (polynomialDerivativeℂ p r) ≤ℝ polynomialLipschitzBoundℂ p bound
  polynomialDerivative-boundℂ p bound r rb =
    subst (_≤ℝ polynomialLipschitzBoundℂ p bound)
      (cong normℂ (polynomialDividedDifference-diagonalℂ p r))
      (polynomialDividedDifference-boundℂ p bound r r rb rb)

  polynomialLipschitzBound-nonnegativeℂ : ∀ p bound → 0ℝ ≤ℝ bound →
    0ℝ ≤ℝ polynomialLipschitzBoundℂ p bound
  polynomialLipschitzBound-nonnegativeℂ p bound nonnegative =
    ≤ℝ-trans 0ℝ (normℂ (evaluatePolynomialℂ (quotientPolynomialℂ p 0ℂ) 0ℂ))
      (polynomialLipschitzBoundℂ p bound)
      (normℂ-nonnegative (evaluatePolynomialℂ (quotientPolynomialℂ p 0ℂ) 0ℂ))
      (polynomialDividedDifference-boundℂ p bound 0ℂ 0ℂ zero-bound zero-bound)
    where
    zero-bound : normℂ 0ℂ ≤ℝ bound
    zero-bound = subst (_≤ℝ bound) (sym normℂ-zero) nonnegative

  polynomialDerivativeVariation-nonnegativeℂ : ∀ p bound → 0ℝ ≤ℝ bound →
    0ℝ ≤ℝ polynomialDerivativeVariationℂ p bound
  polynomialDerivativeVariation-nonnegativeℂ [] bound nonnegative = ≤ℝ-refl 0ℝ
  polynomialDerivativeVariation-nonnegativeℂ (a ∷ p) bound nonnegative =
    isNonnegative→0≤ (polynomialDerivativeVariationℂ (a ∷ p) bound)
      (addPresIsNonnegative lip (lip + bound · variation) lip-nonnegative
        (addPresIsNonnegative lip (bound · variation) lip-nonnegative
          (mulPresIsNonnegative bound variation (0≤→isNonnegative bound nonnegative)
            (0≤→isNonnegative variation (polynomialDerivativeVariation-nonnegativeℂ p bound nonnegative)))))
    where
    lip : ℝ
    lip = polynomialLipschitzBoundℂ p bound
    variation : ℝ
    variation = polynomialDerivativeVariationℂ p bound
    lip-nonnegative : IsNonnegative lip
    lip-nonnegative = 0≤→isNonnegative lip (polynomialLipschitzBound-nonnegativeℂ p bound nonnegative)

  -- Both arguments may move within radius of r. Unlike the Taylor
  -- estimate with just one moving endpoint, this controls contraction
  -- between any two points in the ball.
  polynomialDividedDifference-errorℂ : ∀ p bound radius r w z →
    normℂ r ≤ℝ bound → normℂ w ≤ℝ bound → normℂ z ≤ℝ bound →
    normℂ (w -ℂ r) ≤ℝ radius → normℂ (z -ℂ r) ≤ℝ radius →
    normℂ (evaluatePolynomialℂ (quotientPolynomialℂ p w) z -ℂ polynomialDerivativeℂ p r) ≤ℝ
      polynomialDerivativeVariationℂ p bound · radius
  polynomialDividedDifference-errorℂ [] bound radius r w z rb wb zb wr zr =
    subst2 _≤ℝ_ (sym (cong normℂ (error-empty r w z) ∙ normℂ-zero))
      (sym (RR.0LeftAnnihilates radius)) (≤ℝ-refl 0ℝ)
  polynomialDividedDifference-errorℂ (a ∷ p) bound radius r w z rb wb zb wr zr =
    subst2 _≤ℝ_ (sym (cong normℂ (error-step a p r w z)))
      (R.boundStep lip bound variation radius)
      (normℂ-addBound (evaluatePolynomialℂ p w -ℂ evaluatePolynomialℂ p r)
        ((z -ℂ r) ·ℂ divided +ℂ r ·ℂ (divided -ℂ polynomialDerivativeℂ p r))
        (lip · radius) (radius · lip + bound · (variation · radius))
        evaluation-error
        (normℂ-addBound ((z -ℂ r) ·ℂ divided) (r ·ℂ (divided -ℂ polynomialDerivativeℂ p r))
          (radius · lip) (bound · (variation · radius))
          (normℂ-mulBound (z -ℂ r) divided radius lip zr
            (polynomialDividedDifference-boundℂ p bound w z wb zb))
          (normℂ-mulBound r (divided -ℂ polynomialDerivativeℂ p r)
            bound (variation · radius) rb
            (polynomialDividedDifference-errorℂ p bound radius r w z rb wb zb wr zr))))
    where
    lip : ℝ
    lip = polynomialLipschitzBoundℂ p bound
    variation : ℝ
    variation = polynomialDerivativeVariationℂ p bound
    divided : ℂ
    divided = evaluatePolynomialℂ (quotientPolynomialℂ p w) z

    lip-nonnegative : 0ℝ ≤ℝ lip
    lip-nonnegative = ≤ℝ-trans 0ℝ (normℂ divided) lip (normℂ-nonnegative divided)
      (polynomialDividedDifference-boundℂ p bound w z wb zb)

    evaluation-error : normℂ (evaluatePolynomialℂ p w -ℂ evaluatePolynomialℂ p r) ≤ℝ lip · radius
    evaluation-error = ≤ℝ-trans (normℂ (evaluatePolynomialℂ p w -ℂ evaluatePolynomialℂ p r))
      (lip · normℂ (w -ℂ r)) (lip · radius)
      (evaluatePolynomialℂ-lipschitz p bound w r wb rb)
      (mulPres≤L (normℂ (w -ℂ r)) radius lip (0≤→isNonnegative lip lip-nonnegative) wr)

  polynomialNewtonRemainder-boundℂ : ∀ p bound radius r z w →
    normℂ r ≤ℝ bound → normℂ z ≤ℝ bound → normℂ w ≤ℝ bound →
    normℂ (z -ℂ r) ≤ℝ radius → normℂ (w -ℂ r) ≤ℝ radius →
    normℂ ((evaluatePolynomialℂ p z -ℂ evaluatePolynomialℂ p w) -ℂ
      polynomialDerivativeℂ p r ·ℂ (z -ℂ w)) ≤ℝ
      (polynomialDerivativeVariationℂ p bound · radius) · normℂ (z -ℂ w)
  polynomialNewtonRemainder-boundℂ p bound radius r z w rb zb wb zr wr =
    subst2 _≤ℝ_ (sym (cong normℂ (remainder-factor p r z w)))
      (mulComm (normℂ (z -ℂ w)) (polynomialDerivativeVariationℂ p bound · radius))
      (normℂ-mulBound (z -ℂ w)
        (evaluatePolynomialℂ (quotientPolynomialℂ p w) z -ℂ polynomialDerivativeℂ p r)
        (normℂ (z -ℂ w)) (polynomialDerivativeVariationℂ p bound · radius) (≤ℝ-refl (normℂ (z -ℂ w)))
        (polynomialDividedDifference-errorℂ p bound radius r w z rb wb zb wr zr))
