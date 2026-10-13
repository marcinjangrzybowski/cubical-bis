module Cubical.Analysis.Complex.FundamentalTheorem.Separable.Parameters where

-- Uniform constants obtained from one formal Bézout certificate. They
-- depend on finitely many coefficients, not on a selected approximate root.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_; addInvR)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order using (positiveReciprocalPositive)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Inverse.Bounds
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Bounds
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Coercivity
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Estimates
open import Cubical.Analysis.Complex.Polynomial.Newton.Remainder
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic using (BezoutSeparability)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.LocalRoots using (NewtonErrorBound)
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Bounds
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Constants using () renaming
  (descentHalf to half; descentHalf-positive to half-positive; descentHalf-double to half-double)

-- Only the already checked numeric half is reused from descent.
one-positive : 0ℝ <ℝ 1ℝ
one-positive = <ℚ→<ℝ 0 1 (ℚ.pos<pos tt)

sum-nonnegative : ∀ x y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y → 0ℝ ≤ℝ x + y
sum-nonnegative x y xn yn = isNonnegative→0≤ (x + y)
  (addPresIsNonnegative x y (0≤→isNonnegative x xn) (0≤→isNonnegative y yn))

product-nonnegative : ∀ x y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y → 0ℝ ≤ℝ x · y
product-nonnegative x y xn yn = isNonnegative→0≤ (x · y)
  (mulPresIsNonnegative x y (0≤→isNonnegative x xn) (0≤→isNonnegative y yn))

private
  one-nonnegative : 0ℝ ≤ℝ 1ℝ
  one-nonnegative = <ℝ-weaken 0ℝ 1ℝ one-positive

  enlarge : ∀ x → x ≤ℝ x + 1ℝ
  enlarge x = subst (_≤ℝ x + 1ℝ) (addIdR x) (addPres≤L 0ℝ 1ℝ x one-nonnegative)

opaque
  half<one : half <ℝ 1ℝ
  half<one = subst2 _<ℝ_ (addIdR half) half-double
    (<ℝ-addL 0ℝ half half half-positive)

  one-minus-half : 1ℝ - half ≡ half
  one-minus-half = cong (_- half) (sym half-double)
    ∙ sym (addAssoc half half (- half)) ∙ cong (half +_) (addInvR half) ∙ addIdR half

module Parameters {n} (p : MonicPolynomial n) (certificate : BezoutSeparability p) where
  private
    s = BezoutSeparability.bezoutS certificate
    t = BezoutSeparability.bezoutT certificate

  opaque
    centerBound : ℝ
    centerBound = (monicCoerciveRadius p + 1ℝ) + (monicCoerciveRadius p + 1ℝ)

    centerBound-nonnegative : 0ℝ ≤ℝ centerBound
    centerBound-nonnegative = sum-nonnegative (monicCoerciveRadius p + 1ℝ) (monicCoerciveRadius p + 1ℝ)
      (sum-nonnegative (monicCoerciveRadius p) 1ℝ (monicCoerciveRadius-nonnegative p) one-nonnegative)
      (sum-nonnegative (monicCoerciveRadius p) 1ℝ (monicCoerciveRadius-nonnegative p) one-nonnegative)

    smallResidual-centerBound : ∀ z → modulusℂ (evaluateMonic p z) <ℝ 1ℝ → normℂ z ≤ℝ centerBound
    smallResidual-centerBound = smallResidual-normBound p

    residualMultiplier : ℝ
    residualMultiplier = polynomialBoundℂ s centerBound

    residualMultiplier-nonnegative : 0ℝ ≤ℝ residualMultiplier
    residualMultiplier-nonnegative = polynomialBound-nonnegativeℂ s centerBound centerBound-nonnegative

    derivativeMultiplier : ℝ
    derivativeMultiplier = polynomialBoundℂ t centerBound + 1ℝ

    derivativeMultiplier-positive : 0ℝ <ℝ derivativeMultiplier
    derivativeMultiplier-positive = subst (_<ℝ derivativeMultiplier) (addIdR 0ℝ)
      (≤<ℝ-add 0ℝ (polynomialBoundℂ t centerBound) 0ℝ 1ℝ
        (polynomialBound-nonnegativeℂ t centerBound centerBound-nonnegative) one-positive)

    derivativeLower : ℝ
    derivativeLower = half · positiveReciprocal derivativeMultiplier derivativeMultiplier-positive

    derivativeLower-positive : 0ℝ <ℝ derivativeLower
    derivativeLower-positive = mulPositive half
      (positiveReciprocal derivativeMultiplier derivativeMultiplier-positive) half-positive
      (positiveReciprocalPositive derivativeMultiplier derivativeMultiplier-positive)

    inverseBound : ℝ
    inverseBound = positiveReciprocal derivativeLower derivativeLower-positive +
      positiveReciprocal derivativeLower derivativeLower-positive

    inverseBound-nonnegative : 0ℝ ≤ℝ inverseBound
    inverseBound-nonnegative = sum-nonnegative
      (positiveReciprocal derivativeLower derivativeLower-positive)
      (positiveReciprocal derivativeLower derivativeLower-positive)
      (<ℝ-weaken 0ℝ (positiveReciprocal derivativeLower derivativeLower-positive)
        (positiveReciprocalPositive derivativeLower derivativeLower-positive))
      (<ℝ-weaken 0ℝ (positiveReciprocal derivativeLower derivativeLower-positive)
        (positiveReciprocalPositive derivativeLower derivativeLower-positive))

    derivativeInverse : ∀ z → normℂ z ≤ℝ centerBound →
      residualMultiplier · modulusℂ (evaluateMonic p z) ≤ℝ half →
      Σ[ inverse ∈ ℂ ] ((inverse ·ℂ derivativeMonic p z ≡ 1ℂ) × (normℂ inverse ≤ℝ inverseBound))
    derivativeInverse z bounded small = inverseℂ (derivativeMonic p z) nonzero ,
      inverseℂ-law' (derivativeMonic p z) nonzero ,
      inverseℂ-normBound (derivativeMonic p z) nonzero derivativeLower derivativeLower-positive lower-bound
      where
      lower-bound : derivativeLower ≤ℝ modulusℂ (derivativeMonic p z)
      lower-bound = bezoutSeparability-derivativeLowerBound p certificate z residualMultiplier derivativeMultiplier
        half half derivativeMultiplier-positive (evaluatePolynomialℂ-bound s centerBound z bounded)
        (≤ℝ-trans (normℂ (evaluatePolynomialℂ t z)) (polynomialBoundℂ t centerBound) derivativeMultiplier
          (evaluatePolynomialℂ-bound t centerBound z bounded) (enlarge (polynomialBoundℂ t centerBound)))
        small half-double
      nonzero : ComplexNonzero (derivativeMonic p z)
      nonzero = modulusPositive→nonzeroℂ (derivativeMonic p z)
        (<≤ℝ-trans 0ℝ derivativeLower (modulusℂ (derivativeMonic p z)) derivativeLower-positive lower-bound)

    variationBound : ℝ
    variationBound = polynomialDerivativeVariationℂ (monicCoefficients p) (centerBound + 1ℝ)

    variationBound-nonnegative : 0ℝ ≤ℝ variationBound
    variationBound-nonnegative = polynomialDerivativeVariation-nonnegativeℂ (monicCoefficients p) (centerBound + 1ℝ)
      (sum-nonnegative centerBound 1ℝ centerBound-nonnegative one-nonnegative)

    remainderBound : ∀ center radius → normℂ center ≤ℝ centerBound → radius ≤ℝ 1ℝ →
      NewtonErrorBound p center radius (variationBound · radius)
    remainderBound center radius bounded small z w zb wb =
      monicNewtonRemainder-bound p center (centerBound + 1ℝ) radius z w
        (≤ℝ-trans (normℂ center) centerBound (centerBound + 1ℝ) bounded (enlarge centerBound))
        (pointBound z zb) (pointBound w wb) zb wb
      where
      pointBound : ∀ u → normℂ (u -ℂ center) ≤ℝ radius → normℂ u ≤ℝ centerBound + 1ℝ
      pointBound u ub = ≤ℝ-trans (normℂ u) (centerBound + radius) (centerBound + 1ℝ)
        (normℂ-ballBound center centerBound radius u bounded ub) (addPres≤L radius 1ℝ centerBound small)
