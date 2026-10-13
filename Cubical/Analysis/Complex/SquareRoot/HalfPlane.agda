module Cubical.Analysis.Complex.SquareRoot.HalfPlane where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using ([_/_]; eq/)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.MultiplicativeApartness
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.SquareRoot.Positive
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.NormSquared
import Cubical.Analysis.Complex.SquareRoot.Algebra as AlgebraDefinition

private
  module R = AlgebraDefinition.SquareRootAlgebra ℝCommRing
  module C = AlgebraDefinition.SquareRootAlgebra ℂCommRing

  half : ℝ
  half = rat [ pos 1 / 1+ 1 ]

  half-positive : 0ℝ <ℝ half
  half-positive = <ℚ→<ℝ 0 [ pos 1 / 1+ 1 ] (ℚ.pos<pos tt)

  twice-half : half + half ≡ 1ℝ
  twice-half = rat+rat [ pos 1 / 1+ 1 ] [ pos 1 / 1+ 1 ] ∙ cong rat (eq/ _ _ refl)

module _ (z : ℂ) (positive-real : 0ℝ <ℝ re z) where
  private
    opaque
      norm-positive : 0ℝ <ℝ normSq z
      norm-positive = <≤ℝ-trans 0ℝ (re z · re z) (normSq z)
        (mulPositive (re z) (re z) positive-real positive-real)
        (subst (_≤ℝ normSq z) (addIdR (re z · re z))
          (addPres≤L 0ℝ (im z · im z) (re z · re z)
            (isNonnegative→0≤ (im z · im z) (squareIsNonnegative (im z)))))

    radius : ℝ
    radius = positiveSqrtℝ (normSq z) norm-positive

    radius-positive : 0ℝ <ℝ radius
    radius-positive = positiveSqrtℝ-positive (normSq z) norm-positive

    argument : ℝ
    argument = (radius + re z) · half

    opaque
      argument-positive : 0ℝ <ℝ argument
      argument-positive = mulPositive (radius + re z) half
        (subst (_<ℝ radius + re z) (addIdL 0ℝ)
          (<ℝ-add 0ℝ radius 0ℝ (re z) radius-positive positive-real)) half-positive

    u : ℝ
    u = positiveSqrtℝ argument argument-positive

    reciprocal : ℝ
    reciprocal = positiveReciprocal u (positiveSqrtℝ-positive argument argument-positive)

  opaque
    rightHalfPlaneSqrt : ℂ
    rightHalfPlaneSqrt = u , (half · im z) · reciprocal

    rightHalfPlaneSqrt-square : rightHalfPlaneSqrt ·ℂ rightHalfPlaneSqrt ≡ z
    rightHalfPlaneSqrt-square = ℂ≡
      (R.sqrtRealPart (re z) (im z) radius half u reciprocal twice-half
        (positiveSqrtℝ-square (normSq z) norm-positive)
        (positiveSqrtℝ-square argument argument-positive)
        (positiveReciprocalLaw u (positiveSqrtℝ-positive argument argument-positive)))
      (R.sqrtImaginaryPart (im z) half u reciprocal twice-half
        (positiveReciprocalLaw u (positiveSqrtℝ-positive argument argument-positive)))

opaque
  leftHalfPlaneSqrt : (z : ℂ) → re z <ℝ 0ℝ → ℂ
  leftHalfPlaneSqrt z negative-real = iℂ ·ℂ rightHalfPlaneSqrt (-ℂ z)
    (negativeNegationPositive {x = re z} negative-real)

  leftHalfPlaneSqrt-square : ∀ z negative-real →
    leftHalfPlaneSqrt z negative-real ·ℂ leftHalfPlaneSqrt z negative-real ≡ z
  leftHalfPlaneSqrt-square z negative-real = C.productSquare iℂ root
    ∙ cong₂ _·ℂ_ i²≡-1 (rightHalfPlaneSqrt-square (-ℂ z) positive)
    ∙ ℂRing.-DistL· 1ℂ (-ℂ z)
    ∙ cong (-ℂ_) (·ℂComm 1ℂ (-ℂ z) ∙ ·ℂIdR (-ℂ z))
    ∙ ℂRing.-Idempotent z
    where
    positive : 0ℝ <ℝ re (-ℂ z)
    positive = negativeNegationPositive {x = re z} negative-real
    root : ℂ
    root = rightHalfPlaneSqrt (-ℂ z) positive
