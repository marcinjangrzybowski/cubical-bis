module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int.Fast.Base using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; fromNat)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Primitive


-- x + x²/2 + x³/3 + ⋯, the local series of -log(1-x).
negativeLogOneMinusCoefficients : RealSequence
negativeLogOneMinusCoefficients = formalPrimitive 0ℝ geometricCoefficients


negativeLogCoefficientBound : ℚ₊
negativeLogCoefficientBound = successorPositiveRational zero


opaque
  negativeLogOneMinusCoefficient-zero :
    negativeLogOneMinusCoefficients zero ≡ 0ℝ
  negativeLogOneMinusCoefficient-zero = refl

  negativeLogOneMinusCoefficient-suc : ∀ n →
    negativeLogOneMinusCoefficients (suc n) ≡
    rat (fst (successorPositiveRational n ℚInv.⁻¹₊))
  negativeLogOneMinusCoefficient-suc n =
    scalar-rat (fst (successorPositiveRational n ℚInv.⁻¹₊)) 1
    ∙ cong rat (ℚ.·IdR (fst (successorPositiveRational n ℚInv.⁻¹₊)))

  formalDerivative-negativeLogOneMinus :
    formalDerivative negativeLogOneMinusCoefficients ≡ geometricCoefficients
  formalDerivative-negativeLogOneMinus =
    formalDerivative-formalPrimitive 0ℝ geometricCoefficients


private
  successorInverseNonnegative : ∀ n →
    0ℝ ≤ℝ rat (fst (successorPositiveRational n ℚInv.⁻¹₊))
  successorInverseNonnegative n =
    invEq (rat≤rat≃ 0 (fst (successorPositiveRational n ℚInv.⁻¹₊)))
      (ℚ.<Weaken≤ 0 (fst (successorPositiveRational n ℚInv.⁻¹₊))
        (snd (successorPositiveRational n ℚInv.⁻¹₊)))

  successorInverse≤one : ∀ n →
    fst (successorPositiveRational n ℚInv.⁻¹₊) ℚ.≤ 1
  successorInverse≤one n =
    ℚInv.invℚ₊≤invℚ₊
      (successorPositiveRational n) negativeLogCoefficientBound
      (PositiveRationals.≤ℤ→≤ℚ (pos 1) (pos (suc n))
        (ℤ.ℕ≤→pos-≤-pos 1 (suc n)
          (ℕ.suc-≤-suc ℕ.zero-≤)))


opaque
  negativeLogOneMinusCoefficientsNonnegative :
    NonnegativeCoefficients negativeLogOneMinusCoefficients
  negativeLogOneMinusCoefficientsNonnegative zero = ≤ℝ-refl 0ℝ
  negativeLogOneMinusCoefficientsNonnegative (suc n) =
    subst (0ℝ ≤ℝ_) (sym (negativeLogOneMinusCoefficient-suc n))
      (successorInverseNonnegative n)

  negativeLogOneMinusCoefficientsBounded :
    CoefficientAbsBound negativeLogCoefficientBound
      negativeLogOneMinusCoefficients
  negativeLogOneMinusCoefficientsBounded zero =
    subst (_≤ℝ 1ℝ) (sym absZero) (realNatural-nonnegative 1)
  negativeLogOneMinusCoefficientsBounded (suc n) =
    subst (_≤ℝ 1ℝ)
      (sym (cong absℝ (negativeLogOneMinusCoefficient-suc n)
        ∙ absOfNonnegative
            (rat (fst (successorPositiveRational n ℚInv.⁻¹₊)))
            (successorInverseNonnegative n)))
      (invEq (rat≤rat≃ (fst (successorPositiveRational n ℚInv.⁻¹₊)) 1)
        (successorInverse≤one n))

  negativeLogOneMinusSelfMajorized :
    CoefficientMajorizedBy negativeLogOneMinusCoefficients
      negativeLogOneMinusCoefficients
  negativeLogOneMinusSelfMajorized =
    nonnegativeCoefficientsSelfMajorized negativeLogOneMinusCoefficients
      negativeLogOneMinusCoefficientsNonnegative
