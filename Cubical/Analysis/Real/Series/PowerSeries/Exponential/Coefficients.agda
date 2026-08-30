module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _!)
open import Cubical.Data.Rationals.Base as ℚ
  using (ℚ; fromNat)
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚInv

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _·₊_)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative


-- A positive rational presentation of n!.  Keeping positivity in ℚ makes
-- reciprocal cancellation exact before embedding into the reals.
exponentialPositiveNatural : ℕ → ℚ₊
exponentialPositiveNatural n =
  fromNat (suc n) , ℚ.0<sucN n


exponentialRationalFactorial : ℕ → ℚ₊
exponentialRationalFactorial zero = exponentialPositiveNatural zero
exponentialRationalFactorial (suc n) =
  exponentialPositiveNatural n ·₊ exponentialRationalFactorial n


exponentialRationalFactorial-value : ∀ n →
  fst (exponentialRationalFactorial n) ≡ fromNat (n !)
exponentialRationalFactorial-value zero = refl
exponentialRationalFactorial-value (suc n) =
  cong (fromNat (suc n) ℚ.·_)
    (exponentialRationalFactorial-value n)
  ∙ ℚ.ℕ·→ℚ· (suc n) (n !)


exponentialRationalCoefficient : ℕ → ℚ
exponentialRationalCoefficient n =
  fst (exponentialRationalFactorial n ℚInv.⁻¹₊)


exponentialRationalCoefficient-zero :
  exponentialRationalCoefficient zero ≡ 1
exponentialRationalCoefficient-zero =
  ℚInv.invℚ₊-fromNat zero


exponentialRationalCoefficient-suc : ∀ n →
  fromNat (suc n) ℚ.·
      exponentialRationalCoefficient (suc n)
    ≡
  exponentialRationalCoefficient n
exponentialRationalCoefficient-suc n =
  cong (fromNat (suc n) ℚ.·_)
    (cong fst
      (sym
        (ℚInv.invℚ₊Dist·
          (exponentialPositiveNatural n) (exponentialRationalFactorial n))))
  ∙ ℚInv.y·[x/y]
      (exponentialPositiveNatural n)
      (exponentialRationalCoefficient n)


-- The real coefficient sequence 1/n!, obtained only after all reciprocal
-- arithmetic has been performed exactly in ℚ.
exponentialCoefficients : RealSequence
exponentialCoefficients n =
  rat (exponentialRationalCoefficient n)


exponentialCoefficients-value : ∀ n →
  exponentialCoefficients n
    ≡ rat (fst (exponentialRationalFactorial n ℚInv.⁻¹₊))
exponentialCoefficients-value n = refl


exponentialCoefficients-zero :
  exponentialCoefficients zero ≡ 1ℝ
exponentialCoefficients-zero =
  cong rat exponentialRationalCoefficient-zero


exponentialCoefficients-suc : ∀ n →
  realNatural (suc n)
      · exponentialCoefficients (suc n)
    ≡
  exponentialCoefficients n
exponentialCoefficients-suc n =
  mul-rat
    (fromNat (suc n))
    (exponentialRationalCoefficient (suc n))
  ∙ cong rat (exponentialRationalCoefficient-suc n)


formalDerivative-exponentialCoefficients-pointwise : ∀ n →
  formalDerivative exponentialCoefficients n
    ≡ exponentialCoefficients n
formalDerivative-exponentialCoefficients-pointwise =
  exponentialCoefficients-suc


formalDerivative-exponentialCoefficients :
  formalDerivative exponentialCoefficients
    ≡ exponentialCoefficients
formalDerivative-exponentialCoefficients =
  funExt formalDerivative-exponentialCoefficients-pointwise


repeatedFormalDerivative-exponentialCoefficients : ∀ order →
  repeatedFormalDerivative order exponentialCoefficients
    ≡ exponentialCoefficients
repeatedFormalDerivative-exponentialCoefficients zero = refl
repeatedFormalDerivative-exponentialCoefficients (suc order) =
  cong formalDerivative
    (repeatedFormalDerivative-exponentialCoefficients order)
  ∙ formalDerivative-exponentialCoefficients
