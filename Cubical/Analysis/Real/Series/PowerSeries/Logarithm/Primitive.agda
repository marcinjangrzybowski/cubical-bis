module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Primitive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Rationals.Base as ℚ using (fromNat)
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Compatibility
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative


successorPositiveRational : ℕ → ℚ₊
successorPositiveRational n = fromNat (suc n) , ℚ.0<sucN n


-- Integration of coefficients uses exact positive rational division, so it
-- needs neither an order decision on reals nor an analytic choice principle.
formalPrimitive : ℝ → RealSequence → RealSequence
formalPrimitive constant coefficients zero = constant
formalPrimitive constant coefficients (suc n) =
  fst (successorPositiveRational n ℚInv.⁻¹₊) ⋆ coefficients n


opaque
  formalDerivative-formalPrimitive : ∀ constant coefficients →
    formalDerivative (formalPrimitive constant coefficients) ≡ coefficients
  formalDerivative-formalPrimitive constant coefficients = funExt λ n →
    cong (realNatural (suc n) ·_)
      (scalar-as-mul (fst (successorPositiveRational n ℚInv.⁻¹₊))
        (coefficients n))
    ∙ mulAssoc (realNatural (suc n))
        (rat (fst (successorPositiveRational n ℚInv.⁻¹₊)))
        (coefficients n)
    ∙ cong (_· coefficients n)
        (mul-rat (fromNat (suc n))
          (fst (successorPositiveRational n ℚInv.⁻¹₊))
        ∙ cong rat (ℚInv.x·invℚ₊[x] (successorPositiveRational n)))
    ∙ mulIdL (coefficients n)

-- Conversely, the constant term and derivative recover every coefficient.
-- Only the inverse of an explicitly positive rational successor is used.
opaque
  formalPrimitive-formalDerivative : ∀ coefficients →
    formalPrimitive (coefficients zero) (formalDerivative coefficients) ≡ coefficients
  formalPrimitive-formalDerivative coefficients = funExt recover
    where
    recover : ∀ n → formalPrimitive (coefficients zero) (formalDerivative coefficients) n ≡ coefficients n
    recover zero = refl
    recover (suc n) =
      scalar-as-mul (fst (successorPositiveRational n ℚInv.⁻¹₊))
        (realNatural (suc n) · coefficients (suc n))
      ∙ mulAssoc (rat (fst (successorPositiveRational n ℚInv.⁻¹₊)))
          (realNatural (suc n)) (coefficients (suc n))
      ∙ cong (_· coefficients (suc n))
          (mul-rat (fst (successorPositiveRational n ℚInv.⁻¹₊)) (fromNat (suc n))
          ∙ cong rat (ℚInv.invℚ₊[x]·x (successorPositiveRational n)))
      ∙ mulIdL (coefficients (suc n))
