module Cubical.Analysis.Complex.Calculus.Derivative.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (addComm)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (mulIdL; mulDistL)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (addReflects≤R)
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Inverse.Algebra as Algebra

open import Cubical.Analysis.Complex.Calculus.Derivative.Inverse.Estimates

private
  module E = Algebra.InverseRemainder ℂCommRing

-- Inverse differentiation at one parameter value. Only a single truncated
-- bound for the reciprocal derivative is used at each requested tolerance.
-- The inverse coordinate need not be injective and no increment is divided.
opaque
  inverseComplexDerivativeAlongAt : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate inverseCoordinate : A → ℂ) (forwardDerivative inverseDerivative : ℂ) (x : A) →
    inverseDerivative ·ℂ forwardDerivative ≡ 1ℂ →
    IsComplexDerivativeAlongAt source inverseCoordinate coordinate forwardDerivative x →
    IsComplexDerivativeAlongAt source coordinate inverseCoordinate inverseDerivative x
  inverseComplexDerivativeAlongAt source coordinate inverseCoordinate forwardDerivative inverseDerivative x law forward ε = do
    (C , bounded) ← complexNormRationalBound inverseDerivative
    (ρ , coarse) ← forward ((1₊ /2₊) ₊／₊ C)
    (δ , fine) ← forward ((ε ₊／₊ C) ₊／₊ (C +₊ C))
    return (min₊ ρ δ , λ y close →
      subst (λ e → normℂ e ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
        (sym (E.inverseError inverseDerivative forwardDerivative law
          (coordinate x) (coordinate y) (inverseCoordinate x) (inverseCoordinate y)))
        (boundedComplexErrorProduct (-ℂ inverseDerivative)
          (complexDerivativeErrorAlong inverseCoordinate coordinate forwardDerivative x y)
          (normℂ (coordinate y -ℂ coordinate x)) C ε
          (subst (_≤ℝ rat (fst C)) (sym (normℂ-neg inverseDerivative)) bounded)
          (complexErrorThroughLinearInput (complexDerivativeErrorAlong inverseCoordinate coordinate forwardDerivative x y)
            (normℂ (inverseCoordinate y -ℂ inverseCoordinate x)) (normℂ (coordinate y -ℂ coordinate x)) (C +₊ C) (ε ₊／₊ C)
            (fine y (PremetricStr.isMonotone≈≤ source x y (min₊ ρ δ) δ (min₊≤R ρ δ) close))
            (inverseChordBound inverseDerivative forwardDerivative law
              (coordinate x) (coordinate y) (inverseCoordinate x) (inverseCoordinate y) C bounded
              (coarse y (PremetricStr.isMonotone≈≤ source x y (min₊ ρ δ) ρ (min₊≤L ρ δ) close))))))

inverseComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  (coordinate inverseCoordinate forwardDerivative inverseDerivative : A → ℂ) →
  (∀ x → inverseDerivative x ·ℂ forwardDerivative x ≡ 1ℂ) →
  IsComplexDerivativeAlong source inverseCoordinate coordinate forwardDerivative →
  IsComplexDerivativeAlong source coordinate inverseCoordinate inverseDerivative
inverseComplexDerivativeAlong source coordinate inverseCoordinate forwardDerivative inverseDerivative law forward x =
  inverseComplexDerivativeAlongAt source coordinate inverseCoordinate (forwardDerivative x) (inverseDerivative x) x (law x) (forward x)
