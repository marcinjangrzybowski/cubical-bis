module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Inverse where

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
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Inverse.Algebra as Algebra

open import Cubical.Analysis.Complex.Calculus.Derivative.Inverse.Estimates

private
  module E = Algebra.InverseRemainder ℂCommRing

-- Uniform inverse differentiation on an arbitrary parameter space. The
-- forward derivative is measured relative to the inverse coordinate.
-- A local Lipschitz bound for that coordinate is derived by absorption;
-- it is not an extra hypothesis, and no nonzero increment is divided out.
opaque
  uniformInverseComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate inverseCoordinate forwardDerivative inverseDerivative : A → ℂ) (C : ℚ₊) →
    (∀ x → inverseDerivative x ·ℂ forwardDerivative x ≡ 1ℂ) →
    (∀ x → normℂ (inverseDerivative x) ≤ℝ rat (fst C)) →
    IsRadiuswiseUniformComplexDerivativeAlong source inverseCoordinate coordinate forwardDerivative →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate inverseCoordinate inverseDerivative
  uniformInverseComplexDerivativeAlong source coordinate inverseCoordinate forwardDerivative inverseDerivative C law bounded forward ε = do
    (ρ , coarse) ← forward ((1₊ /2₊) ₊／₊ C)
    (δ , fine) ← forward ((ε ₊／₊ C) ₊／₊ (C +₊ C))
    return (min₊ ρ δ , λ x y close →
      subst (λ e → normℂ e ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
        (sym (E.inverseError (inverseDerivative x) (forwardDerivative x) (law x)
          (coordinate x) (coordinate y) (inverseCoordinate x) (inverseCoordinate y)))
        (boundedComplexErrorProduct (-ℂ inverseDerivative x)
          (complexDerivativeErrorAlong inverseCoordinate coordinate (forwardDerivative x) x y)
          (normℂ (coordinate y -ℂ coordinate x)) C ε
          (subst (_≤ℝ rat (fst C)) (sym (normℂ-neg (inverseDerivative x))) (bounded x))
          (complexErrorThroughLinearInput (complexDerivativeErrorAlong inverseCoordinate coordinate (forwardDerivative x) x y)
            (normℂ (inverseCoordinate y -ℂ inverseCoordinate x)) (normℂ (coordinate y -ℂ coordinate x)) (C +₊ C) (ε ₊／₊ C)
            (fine x y (PremetricStr.isMonotone≈≤ source x y (min₊ ρ δ) δ (min₊≤R ρ δ) close))
            (inverseChordBound (inverseDerivative x) (forwardDerivative x) (law x)
              (coordinate x) (coordinate y) (inverseCoordinate x) (inverseCoordinate y) C (bounded x)
              (coarse x y (PremetricStr.isMonotone≈≤ source x y (min₊ ρ δ) ρ (min₊≤L ρ δ) close))))))
