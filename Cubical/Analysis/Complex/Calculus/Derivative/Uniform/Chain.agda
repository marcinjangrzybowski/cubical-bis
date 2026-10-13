module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Chain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
import Cubical.Analysis.Complex.Calculus.Derivative.Identities as Identities

private module E = Identities.RemainderAlgebra ℂCommRing

-- Both remainders are measured on the same parameter space. Pullback of
-- the outer derivative can be supplied by uniform continuity of a path.
-- Explicit uniform bounds replace the point-dependent choices used in the
-- ordinary chain rule; every error radius remains independently truncated.
opaque
  chainHasUniformComplexDerivativeAlongIndexedBounded : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate inner inner' outer outer' : A → ℂ) (B C : ℚ₊) →
    (∀ x y → normℂ (inner y -ℂ inner x) ≤ℝ rat (fst B) · normℂ (coordinate y -ℂ coordinate x)) →
    (∀ x → normℂ (outer' x) ≤ℝ rat (fst C)) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate inner inner' →
    IsRadiuswiseUniformComplexDerivativeAlong source inner outer outer' →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate outer (λ x → outer' x ·ℂ inner' x)
  chainHasUniformComplexDerivativeAlongIndexedBounded source coordinate inner inner' outer outer' B C
    inputBound derivativeBound first second ε = do
    (δi , innerNear) ← first ((ε /2₊) ₊／₊ C)
    (δo , outerNear) ← second ((ε /2₊) ₊／₊ B)
    return (min₊ δi δo , λ x y close →
      subst2 _≤ℝ_
        (sym (cong normℂ (E.chain-error (inner x) (inner y) (outer x) (outer y) (inner' x) (outer' x)
          (coordinate y -ℂ coordinate x))))
        (halfErrorSum ε (normℂ (coordinate y -ℂ coordinate x)))
        (normℂ-addBound
          (complexDerivativeErrorAlong inner outer (outer' x) x y)
          (outer' x ·ℂ complexDerivativeErrorAlong coordinate inner (inner' x) x y)
          (rat (fst (ε /2₊)) · normℂ (coordinate y -ℂ coordinate x))
          (rat (fst (ε /2₊)) · normℂ (coordinate y -ℂ coordinate x))
          (complexErrorThroughLinearInput (complexDerivativeErrorAlong inner outer (outer' x) x y)
            (normℂ (inner y -ℂ inner x)) (normℂ (coordinate y -ℂ coordinate x)) B (ε /2₊)
            (outerNear x y (PremetricStr.isMonotone≈≤ source x y (min₊ δi δo) δo (min₊≤R δi δo) close))
            (inputBound x y))
          (boundedComplexErrorProduct (outer' x) (complexDerivativeErrorAlong coordinate inner (inner' x) x y)
            (normℂ (coordinate y -ℂ coordinate x)) C (ε /2₊) (derivativeBound x)
            (innerNear x y (PremetricStr.isMonotone≈≤ source x y (min₊ δi δo) δi (min₊≤L δi δo) close)))))
