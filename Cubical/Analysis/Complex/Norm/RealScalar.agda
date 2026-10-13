module Cubical.Analysis.Complex.Norm.RealScalar where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Norm

-- Although the l1 norm is only submultiplicative for complex products,
-- multiplication by a real scalar has an exact norm formula.
opaque
  normℂ-multiplyReal : ∀ z scalar → normℂ (z ·ℂ fromℝ scalar) ≡ normℂ z · absℝ scalar
  normℂ-multiplyReal z scalar = cong normℂ (complexMultiplyReal z scalar)
    ∙ cong₂ _+_ (absMul (re z) scalar) (absMul (im z) scalar)
    ∙ sym (mulDistL (absℝ (re z)) (absℝ (im z)) (absℝ scalar))
