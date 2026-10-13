module Cubical.Analysis.Complex.Transcendental.Exponential.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Inverse.Bounds
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.Cis.Properties
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base

opaque
  modulusℂ-exp : ∀ z → modulusℂ (expℂ z) ≡ expℝ (re z)
  modulusℂ-exp z = cong modulusℂ (expℂ-polar z)
    ∙ modulusℂ-mul (fromℝ (expℝ (re z))) (cisℝ (im z))
    ∙ cong₂ _·_ (modulusℂ-fromℝ (expℝ (re z))
      ∙ absOfNonnegative (expℝ (re z)) (<ℝ-weaken 0ℝ (expℝ (re z)) (expℝ-positive (re z))))
      (modulusℂ-cisℝ (im z))
    ∙ mulIdR (expℝ (re z))

  expℂ-modulus-positive : ∀ z → 0ℝ <ℝ modulusℂ (expℂ z)
  expℂ-modulus-positive z = subst (0ℝ <ℝ_) (sym (modulusℂ-exp z)) (expℝ-positive (re z))

  -- This is positive apartness, which is sufficient for the native reciprocal.
  expℂ-nonzero : ∀ z → ComplexNonzero (expℂ z)
  expℂ-nonzero z = modulusPositive→nonzeroℂ (expℂ z) (expℂ-modulus-positive z)

  inverseℂ-exp : ∀ z (nonzero : ComplexNonzero (expℂ z)) →
    inverseℂ (expℂ z) nonzero ≡ expℂ (-ℂ z)
  inverseℂ-exp z nonzero = sym
    (inverseℂ-unique (expℂ z) nonzero (expℂ (-ℂ z)) (expℂ-neg-inverse z))

  expℂ-sub : ∀ z w → expℂ (z -ℂ w) ≡ expℂ z ·ℂ inverseℂ (expℂ w) (expℂ-nonzero w)
  expℂ-sub z w = expℂ-add z (-ℂ w)
    ∙ cong (expℂ z ·ℂ_) (sym (inverseℂ-exp w (expℂ-nonzero w)))

  expℂ-iPi : expℂ (iℂ ·ℂ fromℝ piℝ) ≡ -ℂ 1ℂ
  expℂ-iPi = expℂ-euler piℝ ∙ cisℝ-pi

  expℂ-imaginaryTwoPi : expℂ (0ℝ , twoPiℝ) ≡ 1ℂ
  expℂ-imaginaryTwoPi = expℂ-imaginary twoPiℝ
    ∙ cong cisℝ (sym (addIdL twoPiℝ)) ∙ cisℝ-periodic 0ℝ ∙ cisℝ-zero

  expℂ-periodic : ∀ z → expℂ (z +ℂ (0ℝ , twoPiℝ)) ≡ expℂ z
  expℂ-periodic z = expℂ-add z (0ℝ , twoPiℝ)
    ∙ cong (expℂ z ·ℂ_) expℂ-imaginaryTwoPi ∙ ·ℂIdR (expℂ z)
