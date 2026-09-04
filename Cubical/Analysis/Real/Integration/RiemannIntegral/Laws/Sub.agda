module Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Sub where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Add
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Neg


subHasRiemannIntegral : ∀ {a b} (f g : ℝ → ℝ) value value' →
  HasRiemannIntegralOn f a b value →
  HasRiemannIntegralOn g a b value' →
  HasRiemannIntegralOn (λ x → f x - g x) a b (value - value')
subHasRiemannIntegral f g value value' hasValue hasValue' =
  addHasRiemannIntegral f (λ x → - g x) value (- value')
    hasValue (negHasRiemannIntegral g value' hasValue')


subIsRiemannIntegrable : ∀ {a b} (f g : ℝ → ℝ) →
  IsRiemannIntegrableOn f a b →
  IsRiemannIntegrableOn g a b →
  IsRiemannIntegrableOn (λ x → f x - g x) a b
subIsRiemannIntegrable f g (value , hasValue) (value' , hasValue') =
  value - value'
  , subHasRiemannIntegral f g value value' hasValue hasValue'


integral-sub : ∀ {a b} (f g : ℝ → ℝ)
  (f-integrable : IsRiemannIntegrableOn f a b)
  (g-integrable : IsRiemannIntegrableOn g a b) →
  integral
    {f = λ x → f x - g x} {a = a} {b = b}
    (subIsRiemannIntegrable f g f-integrable g-integrable) ≡
  integral {f = f} {a = a} {b = b} f-integrable -
  integral {f = g} {a = a} {b = b} g-integrable
integral-sub f g (value , hasValue) (value' , hasValue') = refl
