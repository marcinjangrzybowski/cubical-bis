module Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Sub where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Add
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Neg


subIsRiemannIntegrable : ∀ {a b} (f g : ℝ → ℝ) →
  IsRiemannIntegrableOn f a b →
  IsRiemannIntegrableOn g a b →
  IsRiemannIntegrableOn (λ x → f x - g x) a b
subIsRiemannIntegrable f g f-integrable g-integrable =
  addIsRiemannIntegrable f (λ x → - g x)
    f-integrable (negIsRiemannIntegrable g g-integrable)


integral-sub : ∀ {a b} (f g : ℝ → ℝ)
  (f-integrable : IsRiemannIntegrableOn f a b)
  (g-integrable : IsRiemannIntegrableOn g a b) →
  integral
    {f = λ x → f x - g x} {a = a} {b = b}
    (subIsRiemannIntegrable f g f-integrable g-integrable) ≡
  integral {f = f} {a = a} {b = b} f-integrable -
  integral {f = g} {a = a} {b = b} g-integrable
integral-sub f g (value , hasValue) (value' , hasValue') = refl
