module Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Neg where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings using (IsNonExpanding)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


negHasRiemannIntegral : ∀ {a b} (f : ℝ → ℝ) value →
  HasRiemannIntegralOn f a b value →
  HasRiemannIntegralOn (λ x → - f x) a b (- value)
negHasRiemannIntegral f value hasValue ε =
  PT.map
    (λ { (δ , closeToValue) →
      δ , λ tagged fine →
        closeness→absDifference<
          (riemannSum tagged (λ x → - f x)) (- value) ε
          (subst (_∼[ ε ] (- value))
            (sym (riemannSum-neg tagged f))
            (IsNonExpanding.pres≈ neg-isNonExpanding
              (riemannSum tagged f) value ε
              (absDifference<→closeness
                (riemannSum tagged f) value ε
                (closeToValue tagged fine)))) })
    (hasValue ε)


negIsRiemannIntegrable : ∀ {a b} (f : ℝ → ℝ) →
  IsRiemannIntegrableOn f a b →
  IsRiemannIntegrableOn (λ x → - f x) a b
negIsRiemannIntegrable f (value , hasValue) =
  - value , negHasRiemannIntegral f value hasValue


integral-neg : ∀ {a b} (f : ℝ → ℝ)
  (f-integrable : IsRiemannIntegrableOn f a b) →
  integral
    {f = λ x → - f x} {a = a} {b = b}
    (negIsRiemannIntegrable f f-integrable) ≡
  - integral {f = f} {a = a} {b = b} f-integrable
integral-neg f (value , hasValue) = refl
