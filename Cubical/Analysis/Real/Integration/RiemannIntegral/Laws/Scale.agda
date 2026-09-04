module Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Scale where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings using (IsContinuousAt)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


scaleHasRiemannIntegral : ∀ {a b} (c : ℝ) (f : ℝ → ℝ) value →
  HasRiemannIntegralOn f a b value →
  HasRiemannIntegralOn (λ x → c · f x) a b (c · value)
scaleHasRiemannIntegral c f value hasValue ε =
  PT.rec squash₁
    (λ where
      (η , scaleClose) →
        PT.map
          (λ where
            (δ , closeToValue) →
              δ , λ tagged fine →
                closeness→absDifference<
                  (riemannSum tagged (λ x → c · f x))
                  (c · value) ε
                  (subst (_∼[ ε ] c · value)
                    (sym (riemannSum-scale tagged c f))
                    (sym∼
                      (c · value) (c · riemannSum tagged f) ε
                      (scaleClose (riemannSum tagged f)
                        (sym∼
                          (riemannSum tagged f) value η
                          (absDifference<→closeness
                            (riemannSum tagged f) value η
                            (closeToValue tagged fine)))))))
          (hasValue η))
    (mul-isContinuous₂ c value .IsContinuousAt.pres≈ ε)


scaleIsRiemannIntegrable : ∀ {a b} (c : ℝ) (f : ℝ → ℝ) →
  IsRiemannIntegrableOn f a b →
  IsRiemannIntegrableOn (λ x → c · f x) a b
scaleIsRiemannIntegrable c f (value , hasValue) =
  c · value , scaleHasRiemannIntegral c f value hasValue


integral-scale : ∀ {a b} (c : ℝ) (f : ℝ → ℝ)
  (f-integrable : IsRiemannIntegrableOn f a b) →
  integral
    {f = λ x → c · f x} {a = a} {b = b}
    (scaleIsRiemannIntegrable c f f-integrable) ≡
  c · integral {f = f} {a = a} {b = b} f-integrable
integral-scale c f (value , hasValue) = refl
